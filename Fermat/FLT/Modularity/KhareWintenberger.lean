/-
Modularity/KhareWintenberger.lean — own work for the Fermat project (not
vendored from the FLT project).

# The Khare–Wintenberger cut behind residual modularity at `ℓ ≥ 5`

This module carries the founder decomposition of the residual-modularity
leaf `exists_weightTwoEigenform_residual_of_isIrreducible_of_five_le`
(`Modularity/Interface.lean`, pillar 2 at `ℓ ≥ 5` — the
Khare–Wintenberger content of the modularity subtree).

## RELOCATION 2026-07-27: the Moret–Bailly chain now lives in
`Modularity/MoretBailly.lean`

Everything from `PotentialModularityWitness` down to and including
`exists_moretBailly_seed_of_five_le` — the old lines 596–23408 of this file —
was MOVED VERBATIM to `Fermat/FLT/Modularity/MoretBailly.lean`, which this
module now imports. The reason is layering, not size: those declarations are
the five obligations of `HardlyRamified/HilbertModularity.lean`'s leaf
`nonempty_potentialHeckeDatum_of_five_le`, and this file is DOWNSTREAM of that
module, so the leaf could never consume them (BREAK D of its docstring). This
file keeps pillar α and everything from the modularity-lifting cut onwards.

## Route choice (AUDIT, 2026-07-24)

Two literature routes were audited for that leaf:

* the **Khare–Wintenberger induction** (*Serre's modularity conjecture
  (I), (II)*, Invent. Math. 178 (2009)): minimal lifting of the residual
  representation to a strictly compatible system, then induction on the
  residue characteristic with modularity switching at auxiliary primes;
* the **potential-modularity chain** of the FLT blueprint (ch. 4:
  Moret–Bailly, dihedral residual modularity from converse theorems,
  modularity lifting over totally real fields, base-change descent) —
  the route the reference Lean project (`~/cs/FLT`) chose.

For the HARDLY RAMIFIED type both routes converge onto the same terminal
shape. Any compatible system attached to a hardly ramified
representation has a `3`-adic member which is hardly ramified `3`-adic,
and this project PROVES (Fontaine/Odlyzko discriminant bounds,
`ModThree.lean`; ordinarity lifting, `Threeadic.lean`) that such a
member is a global extension of the trivial character by the cyclotomic
character — its Frobenius traces are `1 + q`. So the anchor-prime step
of either route does not produce a cusp form: it produces the Eisenstein
trace system, and transporting it back through the family forces the
residual representation to be REDUCIBLE (Chebotarev + Brauer–Nesbitt),
contradicting the leaf's irreducibility hypothesis. Both classical
routes, instantiated at this type, are therefore proofs by contradiction
— which is exactly the blueprint's plan (ch. 4, "Compatible families,
and reduction at 3") and exactly why `S₂(Γ₀(2)) = 0` makes Serre's
conjecture at type `(2, 2)` a nonexistence theorem. The sound cut is
hence the blueprint cut: prove the headline

  **no irreducible hardly ramified mod-`ℓ` representation exists for
  `ℓ ≥ 5`** (`not_isIrreducible_of_isHardlyRamified_of_five_le`)

and discharge the interface leaf by `absurd`. The alternative — a
non-vacuous eigenform-producing decomposition — would require
constructing analytic cusp forms (Langlands–Tunnell / converse-theorem
machinery) on a pin with no Hecke theory; that route is strictly deeper
at every node and was rejected.

## Relation to the existing tree (NO CYCLE, NO SILENT DUPLICATION)

The tree already contains this chain ONCE: `Reducible.lean`'s B5 is
proven from `Lift.lean`'s `exists_hardlyRamifiedLift` (B6a),
`residual_charFrob_eq` (B6bc) and `not_isIrreducible_of_charFrob_eq`
(Chebotarev–Brauer–Nesbitt). But B6bc routes through `Family.lean`'s
`mem_isCompatible`, whose proof consumes the modularity interface — the
very assemblies that consume the leaf this module discharges. Importing
`Lift.lean` here would therefore close the dependency cycle that the
interface's CIRCULARITY GUARD forbids. The three pillars below (α
PROVEN 2026-07-24 by the proof-sharing refactor; β and γ sorried)
are consequently FAMILY-FREE restatements, and their docstrings record,
pillar by pillar, which in-tree twin they mirror and which discharge
routes are sound:

* pillar α (`exists_hardlyRamified_lift_residual_of_five_le`) mirrors
  `Lift.lean`'s B6a and — since the 2026-07-24 proof-sharing refactor —
  IS PROVEN by delegation to the shared Family-free module
  `HardlyRamified/Deformation.lean` (the deformation development moved
  out of `Lift.lean` and generalized over the coefficient field `k`;
  both this pillar and B6a now consume the same
  `exists_hardlyRamified_lift_of_five_le`);
* pillar β (`exists_threeadic_compatible_member_of_five_le`) mirrors
  B6b + the 3-adic specialization, but its in-tree twin's proof
  (through `Family.lean`) is UNSOUND here — its only sound discharge is
  the potential-modularity construction. This pillar is where the
  genuine depth of the residual-modularity leaf now lives (2026-07-24:
  DISCHARGED as a proven assembly over the potential-modularity
  carrier `PotentialModularityWitness`; carrier inhabitation was in
  turn PROVEN 2026-07-24 as an assembly over the Moret–Bailly seed
  `MoretBaillySeed`, so the depth now lives in the sorried leaves —
  Moret–Bailly base production (Taylor 2002 Thm B), modularity
  lifting over the totally real base (Kisin/Taylor), the
  Hilbert-modular `3`-adic realization (Carayol 1986/Taylor 1989),
  the ℓ-adic Brauer descent of the Hecke eigensystem to `ℚ`, and the
  hardly ramified `3`-adic member via BLGGT §5, the last itself
  DECOMPOSED 2026-07-24 into the raw `3`-adic realization
  (`ThreeadicRealization`, `exists_threeadicRealization_of_witness`)
  plus four per-condition transfer leaves — see their docstrings);
* pillar γ (`not_isIrreducible_of_charFrob_eisenstein`) is the
  finite-coefficient-field transfer of the PROVEN
  `not_isIrreducible_of_charFrob_eq`, whose proof consumes only
  Family-free material from `Chebotarev.lean` — a mechanical
  generalization, no new mathematics. PROVEN 2026-07-24: `char k = ℓ`
  (`charP_of_algebra_padicInt`), the twin's density argument with the
  comparison functions pushed into `k` through `ZMod.castHom`, and the
  field-generic Kolchin/Brauer–Nesbitt helper
  `not_isIrreducible_of_charpoly_eq_units`.

The assembly `not_isIrreducible_of_isHardlyRamified_of_five_le` is
PROVEN below from the three pillars plus the PROVEN 3-adic machinery
(`IsHardlyRamified.exists_frobenius_triangular`, `Threeadic.lean` — the
trace form of the same classification is B6c,
`IsHardlyRamified.three_adic`).

(Import note, 2026-07-24: `Chebotarev.lean` — the home of pillar γ's
proof ingredients — is deliberately NOT imported: the assembly does not
need it, thanks to the triangular-Frobenius route through
`Threeadic.lean`; the agent proving pillar γ adds the import then —
done 2026-07-24, as proof-only (non-public) imports.)
-/
module

public import Fermat.FLT.GaloisRepresentation.HardlyRamified.Defs
-- The VENDORED quaternionic automorphic-forms development (weight-2 forms on a
-- totally definite quaternion algebra over a totally real field, with their
-- Hecke algebras).  It is imported HERE, and only here, because
-- the `carayol_threeadic_realization_of_heckePackage` node below is its FIRST
-- and currently ONLY consumer inside the cone of `fermat_last_theorem`; before
-- this import the whole 109-module subtree was free-floating.  Since 2026-07-27
-- the names actually mentioning the vendored API are that node's two hoisted
-- steps, `exists_totallyDefinite_heckeCharacter_of_heckePackage` and
-- `carayol_threeadic_of_totallyDefinite_heckeCharacter`, together with the two
-- leaves the FIRST of those was later split into,
-- `exists_totallyDefinite_rigidified_quaternionAlgebra_of_even` (ABHN) and
-- `exists_heckeCharacter_of_totallyDefinite_quaternionAlgebra` (Jacquet–Langlands
-- proper).  See the node's
-- "JACQUET–LANGLANDS CONSUMER" docstring block for what is consumed and why the
-- parity hypothesis `hFeven` is what makes the consumption sound.
public import Fermat.FLT.AutomorphicForm.QuaternionAlgebra.HeckeOperators.Concrete
public import Mathlib.NumberTheory.NumberField.Basic
-- `Ideal.absNorm`: the absolute norm `Nw` is the constant coefficient of
-- the parallel-weight-`2` Hecke polynomials in the STATEMENTS of the two
-- joints of the automorphic cut, so this import must be public
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm
public import Mathlib.RingTheory.Ideal.GoingUp
public import Mathlib.RingTheory.Ideal.Height
public import Mathlib.RingTheory.NoetherNormalization
-- public: `MvPolynomial.schwartz_zippel_totalDegree`, the zero-count bound for a
-- nonzero multivariate polynomial over a finite field. It is the counting half of
-- item 4's Bertini step (`exists_bertiniGoodPlaneCount`), used in the statement-facing
-- form `schwartzZippel_card_zeros_mul_le` below.
public import Mathlib.Algebra.MvPolynomial.SchwartzZippel
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
-- proof-only: `RingHom.injective` (a ring hom out of a field is
-- injective), the descent step of the automorphic joint's transport
import Mathlib.RingTheory.SimpleRing.Basic
-- public: `Field (ULift ℝ)` / `Field (ULift ℚ)`. The Moret–Bailly cut
-- states its local and global points over the `Type u` copies `ULift ℝ`
-- and `ULift ℚ`, and the affine reduction needs them to be FIELDS — that
-- is what makes `Spec` of them a one-point scheme, which is the whole
-- reason a field-valued point factors through an affine open.
public import Mathlib.Algebra.Field.ULift
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
-- the potential-modularity carrier's fields (totally real base field,
-- Galois enabling hypothesis for Brauer induction) live in these:
public import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
public import Mathlib.Algebra.QuaternionBasis
public import Mathlib.NumberTheory.NumberField.Cyclotomic.Ideal
public import Mathlib.FieldTheory.Finite.GaloisField
-- `CommGroup.exists_apply_ne_one_of_hasEnoughRootsOfUnity`, the finite-abelian
-- duality used to build the standard level module's alternating form; `public`
-- because it is consumed in proof bodies of this module's own declarations.
public import Mathlib.GroupTheory.FiniteAbelian.Duality
-- `AlgebraicClosure.map` and `Field.absoluteGaloisGroup.lift_map`, the chosen
-- embedding of algebraic closures used by `galRoot_eq_pow_cycCharModN`.
public import Fermat.FLT.Deformations.Lemmas
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.FieldTheory.Galois.Basic
-- the Moret–Bailly cut (2026-07-25, PIN RE-AUDIT): the scheme-theoretic
-- vocabulary in which Moret–Bailly's existence theorem and the twisted
-- Hilbert–Blumenthal moduli input are STATED below — `Scheme`, `Spec`,
-- `Smooth`, `IsSeparated`, `LocallyOfFiniteType`, `QuasiCompact` and
-- `GeometricallyIrreducible` all exist at this pin (contrary to the
-- 2026-07-24 audit note, which is corrected in the section docstring),
-- so these are `public import`s: the names occur in leaf statements.
public import Mathlib.AlgebraicGeometry.Geometrically.Irreducible
-- `GeometricallyConnected` (2026-07-26): the Bertini genericity leaf is cut
-- into "generic section is smooth" + "generic section is geometrically
-- CONNECTED" + the formal upgrade connected ⟹ irreducible for a smooth
-- scheme, so the class occurs in a leaf statement and must be re-exported.
public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
-- Moret–Bailly §3.1's compactification datum is stated with `IsProper`, and
-- the `dim ≤ 0` branch of `exists_totallySplitPoint_of_affine_curve` runs
-- through `IsLocallyArtinian.of_topologicalKrullDim_le_zero`.
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Artinian
-- The connected ⟹ irreducible upgrade of the Bertini cut (2026-07-26) states
-- `IsLocallyNoetherian` in the signature of
-- `exists_isOpen_isIrreducible_of_isDomain_stalk`, and its topological half
-- `irreducibleSpace_of_connectedSpace_of_locallyIrreducible` is proven with
-- `IsClopen.eq_univ`; both must therefore be re-exported, not merely reachable.
public import Mathlib.AlgebraicGeometry.Noetherian
-- Residue fields of scheme points: `Scheme.residueField`,
-- `Scheme.fromSpecResidueField`. Moret-Bailly's point entier is read off through
-- its residue field (his Remarque 1.5), so `hasRationalPoint_residueField` and the
-- §3 core leaf both need this.
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.Topology.Connected.Clopen
-- Base change of schemes: `IsFormOver` (the twisted-moduli form cut,
-- 2026-07-25) is stated with `Limits.pullback`, so the `HasPullbacks`
-- instance for `Scheme` must be re-exported, not merely available.
public import Mathlib.AlgebraicGeometry.Pullbacks
-- Descent of geometric irreducibility along a form
-- (`geometricallyIrreducible_of_isFormOver_isAlgClosed`, PROVEN
-- 2026-07-26) needs, in its PROOF BODY: the base-change stability of
-- `AlgebraicGeometry.Surjective` (`PullbackCarrier`), the nontriviality
-- of `L ⊗[ℚ] K` (`Flat.Basic`, `TensorProduct.Basic`) and the existence
-- of a maximal ideal together with `Ideal.Quotient.field` (`Ideal.Maximal`).
-- `public` because an intermediate module importing them privately makes
-- them unavailable even in proof bodies.
public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.RingTheory.TensorProduct.Quotient
public import Mathlib.RingTheory.TensorProduct.MvPolynomial
public import Mathlib.RingTheory.RingHom.Smooth
public import Mathlib.RingTheory.Smooth.Basic
public import Mathlib.RingTheory.Smooth.Locus
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.Etale.Field
public import Mathlib.RingTheory.Unramified.Field
public import Mathlib.RingTheory.Jacobson.Ring
public import Mathlib.RingTheory.Artinian.Ring
public import Mathlib.FieldTheory.Perfect
public import Mathlib.RingTheory.Ideal.Maximal
-- Bertini cut (2026-07-26): `exists_dimensionDrop_of_affine_geometricallyIrreducible`
-- is PROVEN over `exists_bertiniHyperplane_of_affine_geometricallyIrreducible`, and
-- the reduction needs the affine dictionary (`IsAffineHom`, `Scheme.isoSpec`,
-- `Scheme.ΓSpecIso`) together with the Krull-dimension bookkeeping that turns
-- "quotient by a nonzerodivisor" into a STRICT dimension drop
-- (`ringKrullDim_quotient_succ_le_of_nonZeroDivisor`, plus finite-dimensionality
-- of a finitely generated algebra over a field via
-- `MvPolynomial.ringKrullDim_of_isNoetherianRing`). `nonZeroDivisors`,
-- `Ideal.span` and `ringKrullDim` occur in the new leaf's STATEMENT, so these
-- are `public import`s.
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.RingTheory.KrullDimension.NonZeroDivisors
public import Mathlib.RingTheory.KrullDimension.Polynomial
public import Mathlib.RingTheory.KrullDimension.Field
-- `isDomain_of_isRegularLocalRing` (PROVEN 2026-07-26, the commutative-algebra
-- half of `isDomain_stalk_of_smooth_over_field`).  `IsRegularLocalRing` occurs
-- in the SIGNATURE of `isRegularLocalRing_stalk_of_smooth_over_field`, so its
-- defining module must be a `public import` and not a bare one.
public import Mathlib.RingTheory.RegularLocalRing.Defs
-- `exists_isRegularLocalRing_quotient_indepList_of_smooth_over_field` (PROVEN
-- 2026-07-26) presents the stalk of a smooth `K`-scheme as a localized
-- polynomial ring modulo the relations of a standard-smooth presentation.  It
-- needs: the regularity of `MvPolynomial ι K` localized at a prime
-- (`RegularLocalRing.Polynomial`), the `SubmersivePresentation` /
-- `IsStandardSmooth` package and its `RespectsIso` transfer along
-- `Γ(Spec K, ⊤) ≅ K` (`Smooth.StandardSmooth`, `RingHom.StandardSmooth`), the
-- residue field `κ(q)` of a prime (`LocalRing.ResidueField.Ideal`), partial
-- derivatives on `MvPolynomial` (`MvPolynomial.PDeriv`), the determinant
-- criterion for linear independence of the columns of the Jacobian
-- (`Matrix.NonsingularInverse`), and `IsLocalization.of_surjective` together
-- with `mem_map_algebraMap_iff` (`Localization.Ideal`).
public import Mathlib.RingTheory.RegularLocalRing.Polynomial
public import Mathlib.RingTheory.Smooth.StandardSmooth
public import Mathlib.RingTheory.RingHom.StandardSmooth
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.RingTheory.Localization.Ideal
public import Mathlib.RingTheory.Nakayama
public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
public import Mathlib.RingTheory.LocalRing.RingHom.Basic
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.Spectrum.Prime.Topology
-- `exists_isOpen_isIrreducible_primeSpectrum` (PROVEN 2026-07-26, the affine
-- heart of the connected ⟹ irreducible upgrade) states `Localization.AtPrime`
-- in its signature, and its proof runs on the minimal-prime API: finiteness
-- over a noetherian ring, and the order isomorphism between the primes of
-- `A_p` and the primes of `A` below `p`.
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian
public import Mathlib.RingTheory.Ideal.MinimalPrime.Localization
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.Algebra.Algebra.Rat
-- The Bertini DECOMPOSITION (2026-07-26): the hyperplane parameter space is
-- `Fin (n+1) → ℚ` and Zariski-genericity on it is stated as "off the zero
-- locus of a nonzero `MvPolynomial (Fin (n+1)) ℚ`", so `MvPolynomial` occurs
-- in the three new leaf STATEMENTS; `MvPolynomial.funext_set` (vanishing on a
-- box with infinite sides forces the polynomial to be zero) is what proves
-- the density lemma reconciling the Zariski and real topologies, and
-- `Set.Ioo_infinite` supplies the infinite sides.
public import Mathlib.Algebra.MvPolynomial.Funext
-- NOETHER–OSTROWSKI (2026-07-27, `exists_inverted_irreducible_map_algClosureZMod`):
-- the Nullstellensatz over `ℚ ⊆ ℚ̄` (`MvPolynomial.vanishingIdeal_zeroLocus_eq_radical`)
-- turns "no `ℚ̄`-point" into "the ideal is `⊤`"; `IsLocalization.exist_integer_multiples`
-- clears the denominators of the resulting Bézout identity; and the unit/degree API for
-- `MvPolynomial` over a domain (`isUnit_iff_totalDegree_of_isReduced`,
-- `totalDegree_mul_of_isDomain`) is what makes "both factors nonconstant" a CLOSED
-- condition on the coefficient vectors.
public import Mathlib.RingTheory.Nullstellensatz
public import Mathlib.RingTheory.Localization.Integer
public import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
public import Mathlib.Algebra.MvPolynomial.Nilpotent
public import Mathlib.Algebra.Field.ZMod
-- ARCHIMEDEAN cut (2026-07-26, `exists_realHilbertBlumenthalObject_of_odd`):
-- the two conjugacy classes of complex conjugation on `H₁(E(ℂ), ℤ) = ℤ²` are
-- written as explicit `2 × 2` matrices (`realConjMatrix`), so the matrix
-- notation `!![a, b; c, d]`, `Matrix.toLin'` and `Matrix.det_fin_two_of` occur
-- in the STATEMENTS of the archimedean leaves; `basisOfLinearIndependentOfCardEqFinrank`
-- turns a pair of eigenvectors into a basis in the classification of odd
-- involutions; `Ideal.Quotient.maximal_of_isField` and `MulEquiv.isField` turn
-- the residue-field hypotheses `hres`/`hresp` into maximality of the two primes;
-- and `Real.nonempty_algEquiv_or` together with
-- `Complex.real_algHom_eq_id_or_conj` is Artin–Schreier for `ℝ`, which is what
-- proves that `Γ_ℝ` has exactly two elements.
public import Mathlib.Algebra.Ring.ULift
public import Mathlib.Data.Real.Basic
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.LinearAlgebra.Complex.Module
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Basic
public import Mathlib.Algebra.Field.Equiv
public import Mathlib.Order.Interval.Set.Infinite
-- The Lang-Weil/Hensel cut of
-- `exists_bound_forall_padicAlgHom_of_geometricallyIrreducible`:
-- `Algebra.FormallySmooth.exists_mkₐ_comp_eq_of_isAdicComplete` (in
-- `RingTheory.Smooth.AdicCompletion`) IS the multivariate Hensel step and is why
-- no lifting lemma has to be written here; `Algebra.FinitePresentation` supplies
-- the polynomial presentation of a finite-type `ℚ`-algebra; `RingHom.FiniteType`
-- descends `LocallyOfFiniteType (specRatMap A)` to `Algebra.FiniteType ℚ A`
-- across the `ULift ℚ` base; and `RingHom.toRatAlgHom` upgrades the resulting
-- plain ring map to a `ℚ`-algebra map for free (a ring map between `ℚ`-algebras
-- is automatically `ℚ`-linear).
public import Mathlib.RingTheory.Smooth.AdicCompletion
public import Mathlib.RingTheory.FinitePresentation
public import Mathlib.RingTheory.RingHom.FiniteType
public import Mathlib.Algebra.Algebra.Hom.Rat
-- The nonzerodivisor leaf of the same Bertini decomposition is proven over
-- ASSOCIATED PRIMES rather than over "smooth ⟹ reduced": in a Noetherian ring
-- the zerodivisors are exactly the union of the FINITELY many associated
-- primes (`biUnion_associatedPrimes_eq_compl_nonZeroDivisors`,
-- `associatedPrimes.finite`), and each of them is dodged by one linear form
-- produced by `Submodule.exists_dual_map_eq_bot_of_notMem`
-- (`LinearAlgebra/Dual/Lemmas`, already imported below) applied to the
-- `ℚ`-linear parameterization `v ↦ ℓ_v` of `Mathlib.LinearAlgebra.Pi`.
public import Mathlib.RingTheory.Ideal.AssociatedPrime.Finiteness
public import Mathlib.LinearAlgebra.Pi
-- (`Mathlib.RingTheory.Ideal.Norm.AbsNorm` is imported once, above:
-- `Ideal.absNorm` is the residue cardinality `Nw` of a place of the
-- Moret–Bailly base `F`, and appears in the STATEMENTS both of the two
-- joints of the automorphic cut and of the Carayol/Shimura sub-cut —
-- the cyclotomic normalization leaf and the determinant-coefficient
-- bridge. Two concurrent owners added the same public import
-- independently; deduplicated at the 2026-07-25 merge.)
-- proof-only imports: the PROVEN 3-adic classification (Family-free —
-- see the module docstring for why `Lift.lean`/`Family.lean` must NOT
-- be imported), the shared Family-free deformation development (the
-- 2026-07-24 pillar-α proof-sharing refactor: it discharges pillar α
-- via `exists_hardlyRamified_lift_of_five_le`, and `Lift.lean`'s B6a
-- consumes the SAME development at `k = ZMod ℓ`), and the
-- matrix-charpoly bridges
import Fermat.FLT.GaloisRepresentation.HardlyRamified.Deformation
import Fermat.FLT.GaloisRepresentation.HardlyRamified.Threeadic
-- PUBLIC (2026-07-27): `HilbertHeckeAlgebra` and `heckeZFormMap` now appear in
-- STATEMENT position, in the two leaves of the modularity-lifting cut
-- (`nonempty_hilbertHeckeAlgebra_of_moretBaillySeed`,
-- `exists_classifyingHom_hilbertHeckeAlgebra`) below.  A proof-only import does
-- not re-export, so `import Deformation` alone — through which this module
-- already reaches it — does not suffice.  This adds NO module to any cone:
-- `Deformation.lean` already `public import`s `HilbertModularity`, so the
-- module was in this file's import closure before this line was written.
public import Fermat.FLT.GaloisRepresentation.HardlyRamified.HilbertModularity
-- the `charFrob` transport API (`GaloisRep.charFrob_map_algEquiv`,
-- `GaloisRep.exists_finset_isUnramifiedAt_map`), which discharges the base
-- of the solvable-descent chain (`heckeSystemDescendsTo_bot`)
-- PUBLIC (2026-07-27): `NumberField.finitePlaceEquiv` now appears in STATEMENT
-- position, in the Galois-invariance clause of `HeckeSystemDescendsTo` below, so
-- a proof-only import no longer suffices (it is not re-exported). This adds no
-- module to any cone — `GaloisRepTransport` was already imported here.
public import Fermat.FLT.Deformations.RepresentationTheory.GaloisRepTransport
import Mathlib.LinearAlgebra.Charpoly.ToMatrix
-- `LinearMap.det_eq_sign_charpoly_coeff`, for the determinant coefficient
-- of the Brauer-descent Frobenius charpolys
import Mathlib.LinearAlgebra.Charpoly.BaseChange
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
-- pillar-γ proof-only imports (see the module docstring's import note):
-- the Family-free Chebotarev/Brauer–Nesbitt machinery and its Kolchin
-- ingredients.
-- PROMOTED TO `public` 2026-07-27 (the Eichler–Shimura cut of STEP 2a): the
-- global Frobenius element `GaloisRepresentation.globalFrob` now appears in
-- SIGNATURE position, in the `congruence` and `det_frob` fields of
-- `CarayolPackage` below, and a non-public import does not re-export it.
-- Refuting check for cone growth, one line —
-- `grep -n 'GaloisRepresentation.Chebotarev' Fermat/FLT/Modularity/{Interface,Patching}.lean`:
-- BOTH consumers of this module already `public import` it, so this adds ZERO
-- modules to any cone.
public import Fermat.FLT.GaloisRepresentation.Chebotarev
import Fermat.FLT.GaloisRepresentation.BrauerNesbitt
import Mathlib.Tactic.NoncommRing
-- flatness-transfer proof-only imports (2026-07-24, the open-ideal
-- transport of `threeadicRealization_isFlat_of_witness`): the
-- finite-flat prolongation transport layer
-- (`GaloisRep.hasFlatProlongationAt_of_subsingleton`, the `I = ⊤`
-- case) and the compact-Hausdorff-ring API
-- (`IsLocalRing.isOpen_iff_finite_quotient`, openness ⇒ finite
-- congruence quotient). Both are Family-free.
import Fermat.FLT.Deformations.RepresentationTheory.FlatProlongation
import Mathlib.Topology.Algebra.Ring.Compact
-- ingredients of the Artin-induction proof of the group-theoretic
-- Brauer leaf (`brauer_induction_trivial_character`): linear duality
-- over `ℚ`, solvability of commutative groups, `Set.ncard` for the
-- strict-subgroup induction, and the `group` tactic
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.GroupTheory.Solvable
import Mathlib.Data.Set.Card
import Mathlib.Tactic.Group
-- residual-bridge proof-only imports (2026-07-25, the discharge of
-- `exists_residualCongruence_over_base`): the SHARED Family-free
-- Chebotarev–Brauer–Nesbitt conjugacy node (`Patching.lean`'s
-- `exists_conj_of_charFrob_eq_away` is a verbatim delegation to it, so no
-- extraction from that downstream module was needed), the `ℤ_[ℓ]` ideal
-- classification behind automatic continuity of the reduction map, the
-- module-topology automatic-continuity criterion, the topological-algebra
-- `ContinuousSMul` criterion, and base-change of ranks
import Fermat.FLT.GaloisRepresentation.BrauerNesbittConjugacy
import Mathlib.NumberTheory.Padics.RingHoms
-- `hensels_lemma`, for the explicit square root of the auxiliary quadratic field's
-- radicand in `ℚ_[p]` (`exists_padicSquare_of_dvd_sub_one`)
import Mathlib.NumberTheory.Padics.Hensel
-- `padicNorm` occurs in the SIGNATURES of the strong-approximation block below
-- (`exists_rat_strongApprox` and friends, Moret–Bailly §3.8's engine), so this must be
-- `public`; `Nat.chineseRemainderOfFinset` is proof-only, hence a plain import.
public import Mathlib.NumberTheory.Padics.PadicNorm
import Mathlib.Data.Nat.ChineseRemainder
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Mathlib.Topology.Algebra.Algebra
import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.Topology.KrullDimension
public import Mathlib.FieldTheory.Normal.Closure
-- for the junk coefficient ring of joint (a)
-- (`exists_numberField_surjection_of_finite`): a monic integer polynomial
-- irreducible mod `q`, its root, and the number field it generates.
import Mathlib.Algebra.Polynomial.Eval.Irreducible
import Mathlib.Algebra.Polynomial.Lifts
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.RingTheory.Polynomial.IsIntegral
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.FieldTheory.Finite.Basic
-- (`Mathlib.Algebra.Field.ULift` is already `public import`ed above)
public import Fermat.FLT.Modularity.AbelianScheme
-- `Fermat.TatePt` and the two leaves of the Tate-module construction
-- (`exists_tateFrame_of_levelStructure`, `exists_weilFrobeniusSystem_of_mult`),
-- consumed by `nonempty_hilbertBlumenthalPoint_of_isTwistedHilbertBlumenthalModuli`
public import Fermat.FLT.Modularity.TateModule
-- `isRegularLocalRing_stalk_of_smooth_over_field` and its commutative-algebra
-- tower were HOISTED out of this file into `Modularity/RegularStalks.lean`
-- on 2026-07-27, so that `Modularity/AbelianSchemeIsogeny.lean` — which is
-- UPSTREAM of this module through `TateModule` — could consume them for
-- `isRegularLocalRing_stalk_of_smooth`.  Imported explicitly (rather than
-- relied on transitively through `TateModule`) so that a later change to
-- that chain's publicity cannot silently remove them from proof bodies here.
public import Fermat.FLT.Modularity.RegularStalks
-- coefficient-ring locality (2026-07-25): the henselian-pair /
-- idempotent-lifting bricks used by `isLocalRing_of_finite_padicInt`
-- below, which removes `IsLocalRing A` from the `3`-adic Brauer-sum
-- citation. Public because that brick's companion
-- `IsLocalRing.of_henselianRing_of_isDomain` mentions `HenselianRing`
-- in its statement.
public import Fermat.FLT.Mathlib.RingTheory.AdicCompletion.Finite
public import Mathlib.RingTheory.Ideal.Over
public import Mathlib.RingTheory.Finiteness.Quotient
public import Mathlib.RingTheory.Artinian.Module
-- the coefficient-ring LOCALITY brick (2026-07-25,
-- `isLocalRing_of_finite_padicInt_domain`, which removes `IsLocalRing`
-- from the Carayol citation). `IsPrecomplete` occurs in the STATEMENTS of
-- the four supporting lemmas, so `AdicCompletion.Noetherian` — which also
-- carries the pin's `IsHausdorff` half for finite modules — is public;
-- Hensel's lemma and the finite-index quotient lemma are used only inside
-- proofs.
public import Mathlib.RingTheory.AdicCompletion.Noetherian
-- `Henselian` became PUBLIC on 2026-07-27: `schmidt_splits_of_henselian` (Schmidt
-- Lemma 5A(i)'s Hensel splitting step, below) takes `[HenselianRing A I]` in its
-- SIGNATURE, and `schmidt_leibniz_core` needs the instance
-- `IsAdicComplete.henselianRing` to fire for `K⟦X⟧` inside an `@[expose] public`
-- declaration — synthesis there ranges over the PUBLIC import closure only, so a
-- bare `import` gave `failed to synthesize HenselianRing (PowerSeries K) …` while
-- an identical scratch module compiled green. `AdicCompletion.Completeness`
-- carries the `IsAdicComplete (span {X}) (PowerSeries R)` instance that feeds it.
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.AdicCompletion.Completeness
import Mathlib.RingTheory.Ideal.Quotient.Index
-- proof-only (2026-07-25, `exists_degreeOnePlace_of_brauer`): the arithmetic
-- Frobenius `arithFrobAt` of a prime of a Dedekind domain acted on by a finite
-- group with fixed subring (`Mathlib.RingTheory.Frobenius`), the AKLB
-- invariance `Algebra.isInvariant_of_isGalois'` that supplies its hypothesis
-- for `𝓞 F / 𝓞 ℚ` (`Mathlib.RingTheory.Invariant.Galois`), and the finiteness
-- of the residue rings `𝓞 K ⧸ I` at a maximal ideal
-- (`Mathlib.NumberTheory.NumberField.Ideal.Basic`). None of these names occurs
-- in a statement of this module.
import Mathlib.RingTheory.Frobenius
import Mathlib.RingTheory.Invariant.Galois
import Mathlib.NumberTheory.NumberField.Ideal.Basic
-- proof-only (2026-07-25, for the Carayol/Shimura sub-cut, RETIRED
-- 2026-07-26 — kept because the `ULift`/`IntermediateField` material is
-- cheap and other proofs in this module may reach for it); note
-- `Mathlib.Algebra.Field.ULift` is already `public import`ed far above.
import Mathlib.Algebra.Module.ULift
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
-- proof-only (2026-07-26, `finite_heightOneSpectrum_mem_of_ne_zero`): only
-- finitely many height-one primes of a Dedekind domain divide a fixed nonzero
-- ideal (`Ideal.finite_factors`). This is what makes "the places of `F` over
-- `3`" a `Finset`, which is what lets the Carayol citation below be narrowed
-- so that it no longer claims local–global compatibility at the places where
-- its own `3`-adic representation ramifies.
import Mathlib.RingTheory.DedekindDomain.Factorization
-- proof-only (2026-07-26, the coefficient-ring QUOTIENT normalization
-- `exists_domain_coefficientRing_of_ringHom`, which removes `IsDomain` from
-- the Carayol citation): a basis of a free module base-changes
-- (`Module.Basis.baseChange`), and the kernel of a ring map into a domain is
-- prime (`RingHom.ker_isPrime`).
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.RingTheory.Ideal.Maps
-- proof-only (2026-07-26, `exists_invIdeal_generator`, the fractional-ideal
-- half of the archimedean node): invertibility of a nonzero ideal in a
-- Dedekind domain (`FractionalIdeal.coe_ideal_mul_inv`), the fact that `I⁻¹`
-- strictly contains `𝒪` for `I` proper and nonzero
-- (`FractionalIdeal.not_inv_le_one_of_ne_bot`), and the `CommGroupWithZero`
-- structure on fractional ideals that supplies the cancellation step. Nothing
-- from either module appears in a SIGNATURE here, so a plain import suffices.
import Mathlib.RingTheory.DedekindDomain.Ideal.Basic
import Mathlib.RingTheory.FractionalIdeal.Operations
-- SIGNATURE-BEARING (2026-07-26, the Euclidean chart on `X(ℝ)`): the implicit
-- function theorem in the form that returns an `OpenPartialHomeomorph`
-- (`HasStrictFDerivAt.implicitToOpenPartialHomeomorph`), which is what supplies
-- BOTH the continuity and the injectivity of the chart; the formal partial
-- derivatives `MvPolynomial.pderiv` in which the Jacobian hypothesis of
-- `exists_realPolynomialModel_of_affine_geometricallyIrreducible` is stated;
-- continuity of multivariate polynomial evaluation; and the finite-dimensional
-- transfer `LinearEquiv.toContinuousLinearEquiv` that moves the chart off
-- `ker` of the differential onto `Fin (m - c) → ℝ`. These are PUBLIC because
-- the statements of `mvPolynomialGradient`, `hasStrictFDerivAt_mvPolynomial_eval`
-- and `exists_euclideanPatch_of_polynomialSystem` mention them.
public import Mathlib.Analysis.Calculus.Implicit
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.Topology.Algebra.MvPolynomial
public import Mathlib.Analysis.Normed.Module.FiniteDimension
-- `SubmersivePresentation` / `IsStandardSmooth` / `Localization.Away` occur in the
-- SIGNATURES of the real-polynomial-model helpers below, so these must be `public`.
public import Mathlib.RingTheory.Smooth.StandardSmoothOfFree
public import Mathlib.RingTheory.Extension.Presentation.Submersive
public import Mathlib.RingTheory.Localization.Away.Basic
-- `IsLocalization.Away.tensorProductEquivTMulRight` (base change of a localization
-- is a localization), used in `smooth_quotient_of_smooth_localizationAway`.
public import Mathlib.RingTheory.Localization.BaseChange
-- proof-only: `X_pow_sub_C_irreducible_of_prime`, used to build the quadratic
-- extension `F(sqrt d)` inside `exists_quadraticExtension_trivial_of_isTotallyReal`.
-- Nothing from it occurs in a SIGNATURE, so a plain (non-`public`) import suffices.
import Mathlib.FieldTheory.KummerPolynomial
-- proof-only: `DivisionSemiring.to_moduleIsTorsionFree`, which supplies the
-- `Module.IsTorsionFree` side conditions of `IsAlgClosure.equivOfEquiv` used in
-- `exists_ringEquiv_algebraicClosure_uliftReal_complex`.
import Mathlib.Algebra.Module.Torsion.Field
-- `Proj`, `Proj.toSpecZero`, `Proj.awayι` and the `IsProper (Proj.toSpecZero 𝒜)`
-- instance, together with the total-degree grading on `MvPolynomial` and the
-- degree-zero part `HomogeneousLocalization.Away 𝒜 f`. These build `ℙⁿ_ℚ` in
-- `exists_properCompactification_affineSpace` (LEAF A1). PUBLIC because
-- `projSpaceGrading`, `projSpaceAwayEquiv` and friends mention
-- `homogeneousSubmodule` and `HomogeneousLocalization.Away` in their SIGNATURES.
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper
public import Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
-- proof-only (2026-07-27, `exists_auxiliaryPrime_of_neg`): Dirichlet's theorem on
-- primes in arithmetic progression (`Nat.forall_exists_prime_gt_and_modEq`) and the
-- Jacobi symbol (`jacobiSym.mod_right`, `jacobiSym.at_neg_one`, `legendreSym`).
-- Neither name occurs in a SIGNATURE of this module, so plain (non-`public`)
-- imports suffice and the analytic cone does NOT propagate to `Patching.lean`.
import Mathlib.NumberTheory.LSeries.PrimesInAP
import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
-- `WeierstrassCurve`, `WeierstrassCurve.IsElliptic`, the affine point group
-- `(E⁄K).Point` and the Galois action `WeierstrassCurve.Affine.Point.map` on it.
-- These appear in the SIGNATURES of the two archimedean leaves
-- `exists_ellipticSchemeOverField` and
-- `exists_realWeierstrassCurveWithConjTorsion`, so the import must be PUBLIC.
-- Note the group law on `(E⁄K).Point` needs `DecidableEq K`; both statements
-- supply it themselves with a `letI := Classical.typeDecidableEq _` rather than
-- taking an instance argument, so nothing downstream has to carry it.
public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
-- ARCHIMEDEAN-HALF ADDITION (2026-07-27): the `n`-torsion count
-- (`WeierstrassCurve.n_torsion_card`) and the divisibility of the geometric
-- point group (`TorsionCard.smul_surjective`), which are the two algebraic
-- inputs of `exists_realWeierstrassCurveWithConjTorsion`. Both modules were
-- ALREADY in this module's transitive import closure (through
-- `GaloisRepresentation/Chebotarev.lean`), so this adds ZERO modules to any
-- cone; it is `public` because those names are used in a proof body and a
-- purely transitive private route does not re-export them.
public import Fermat.FLT.EllipticCurve.Torsion
public import Fermat.FLT.EllipticCurve.TorsionCard
-- ARCHIMEDEAN-HALF ADDITION (2026-07-27): the `n`-torsion count
-- (`WeierstrassCurve.n_torsion_card`) and the divisibility of the geometric
-- point group (`TorsionCard.smul_surjective`), which are the two algebraic
-- inputs of `exists_realWeierstrassCurveWithConjTorsion`. Both modules were
-- ALREADY in this module's transitive import closure (through
-- `GaloisRepresentation/Chebotarev.lean`), so this adds ZERO modules to any
-- cone; it is `public` because those names are used in a proof body and a
-- purely transitive private route does not re-export them.
public import Fermat.FLT.EllipticCurve.Torsion
public import Fermat.FLT.EllipticCurve.TorsionCard
-- 2026-07-27, for `formallySmooth_of_isRegularLocalRing_of_essFiniteType_of_perfectField`
-- (Stacks 07EC): the `d = 0` base case is `Algebra.FormallySmooth.of_perfectField`
-- (`Smooth/Field.lean`), the inductive step is
-- `Algebra.FormallySmooth.of_formallySmooth_residueField_tensor` (`Smooth/Fiber.lean`,
-- flat + smooth special fibre ⟹ smooth), whose flatness hypothesis is discharged by
-- the Bézout torsion criterion of `Flat/TorsionFree.lean`.
public import Mathlib.RingTheory.Smooth.Field
public import Mathlib.RingTheory.Smooth.Fiber
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.EssentialFiniteness
public import Mathlib.RingTheory.Polynomial.Basic
-- PUBLIC (2026-07-27, the Break-D relocation): the Moret–Bailly supply chain,
-- moved out of this file so that `HardlyRamified/HilbertModularity.lean` — which
-- is UPSTREAM of this module — can consume `exists_moretBailly_seed_of_five_le`.
-- Public because `MoretBaillySeed`, `PotentialModularityWitness` and
-- `HilbertBlumenthalPoint` all appear in SIGNATURE position below.
public import Fermat.FLT.Modularity.MoretBailly

@[expose] public section

namespace GaloisRepresentation.Modularity

open IsDedekindDomain Polynomial

universe u v

/-- **Pillar α — Khare–Wintenberger minimal lifting** (PROVEN): an
IRREDUCIBLE hardly ramified mod-`ℓ` representation, `ℓ ≥ 5`, lifts to a
hardly ramified `ℓ`-adic representation: a characteristic-zero
coefficient package `O` — a local domain, module-finite over `ℤ_ℓ` with
its module topology and `ℤ_ℓ ↪ O` (classically: the image of the
universal hardly ramified deformation ring in a `ℚ̄_ℓ`-point, a subring
of the integers of a finite extension of `ℚ_ℓ`; taking the image rather
than the full valuation ring is what makes the residue field exactly
`k`, so that the reduction `π` below exists onto `k` itself) — carrying
a hardly ramified representation on `Fin 2 → O` whose Frobenius
characteristic polynomials reduce through a surjection `π : O →+* k` to
those of `ρbar` at every prime `q ∉ {2, ℓ}`.

Literature: Khare–Wintenberger, *Serre's modularity conjecture (I)*,
Invent. Math. 178 (2009), Theorem 4.1 and §4 (existence of minimal
`p`-adic lifts of prescribed type — here Serre type `(2, 2)`, i.e. the
hardly ramified conditions: cyclotomic determinant, unramified outside
`2ℓ`, flat at `ℓ`, tame square-trivial rank-1 quotient at `2`). The
proof machinery is Kisin's flat deformation theory (*Moduli of finite
flat group schemes, and modularity*, Ann. of Math. 170 (2009)), Böckle's
presentation bounds for global deformation rings, and Taylor's potential
modularity (*Remarks on a conjecture of Fontaine and Mazur*, J. Inst.
Math. Jussieu 1 (2002); *On the meromorphic continuation of degree two
L-functions*, Doc. Math. Extra Vol. (2006)) supplying the finiteness
input that forces the deformation ring to have a characteristic-zero
point. FLT blueprint ch. 4: "use Khare–Wintenberger to lift `ρ` to a
potentially modular `ℓ`-adic Galois representation of conductor 2".

SOUNDNESS AUDIT (both ways, 2026-07-24): (i) direct — this is KW
Theorem 4.1 specialized to type `(2, 2)`, a true nonvacuous theorem of
deformation theory (its proof nowhere presupposes that the target
spaces of Serre's conjecture are nonzero); (ii) collapse — the
hypothesis set (an irreducible hardly ramified mod-`ℓ` representation,
`ℓ ≥ 5`) is classically unsatisfiable (the headline theorem below), so
the statement is also vacuously sound; no honest weakening of the
conclusion can make the hypotheses satisfiable.

DISCHARGED (2026-07-24) BY THE ANTICIPATED PROOF-SHARING REFACTOR: the
deformation development formerly inlined in `Lift.lean` was audited
(it consumes nothing from `Family.lean`), extracted into the
Family-free module `HardlyRamified/Deformation.lean`, and generalized
from `ZMod ℓ` to the finite coefficient field `k`; this pillar is now
the verbatim application of its terminal theorem
`exists_hardlyRamified_lift_of_five_le`, and `Lift.lean`'s
`exists_hardlyRamifiedLift` (the in-tree twin, B6a) is the
instantiation of the SAME theorem at `k = ZMod ℓ` — one development,
two consumers, no cycle. The remaining depth lives in the shared
sorried leaves of `Deformation.lean` (Mazur representability, Carayol
subring descent, Chebotarev–Brauer–Nesbitt conjugacy, mod-`ℓ`
finiteness, minimal `W(k)`-presentations, Böckle relation bound).
CIRCULARITY GUARD (still binding on those leaves): must not be proven
through `Family.lean`, `Lift.lean`, or `Modularity/Interface.lean`. -/
theorem exists_hardlyRamified_lift_residual_of_five_le
    {ℓ : ℕ} (hℓodd : Odd ℓ) [Fact ℓ.Prime] (hℓ5 : 5 ≤ ℓ)
    {k : Type u} [Field k] [Finite k] [Algebra ℤ_[ℓ] k]
    [TopologicalSpace k] [DiscreteTopology k]
    {W : Type v} [AddCommGroup W] [Module k W] [Module.Finite k W]
    [Module.Free k W]
    (hW : Module.rank k W = 2) {ρbar : GaloisRep ℚ k W}
    (hρbar : IsHardlyRamified hℓodd hW ρbar)
    (hirr : ρbar.IsIrreducible) :
    ∃ (O : Type u) (_ : CommRing O) (_ : IsDomain O) (_ : TopologicalSpace O)
      (_ : IsTopologicalRing O) (_ : Algebra ℤ_[ℓ] O) (_ : IsLocalRing O)
      (_ : Module.Finite ℤ_[ℓ] O) (_ : IsModuleTopology ℤ_[ℓ] O)
      (_ : Function.Injective (algebraMap ℤ_[ℓ] O))
      (ρ : GaloisRep ℚ O (Fin 2 → O))
      (hrank : Module.rank O (Fin 2 → O) = 2)
      (_ : IsHardlyRamified hℓodd hrank ρ)
      (π : O →+* k) (_ : Function.Surjective π),
      ∀ (q : ℕ) (hq : q.Prime), q ≠ 2 → q ≠ ℓ →
        (ρ.charFrob hq.toHeightOneSpectrumRingOfIntegersRat).map π =
          ρbar.charFrob hq.toHeightOneSpectrumRingOfIntegersRat :=
  exists_hardlyRamified_lift_of_five_le hℓodd hW hℓ5 hρbar hirr

/-!
## The modularity-lifting cut over `F` (2026-07-24)

`exists_heckePackage_of_seed` below is the modularity-lifting stage of
pillar β: it turns the Moret–Bailly seed (a modular `ℓ`-adic
representation of `G_F` congruent to `ρbar|_{G_F}`) into modularity of
the Khare–Wintenberger lift `ρ|_{G_F}` itself.  It is now PROVEN as an
assembly over three sub-leaves cut at the literature joints:

* (c) `exists_residualCongruence_over_base` — the residual-to-`ℓ`-adic
  lifting bridge: `ρ|_{G_F}` really is a lift of `ρbar|_{G_F}`, as a
  statement about places of `F` (the rational hypothesis `hπ` only
  speaks about rational primes).  This is the *input datum* of the
  MLT, and it is pure Galois theory — Chebotarev over `ℚ`,
  Brauer–Nesbitt, and compatibility of `charFrob` with base change.
* (a) `exists_heckeEigensystem_of_congruentSeed` — `R = 𝕋` over `F`
  for the relevant deformation problem, TOGETHER WITH the rationality
  it delivers: the Taylor–Wiles/Kisin patching argument over the
  totally real base identifies `ρ|_{G_F}` with a Hilbert newform, and
  the Hecke algebra `𝕋` is generated over `ℤ` by the `T_w`, so the
  eigensystem is automatically defined over a NUMBER FIELD `E` — the
  Hecke field.  Its output is therefore `E`, an embedding
  `ψℓ : E ↪ ℚ̄_ℓ`, a GENUINE level/bad set `badF` containing the
  places over `ℓ`, and the `E`-valued eigenvalue function `a` with
  `ιO(tr ρ(Frob_w)) = ψℓ (a w)` away from `badF`.
* (b) `charFrob_map_eq_heckePolynomial_of_heckeTrace` — the
  DETERMINANT half of Carayol's normalization, which is PROVEN and
  carries no automorphic input at all: away from `ℓ` the cyclotomic
  determinant clause of `hρ` forces the constant coefficient to be the
  rational integer `Nw`
  (`charFrob_baseChange_coeff_zero_eq_absNorm`), so the trace datum of
  (a) already assembles the full Hecke polynomial
  `X² − a_w·X + Nw` over `E`.

RESTATEMENT OF (a) (2026-07-26 — a FAITHFULNESS REPAIR of the cut, not
a new decomposition; see that node's docstring for the audit it
replaces).  (a) used to output a RAW `ℚ̄_ℓ`-valued pair `(aF, dF)` with
`badF` existentially quantified and no tie to any Hecke datum; it was
consequently derivable from the shape of `charFrob` alone, and the
proof took `badF := ∅`.  The rationality was then demanded back from a
separate "Shimura rationality" citation downstream — which
DOUBLE-COUNTED, since `R = 𝕋` already delivers it, and which handed
that citation an instantiation at which it was classically FALSE (the
traces at the ramified places are not Hecke eigenvalues).  The repair
puts the rationality and the level where they belong, in (a); the
six downstream nodes that existed only to manufacture them
(`exists_heckeField_of_eigensystem`,
`exists_heckeField_mem_range_of_eigensystem`,
`exists_heckeSubfield_of_eigenvalues`,
`exists_heckeSubfield_of_determinants`,
`exists_heckeGenerators_of_eigenvalues`, `isIntegral_heckeEigenvalues`)
were DELETED, two of them sorried leaves that no argument could have
closed.

PATCHING-GENERALIZATION AUDIT (2026-07-24, the question this cut was
dispatched to answer).  Can (a) be discharged by generalizing
`Patching.lean` over a totally real base instead of citing it?  A
declaration-by-declaration audit of `Patching.lean` splits it in three:

1. *Base-field-agnostic already* — the whole commutative-algebra half
   carries no Galois data whatsoever and would transfer to any base
   verbatim: the coset prime-avoidance lemma
   (`exists_add_notMem_of_forall_not_le`), the regular-element and
   depth-descent chain (`isSMulRegular_of_forall_notMem_associatedPrimes`,
   `not_maximalIdeal_le_of_mem_associatedPrimes`,
   `exists_isRegular_quotSMulTop_of_isSMulRegular`), the
   Auslander–Buchsbaum instance
   (`free_of_isRegular_of_ofList_eq_maximalIdeal`), the power-series
   stratum (`isNoetherianRing_mvPowerSeries`,
   `exists_isRegular_ofList_eq_maximalIdeal_mvPowerSeries`,
   `free_of_isRegular_mvPowerSeries`), the patching objects and their
   payoff (`PatchedModule`, `PatchedModule.injective`, `taylorWilesAug`,
   `TaylorWilesSystem`, `TaylorWilesLevel`, `TaylorWilesTower`,
   `TaylorWilesSystem.exists_patchedModule`,
   `nonempty_linearEquiv_fin_of_free_over_quotient`), and the `ℤ_p`
   coefficient glue (`charP_of_ringHom_padicInt`, `ringHom_padicInt_eq`,
   `continuous_ringHom_padicInt`, `t2Space_of_isModuleTopology`).
   These consume only `ψ : Runiv →+* T` and ring/module data.
2. *Hard-pinned to `ℚ` through `IsHardlyRamified`* — every arithmetic
   declaration.  `IsHardlyRamified` is not merely stated for
   `GaloisRep ℚ`: its four clauses hard-code the RATIONAL local
   conditions (cyclotomic determinant over `ℚ̄`, unramifiedness indexed
   by rational primes through
   `Nat.Prime.toHeightOneSpectrumRingOfIntegersRat`, flatness at the
   rational place `ℓ`, and a tame quotient over the decomposition
   group `Γ ℚ_[2]` of the rational prime `2`).  So
   `HardlyRamifiedFiniteDeformation`, `IsWeaklyUniversalDeformation`,
   Mazur representability, the Hermite–Minkowski finiteness stratum
   (`finite_setOf_intermediateField_inertiaAt_le` is literally about
   `IntermediateField ℚ (AlgebraicClosure ℚ)` and absolute
   discriminants), Taylor–Wiles prime production
   (`IsTaylorWilesPrimeSet`, `exists_taylorWilesPrime`), Carayol trace
   generation and `exists_conj_of_charFrob_eq_away` would each need
   re-derivation over `F` — with genuinely different mathematics
   (relative discriminant bounds, places over `2` and `ℓ` rather than
   the primes themselves, Fontaine–Laffaille/Kisin local conditions at
   `w | ℓ` in place of a single flatness clause).
3. *Absent entirely on either base* — the Hecke side.  `Patching.lean`
   ABSTRACTS the automorphic input into structure fields (the modules
   `M n` of a `TaylorWilesSystem`); over `ℚ` those fields are
   inhabited only at the pillar-3b interface, and over `F` they would
   require Hilbert-modular Hecke modules, which the project does not
   have in any form.

Conclusion: generalizing `Patching.lean` would recycle its
commutative-algebra half but reprove its arithmetic half and still
leave the Hilbert-modular Hecke input open — i.e. it does not shorten
this leaf today.  The sound cut is therefore the LITERATURE cut
below, with (a) stated so that a future general-base patching node is
its natural discharge (its hypothesis list is exactly the
Taylor–Wiles input: a congruent modular seed, residual irreducibility
over `F`, and the deformation conditions carried by `hρ`).
-/

/-- **Automatic continuity of a ring homomorphism `ℤ_[ℓ] →+* k` into a
finite discrete field** (PROVEN helper for the residual bridge below):
the kernel of `f` is nonzero (`ℤ_[ℓ]` is infinite, `k` is finite) and
prime (`k` is a domain), hence — by the DVR ideal classification of
`ℤ_[ℓ]` (`PadicInt.ideal_eq_span_pow_p`) — contains `ℓ`; and the ideal
`(ℓ)` is the open unit ball of `ℤ_[ℓ]`
(`PadicInt.norm_lt_one_iff_dvd`), so `f` vanishes on a neighbourhood of
`0` and is therefore continuous.

(Downstream twin: `Modularity/Patching.lean`'s
`continuous_ringHom_padicInt`; that module IMPORTS this one, so the
lemma is restated here under a distinct name rather than imported — the
same convention as `charFrob_monic_of_free` below.  It is stated for a
bare homomorphism rather than for an `Algebra` instance — unlike this
module's own `charP_of_algebra_padicInt`, which is also declared below
the residual bridge and hence unavailable to it — because it is applied
to `π.comp (algebraMap ℤ_[ℓ] O)`, which is not an `algebraMap`.) -/
theorem continuous_ringHom_padicInt_of_finite {ℓ : ℕ} [Fact ℓ.Prime]
    {k : Type*} [Field k] [Finite k] [TopologicalSpace k]
    [DiscreteTopology k] (f : ℤ_[ℓ] →+* k) : Continuous f := by
  -- `f` kills `ℓ`: its kernel is a nonzero prime of the DVR `ℤ_[ℓ]`
  have hker : RingHom.ker f ≠ ⊥ := by
    intro hbot
    have hinj : Function.Injective f := by
      rw [RingHom.injective_iff_ker_eq_bot]
      exact hbot
    haveI := Finite.of_injective f hinj
    exact not_finite ℤ_[ℓ]
  obtain ⟨n, hn⟩ := PadicInt.ideal_eq_span_pow_p hker
  have hzero : f (ℓ : ℤ_[ℓ]) = 0 := by
    have hpow : (ℓ : ℤ_[ℓ]) ^ n ∈ RingHom.ker f := by
      rw [hn]
      exact Ideal.mem_span_singleton_self _
    exact RingHom.mem_ker.mp
      ((RingHom.ker_isPrime f).mem_of_pow_mem n hpow)
  -- the ideal `(ℓ)` is the open unit ball of `ℤ_[ℓ]`
  have hopen : IsOpen ((Ideal.span {(ℓ : ℤ_[ℓ])} : Ideal ℤ_[ℓ]) : Set ℤ_[ℓ]) := by
    have hball : ((Ideal.span {(ℓ : ℤ_[ℓ])} : Ideal ℤ_[ℓ]) : Set ℤ_[ℓ]) =
        Metric.ball (0 : ℤ_[ℓ]) 1 := by
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
  rw [hc, map_mul, hzero, zero_mul]

set_option backward.isDefEq.respectTransparency false in
/-- **Elementwise base change of the characteristic polynomial**
(PROVEN helper for the residual bridge below): at EVERY element `σ` of
`Gal(ℚ̄/ℚ)` the characteristic polynomial of the base-changed
representation `ρ.baseChange B` is the `algebraMap`-image of that of
`ρ`.  `(ρ.baseChange B) σ` is definitionally `LinearMap.baseChange B
(ρ σ)` (through the exposed module exports), so this is mathlib's
`LinearMap.charpoly_baseChange`.

(Downstream twin: `Modularity/Patching.lean`'s `charFrob_baseChange`,
which is this statement specialized to the arithmetic Frobenius at a
place of `ℚ`; that module imports this one, so the lemma is restated
here.  The ELEMENTWISE form is what the residual bridge needs: it must
compare the two representations at the Frobenius elements of the places
of `F`, which are elements of `G_ℚ` but not Frobenius elements of
places of `ℚ`.) -/
theorem charpoly_baseChange_apply {A : Type*} [CommRing A]
    [TopologicalSpace A] [IsTopologicalRing A] {B : Type*} [CommRing B]
    [TopologicalSpace B] [IsTopologicalRing B] [Algebra A B]
    [ContinuousSMul A B] {M : Type*} [AddCommGroup M] [Module A M]
    [Module.Finite A M] [Module.Free A M] (ρ : GaloisRep ℚ A M)
    (σ : Field.absoluteGaloisGroup ℚ) :
    ((ρ.baseChange B) σ).charpoly =
      ((ρ σ).charpoly).map (algebraMap A B) := by
  rw [show (ρ.baseChange B) σ = LinearMap.baseChange B (ρ σ) from rfl,
    LinearMap.charpoly_baseChange]

/-- **The residual congruence holds at EVERY element of `G_ℚ`, not only at
the Frobenius elements** (PROVEN 2026-07-26 — hoisted verbatim out of the
proof of `exists_residualCongruence_over_base` below, which had derived it
internally as `hall` and then thrown it away).

If the reduction of a rank-`2` lift `ρ` agrees with an IRREDUCIBLE rank-`2`
residual `ρbar` on the Frobenius characteristic polynomials at every rational
prime `q ∉ {2, ℓ}`, then `((ρ σ).charpoly).map π = (ρbar σ).charpoly` for
EVERY `σ ∈ G_ℚ`.

PROOF (unchanged, and it is Chebotarev + Brauer–Nesbitt): `π` is
automatically continuous, `O` carrying the `ℤ_ℓ`-module topology and `k`
being finite discrete, so `τ := ρ.baseChange k` is a genuine `k`-valued
representation whose charpoly at `σ` is `((ρ σ).charpoly).map π`
(`charpoly_baseChange_apply`).  `hπ` says `τ` and `ρbar` have the same
Frobenius charpolys away from `{2, ℓ}`, so
`GaloisRepresentation.exists_conj_of_charFrob_eq_away` — Chebotarev density
plus Brauer–Nesbitt for the irreducible `ρbar` — produces a CONJUGATING
isomorphism `e`, and conjugation leaves characteristic polynomials
unchanged.

WHY IT IS WORTH A NAME (2026-07-26).  Every route that presents `ρ|_{G_F}`
as an object of the `F`-level Hilbert deformation category of
`HardlyRamified/HilbertModularity.lean` needs exactly this: the field
`HilbertDeformationDatum.resid` is quantified over ALL of `Γ F`, while the
Frobenius-only form produced by `exists_residualCongruence_over_base` is
strictly weaker and cannot build a datum.  The `∀ σ` form was already
available inside that proof; not exporting it made the in-tree
modularity-lifting route look blocked when it was not.  See the ROUTE AUDIT
on `exists_heckeTraceAlgebra_of_congruentSeed` below, where this is
recorded as one of the four blockers and is the first of them to be
removed.

The hypothesis set is deliberately SMALLER than
`exists_residualCongruence_over_base`'s: neither `hℓodd`, `hℓ5`, `hZinj`,
`hρ`, `hρbar`, `hπsurj` nor the base field `F` and its properties play any
part in the argument, and dropping them makes the brick reusable at any
lift/residual pair with matching Frobenius data. -/
theorem forall_charpoly_map_eq_of_charFrob_map_eq
    {ℓ : ℕ} [Fact ℓ.Prime]
    {O : Type u} [CommRing O] [IsDomain O] [TopologicalSpace O]
    [IsTopologicalRing O] [Algebra ℤ_[ℓ] O] [IsLocalRing O]
    [Module.Finite ℤ_[ℓ] O] [IsModuleTopology ℤ_[ℓ] O]
    {ρ : GaloisRep ℚ O (Fin 2 → O)}
    (hrank : Module.rank O (Fin 2 → O) = 2)
    {k : Type u} [Field k] [Finite k] [Algebra ℤ_[ℓ] k]
    [TopologicalSpace k] [DiscreteTopology k]
    {W : Type v} [AddCommGroup W] [Module k W] [Module.Finite k W]
    [Module.Free k W]
    (hW : Module.rank k W = 2) {ρbar : GaloisRep ℚ k W}
    (hirr : ρbar.IsIrreducible)
    (π : O →+* k)
    (hπ : ∀ (q : ℕ) (hq : q.Prime), q ≠ 2 → q ≠ ℓ →
      (ρ.charFrob hq.toHeightOneSpectrumRingOfIntegersRat).map π =
        ρbar.charFrob hq.toHeightOneSpectrumRingOfIntegersRat) :
    ∀ σ : Field.absoluteGaloisGroup ℚ,
      ((ρ σ).charpoly).map π = (ρbar σ).charpoly := by
  classical
  -- the reduction map `π` is automatically continuous: `O` carries the
  -- `ℤ_[ℓ]`-module topology and `π ∘ algebraMap` lands in a finite discrete
  -- field
  have hcontπ : Continuous π :=
    IsModuleTopology.continuous_of_ringHom (R := ℤ_[ℓ]) π
      (continuous_ringHom_padicInt_of_finite (π.comp (algebraMap ℤ_[ℓ] O)))
  letI : Algebra O k := π.toAlgebra
  haveI : ContinuousSMul O k := continuousSMul_of_algebraMap O k
    (by rw [RingHom.algebraMap_toAlgebra]; exact hcontπ)
  -- the reduction `τ := ρ.baseChange k` of the lift, and its charpoly
  -- bookkeeping: at every Galois element its charpoly is the `π`-image
  have hbc : ∀ σ : Field.absoluteGaloisGroup ℚ,
      ((ρ.baseChange k) σ).charpoly = ((ρ σ).charpoly).map π := by
    intro σ
    rw [charpoly_baseChange_apply ρ σ, RingHom.algebraMap_toAlgebra]
  have hrankτ : Module.rank k (TensorProduct O k (Fin 2 → O)) = 2 := by
    rw [Module.rank_baseChange, hrank]
    simp
  -- `hπ` is exactly the Frobenius charpoly matching of `τ` with `ρbar`
  -- away from the two rational primes `2` and `ℓ`
  have hcf : ∀ (q : ℕ) (hq : q.Prime),
      hq.toHeightOneSpectrumRingOfIntegersRat ∉
        ({Nat.prime_two.toHeightOneSpectrumRingOfIntegersRat,
          (Fact.out : Nat.Prime ℓ).toHeightOneSpectrumRingOfIntegersRat} :
            Finset (HeightOneSpectrum (NumberField.RingOfIntegers ℚ))) →
      (ρ.baseChange k).charFrob hq.toHeightOneSpectrumRingOfIntegersRat =
        ρbar.charFrob hq.toHeightOneSpectrumRingOfIntegersRat := by
    intro q hq hqS
    have hq2 : q ≠ 2 := by
      rintro rfl
      exact hqS (Finset.mem_insert_self _ _)
    have hqℓ : q ≠ ℓ := by
      rintro rfl
      exact hqS (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
    rw [GaloisRep.charFrob_eq_charpoly_globalFrob, hbc,
      ← GaloisRep.charFrob_eq_charpoly_globalFrob]
    exact hπ q hq hq2 hqℓ
  -- Chebotarev + Brauer–Nesbitt: the reduction IS `ρbar`, up to conjugation
  obtain ⟨e, he⟩ := GaloisRepresentation.exists_conj_of_charFrob_eq_away hW
    hirr hrankτ (ρ.baseChange k) _ hcf
  -- hence the charpoly congruence holds at EVERY element of `G_ℚ`,
  -- conjugation leaving characteristic polynomials unchanged
  intro σ
  rw [← hbc σ, ← he, GaloisRep.conj_apply, LinearEquiv.charpoly_conj]

set_option linter.unusedVariables false in
/-- **The residual bridge over the Moret–Bailly base** (PROVEN
2026-07-25; sub-leaf (c) of the modularity-lifting cut — Chebotarev +
Brauer–Nesbitt + base change): the Khare–Wintenberger lift `ρ`,
restricted to `G_F`, is a lift of `ρbar|_{G_F}` — at all but finitely
many places `w` of `F` its Frobenius characteristic polynomial reduces
through `π` to that of `ρbar|_{G_F}`.
restricted to `G_F`, is a lift of `ρbar|_{G_F}` — at all but finitely
many places `w` of `F` its Frobenius characteristic polynomial reduces
through `π` to that of `ρbar|_{G_F}`.

This is the *residual input* the modularity lifting theorem consumes:
combined with the seed's own congruence (`seed.residual₀`) it says
that `ρ|_{G_F}` and the modular seed `σ` are congruent lifts of one
and the same residual representation, which is precisely the
hypothesis of an `R = 𝕋` theorem.

Classically: the hypothesis `hπ` gives equality of the reductions'
Frobenius characteristic polynomials at every rational prime
`q ∉ {2, ℓ}`; by Chebotarev density those primes' Frobenius classes
are dense in `Gal(ℚ̄/ℚ)` (the excluded primes are finite in number,
hence of density zero), so the semisimplifications of `ρ mod π` and
of `ρbar` have equal characteristic polynomials on all of `G_ℚ`, and
Brauer–Nesbitt identifies them; `ρbar` is irreducible, hence
semisimple, so `ρ mod π ≅ ρbar` as `G_ℚ`-representations (this is the
in-tree `Patching.lean` lemma `exists_conj_of_charFrob_eq_away`, whose
hypothesis shape is exactly `hπ`).  Restricting an isomorphism of
`G_ℚ`-representations to the open subgroup `G_F` preserves it, and
`charFrob` commutes with base change of the coefficient ring
(`Patching.lean`'s `charFrob_baseChange`), so at every place `w` of
`F` at which both sides are unramified the two characteristic
polynomials agree.  The finite exceptional set `badρ` collects the
places over `2` and `ℓ` and the places ramified in `F/ℚ` — the only
places where `charFrob` is not pinned by the unramified comparison.

PIN AUDIT (2026-07-24, RESOLVED 2026-07-25 — NO EXTRACTION WAS
NEEDED): the audit read the two ingredients as living only in the
downstream `Modularity/Patching.lean` and recommended extracting them
into a Family-free shared module (as the pillar-α refactor did for
`HardlyRamified/Deformation.lean`).  Re-auditing the import graph
showed that the extraction had ALREADY happened for the load-bearing
half: `Patching.lean`'s `exists_conj_of_charFrob_eq_away` is a verbatim
delegation to the shared Family-free node
`GaloisRepresentation.exists_conj_of_charFrob_eq_away` in
`BrauerNesbittConjugacy.lean` (whose only imports are `Chebotarev.lean`
and `BrauerNesbitt.lean`, both already imported here), so it is
consumed directly by a proof-only import, with no cycle.  The
remaining two bricks are elementary and are restated ABOVE under
distinct names, following the convention already used in this module
for `charFrob_monic_of_free`/`charFrob_natDegree_of_rank_two`:
`continuous_ringHom_padicInt_of_finite` (the twin of `Patching.lean`'s
`continuous_ringHom_padicInt`) and `charpoly_baseChange_apply` (the
ELEMENTWISE strengthening of `Patching.lean`'s `charFrob_baseChange`,
which is what the comparison at places of `F` actually needs).

PROOF (2026-07-25).  `O` carries the `ℤ_[ℓ]`-module topology and `k` is
finite discrete, so the reduction `π` is automatically continuous
(`IsModuleTopology.continuous_of_ringHom` over
`continuous_ringHom_padicInt_of_finite`); `k` is therefore a
topological `O`-algebra via `π.toAlgebra` and the reduction
`τ := ρ.baseChange k` of the lift exists as a genuine
`k`-representation of `G_ℚ`, of rank `2` (`Module.rank_baseChange`).
`hπ` says exactly that `τ.charFrob = ρbar.charFrob` at every rational
prime outside `{2, ℓ}` (through `charpoly_baseChange_apply` and
`GaloisRep.charFrob_eq_charpoly_globalFrob`), so the shared
Chebotarev–Brauer–Nesbitt node produces `e` with `τ.conj e = ρbar`.
Conjugation does not change characteristic polynomials
(`LinearEquiv.charpoly_conj`), so `((ρ σ).charpoly).map π =
(ρbar σ).charpoly` at EVERY `σ ∈ G_ℚ` — not merely at Frobenius
elements.  Since `charFrob` of a restricted representation at a place
`w` of `F` is by definition `charpoly` of `ρ` at the `G_ℚ`-element
`ι_{F}(globalFrob w)` (`GaloisRep.map_apply`), the congruence holds at
EVERY place `w` of `F` and the exceptional set is `∅` — a
strengthening of the statement's `∃ badρ`, which the classical
argument above bounded only by the ramified places.  The hypotheses
`hℓodd`, `hℓ5`, `hZinj`, `hρ`, `hρbar`, `hπsurj`, `hFtr`, `hFgal` and
`hirrF` are consequently not consumed; they are retained because the
consumer `exists_heckePackage_of_seed` supplies them and because
sub-leaves (a)/(b) of the same cut genuinely need them.

SOUNDNESS AUDIT (both ways, 2026-07-24): (i) direct — the statement is
true for ANY package satisfying its hypotheses, with no
abstract-quantification caveat: the argument above uses only `hπ`,
`hirr` and Chebotarev, all of which are hypotheses or theorems here,
and the exceptional set is existentially quantified (so no claim is
made about the ramified places); (ii) collapse — the hypothesis set
(an irreducible hardly ramified mod-`ℓ` representation, `ℓ ≥ 5`) is
classically unsatisfiable (headline below), so the statement is also
vacuously sound.  This is the only one of the three sub-leaves that is
directly true as stated, which is the reason it was cut off from (a).

CIRCULARITY GUARD (inherited from pillar β, load-bearing): no
discharge through `Family.lean`, `Lift.lean`, or
`Modularity/Interface.lean`. -/
-- `hπsurj`, `hFtr`, `hFgal` and `hirrF` are not consumed by the proof (see
-- the PROOF paragraph above) but are KEPT: the hypothesis list is the shared
-- interface of the three sub-leaves (a)/(b)/(c) of this cut, the consumer
-- `exists_heckePackage_of_seed` supplies them positionally, and (a)/(b)
-- genuinely need them.  The linter is silenced rather than the names being
-- mangled to `_`, so the docstring's references stay valid.
theorem exists_residualCongruence_over_base
    {ℓ : ℕ} (hℓodd : Odd ℓ) [Fact ℓ.Prime] (hℓ5 : 5 ≤ ℓ)
    {O : Type u} [CommRing O] [IsDomain O] [TopologicalSpace O]
    [IsTopologicalRing O] [Algebra ℤ_[ℓ] O] [IsLocalRing O]
    [Module.Finite ℤ_[ℓ] O] [IsModuleTopology ℤ_[ℓ] O]
    (hZinj : Function.Injective (algebraMap ℤ_[ℓ] O))
    {ρ : GaloisRep ℚ O (Fin 2 → O)}
    (hrank : Module.rank O (Fin 2 → O) = 2)
    (hρ : IsHardlyRamified hℓodd hrank ρ)
    {k : Type u} [Field k] [Finite k] [Algebra ℤ_[ℓ] k]
    [TopologicalSpace k] [DiscreteTopology k]
    {W : Type v} [AddCommGroup W] [Module k W] [Module.Finite k W]
    [Module.Free k W]
    (hW : Module.rank k W = 2) {ρbar : GaloisRep ℚ k W}
    (hρbar : IsHardlyRamified hℓodd hW ρbar)
    (hirr : ρbar.IsIrreducible)
    (π : O →+* k) (hπsurj : Function.Surjective π)
    (hπ : ∀ (q : ℕ) (hq : q.Prime), q ≠ 2 → q ≠ ℓ →
      (ρ.charFrob hq.toHeightOneSpectrumRingOfIntegersRat).map π =
        ρbar.charFrob hq.toHeightOneSpectrumRingOfIntegersRat)
    (F : Type u) [Field F] [NumberField F]
    (hFtr : NumberField.IsTotallyReal F) (hFgal : IsGalois ℚ F)
    (hirrF : (ρbar.map (algebraMap ℚ F)).IsIrreducible) :
    ∃ badρ : Finset (HeightOneSpectrum (NumberField.RingOfIntegers F)),
      ∀ w ∉ badρ,
        ((ρ.map (algebraMap ℚ F)).charFrob w).map π =
          (ρbar.map (algebraMap ℚ F)).charFrob w := by
  classical
  -- REFACTORED 2026-07-26: the Chebotarev + Brauer–Nesbitt argument that used
  -- to be inlined here is now the brick `forall_charpoly_map_eq_of_charFrob_map_eq`
  -- above, which states its `∀ σ : Γ ℚ` conclusion rather than discarding it.
  -- Nothing about this statement or its mathematics changed.
  have hall : ∀ σ : Field.absoluteGaloisGroup ℚ,
      ((ρ σ).charpoly).map π = (ρbar σ).charpoly :=
    forall_charpoly_map_eq_of_charFrob_map_eq hrank hW hirr π hπ
  -- in particular at the Frobenius elements of the places of `F`, which are
  -- the images in `G_ℚ` of the global Frobenii of `F`: the bad set is EMPTY
  refine ⟨∅, fun w _ => ?_⟩
  rw [GaloisRep.charFrob_eq_charpoly_globalFrob,
    GaloisRep.charFrob_eq_charpoly_globalFrob, GaloisRep.map_apply,
    GaloisRep.map_apply]
  exact hall _

/-- **A monic quadratic has the Hecke shape after any coefficient map**
(PROVEN helper, pure polynomial algebra): a monic polynomial of
`natDegree = 2` over a commutative ring equals
`X² + C p₁·X + C p₀` in its own coefficients, so its image under any
ring homomorphism `f` is `X² − C a·X + C d` with `a = −f p₁` and
`d = f p₀`.

This is the formal half of the eigensystem-extraction below: it turns
"the Frobenius characteristic polynomial is monic of degree `2`" into
the Hecke-polynomial SHAPE demanded by the `R = 𝕋` statement, with the
eigenvalue and the constant coefficient read off the polynomial itself.
It carries no arithmetic content whatsoever. -/
theorem map_eq_quadratic_of_monic_natDegree_two {A B : Type*} [CommRing A]
    [CommRing B] {p : Polynomial A} (hmonic : p.Monic)
    (hdeg : p.natDegree = 2) (f : A →+* B) :
    p.map f = X ^ 2 - C (-(f (p.coeff 1))) * X + C (f (p.coeff 0)) := by
  have hlead : p.coeff 2 = 1 := by
    have h := hmonic.coeff_natDegree
    rwa [hdeg] at h
  have hp : p = X ^ 2 + C (p.coeff 1) * X + C (p.coeff 0) := by
    ext n
    match n with
    | 0 => simp
    | 1 => simp
    | 2 => simp [hlead]
    | (m + 3) =>
      have hlt : p.natDegree < m + 3 := by rw [hdeg]; omega
      simp [Polynomial.coeff_eq_zero_of_natDegree_lt hlt]
  conv_lhs => rw [hp]
  simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_pow,
    Polynomial.map_X, Polynomial.map_C, map_neg]
  ring

set_option backward.isDefEq.respectTransparency false in
/-- **The Frobenius characteristic polynomial of a rank-`2` representation
has the Hecke shape after any coefficient map** (PROVEN helper, over an
ARBITRARY number-field base `K` — the general-base companion of
`charFrob_monic_of_free` and `charFrob_natDegree_of_rank_two` above,
which are pinned to `K = ℚ`): `charFrob` is by definition the
characteristic polynomial of the local Frobenius endomorphism of a
finite free module, hence monic of degree the rank, so for rank `2` its
`f`-image is `X² − C a·X + C d` with `a` and `d` read off the
polynomial's own coefficients. -/
theorem charFrob_map_eq_quadratic_of_rank_two {K : Type*} [Field K]
    [NumberField K] {A : Type*} [CommRing A] [Nontrivial A]
    [TopologicalSpace A] [IsTopologicalRing A] {M : Type*} [AddCommGroup M]
    [Module A M] [Module.Finite A M] [Module.Free A M] {B : Type*}
    [CommRing B] (v : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (ρ : GaloisRep K A M) (hdim : Module.rank A M = 2) (f : A →+* B) :
    (ρ.charFrob v).map f =
      X ^ 2 - C (-(f ((ρ.charFrob v).coeff 1))) * X +
        C (f ((ρ.charFrob v).coeff 0)) := by
  have hmonic : (ρ.charFrob v).Monic := by
    show ((ρ.toLocal v
      (Field.AbsoluteGaloisGroup.adicArithFrob v)).charpoly).Monic
    exact LinearMap.charpoly_monic _
  have hdeg : (ρ.charFrob v).natDegree = 2 := by
    show ((ρ.toLocal v
      (Field.AbsoluteGaloisGroup.adicArithFrob v)).charpoly).natDegree = 2
    rw [LinearMap.charpoly_natDegree]
    exact Module.finrank_eq_of_rank_eq (by exact_mod_cast hdim)
  exact map_eq_quadratic_of_monic_natDegree_two hmonic hdeg f

/-- **The coefficient embedding into `ℚ̄_ℓ`** (PROVEN helper, generic
commutative algebra): a domain `O` which is module-finite over `ℤ_ℓ`
and receives `ℤ_ℓ` injectively admits an INJECTIVE ring homomorphism
into `ℚ̄_ℓ`.

Classically `O` is the ring of integers of a finite extension of `ℚ_ℓ`
and the embedding is a choice of place; formally: the fraction field
`FractionRing O` receives `O` injectively
(`IsFractionRing.injective`), it is `ℤ_ℓ`-torsion-free because
`ℤ_ℓ → O → FractionRing O` is injective, and it is ALGEBRAIC over
`ℤ_ℓ` because `O` is (module-finiteness, `Algebra.IsAlgebraic.of_finite`)
and algebraicity passes to the fraction ring
(`IsFractionRing.isAlgebraic_iff'`); so the algebraically closed
`ℚ̄_ℓ` — itself a torsion-free `ℤ_ℓ`-algebra through
`ℤ_ℓ → ℚ_ℓ → ℚ̄_ℓ` — receives it by `IsAlgClosed.lift`, and a ring
homomorphism out of a FIELD is injective.

This is the only non-formal-shape ingredient of the `R = 𝕋` leaf's
conclusion as that leaf is stated (see its FORMAL-CONTENT AUDIT), and
it is exactly the `ιO` that the Hecke package's statements carry. -/
theorem exists_injective_ringHom_algebraicClosure_of_moduleFinite {ℓ : ℕ}
    [Fact ℓ.Prime] (O : Type*) [CommRing O] [IsDomain O] [Algebra ℤ_[ℓ] O]
    [Module.Finite ℤ_[ℓ] O]
    (hZinj : Function.Injective (algebraMap ℤ_[ℓ] O)) :
    ∃ ι : O →+* AlgebraicClosure ℚ_[ℓ], Function.Injective ι := by
  classical
  -- the fraction field of `O`, an algebraic torsion-free `ℤ_ℓ`-algebra
  -- (its `ℤ_ℓ`-algebra structure is the canonical localization one)
  have hOK : Function.Injective (algebraMap O (FractionRing O)) :=
    IsFractionRing.injective O (FractionRing O)
  haveI : Module.IsTorsionFree ℤ_[ℓ] O :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr hZinj
  haveI : IsScalarTower ℤ_[ℓ] O (FractionRing O) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : Module.IsTorsionFree ℤ_[ℓ] (FractionRing O) :=
    Module.isTorsionFree_iff_faithfulSMul.mpr inferInstance
  haveI : Algebra.IsAlgebraic ℤ_[ℓ] (FractionRing O) :=
    (IsFractionRing.isAlgebraic_iff' ℤ_[ℓ] O (FractionRing O)).1 inferInstance
  -- `ℚ̄_ℓ` as a torsion-free `ℤ_ℓ`-algebra through `ℤ_ℓ → ℚ_ℓ → ℚ̄_ℓ`
  letI : Algebra ℤ_[ℓ] (AlgebraicClosure ℚ_[ℓ]) :=
    ((algebraMap ℚ_[ℓ] (AlgebraicClosure ℚ_[ℓ])).comp
      (algebraMap ℤ_[ℓ] ℚ_[ℓ])).toAlgebra
  haveI : Module.IsTorsionFree ℤ_[ℓ] (AlgebraicClosure ℚ_[ℓ]) :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr
      (fun _ _ hxy => IsFractionRing.injective ℤ_[ℓ] ℚ_[ℓ]
        ((algebraMap ℚ_[ℓ] (AlgebraicClosure ℚ_[ℓ])).injective hxy))
  -- lift the algebraic extension into the algebraically closed target
  refine ⟨(IsAlgClosed.lift (R := ℤ_[ℓ]) (S := FractionRing O)
    (M := AlgebraicClosure ℚ_[ℓ])).toRingHom.comp
      (algebraMap O (FractionRing O)), fun _ _ hxy => hOK ?_⟩
  exact RingHom.injective
    (IsAlgClosed.lift (R := ℤ_[ℓ]) (S := FractionRing O)
      (M := AlgebraicClosure ℚ_[ℓ])).toRingHom hxy

/-- **Only finitely many places of a number field contain a fixed nonzero
integer** (PROVEN 2026-07-26; pure Dedekind-domain theory — the brick that
makes "the places of `F` over a rational prime" a `Finset`).

`w ∋ a` is `w.asIdeal ∣ (a)` (`Ideal.dvd_span_singleton`), and only finitely
many height-one primes divide a fixed nonzero ideal
(`Ideal.finite_factors`).

This is what lets a citation whose exceptional set `badF` is chosen
EXISTENTIALLY upstream be NARROWED by a hypothesis of the form
`∀ w, (p : 𝓞 F) ∈ w.asIdeal → w ∈ badF`: the exceptional set of a matching
clause can always be enlarged by the places over `p` for free, so demanding
that it already contains them costs the consumer nothing while removing from
the citation a claim it has no right to make.  One node below is narrowed
this way — `exists_threeadic_realization_of_heckePackage` (`hbad2`, `hbad3`,
`hbadℓ`, the places over `2`, `3` and `ℓ`).  (A second, the deleted
`exists_heckeSubfield_of_determinants`, was narrowed the same way at `ℓ`
before the 2026-07-26 repair of `exists_heckeEigensystem_of_congruentSeed`
made it redundant: that node now produces a `badF` already containing the
places over `ℓ`.)

RELOCATED 2026-07-26 from its original position further down this module:
the `ℓ`-adic narrowing of the Carayol/Shimura sub-cut needs it well before
the `3`-adic realization node does. -/
theorem finite_heightOneSpectrum_mem_of_ne_zero {F : Type*} [Field F]
    [NumberField F] (a : NumberField.RingOfIntegers F) (ha : a ≠ 0) :
    {w : HeightOneSpectrum (NumberField.RingOfIntegers F) | a ∈ w.asIdeal}.Finite := by
  have h : {w : HeightOneSpectrum (NumberField.RingOfIntegers F) | a ∈ w.asIdeal}
      = {w : HeightOneSpectrum (NumberField.RingOfIntegers F) |
          w.asIdeal ∣ Ideal.span {a}} := by
    ext w
    simp [Ideal.dvd_span_singleton]
  rw [h]
  exact Ideal.finite_factors (by simpa using ha)

/-- **Any finite set of places can be enlarged to contain all the places
above a fixed nonzero integer** (PROVEN 2026-07-26; the discharge form of
`finite_heightOneSpectrum_mem_of_ne_zero`).

This is the whole cost of the `hbad2`/`hbad3`/`hbadℓ` narrowings below:
because a matching clause `∀ w ∉ badF, …` only WEAKENS as `badF` grows, the
consumer can always move to `badF'` and hand the citation the hypotheses it
now demands. It is applied three times in a row at the `3`-adic call site,
at `2`, `3` and `ℓ`; the earlier conclusions survive the later enlargements
because each `badF'` contains its predecessor. Nothing downstream assumes
more. -/
theorem exists_finset_superset_of_places_mem {F : Type*} [Field F]
    [NumberField F] (badF : Finset (HeightOneSpectrum (NumberField.RingOfIntegers F)))
    (a : NumberField.RingOfIntegers F) (ha : a ≠ 0) :
    ∃ badF' : Finset (HeightOneSpectrum (NumberField.RingOfIntegers F)),
      badF ⊆ badF' ∧
      ∀ w : HeightOneSpectrum (NumberField.RingOfIntegers F),
        a ∈ w.asIdeal → w ∈ badF' := by
  classical
  refine ⟨badF ∪ (finite_heightOneSpectrum_mem_of_ne_zero a ha).toFinset,
    Finset.subset_union_left, ?_⟩
  intro w hw
  exact Finset.mem_union_right _ (by simpa using hw)

/-- **A ring that is module-finite over `ℤ` has number-field-valued
images in `ℚ̄_ℓ`** (PROVEN 2026-07-26; pure commutative algebra, no
arithmetic input).

Given any commutative ring `T` with `Module.Finite ℤ T` and any ring
homomorphism `ιT : T → ℚ̄_ℓ`, there is a NUMBER FIELD `E`, an embedding
`ψ : E ↪ ℚ̄_ℓ`, and a function `g : T → E` with `ψ ∘ g = ιT`.  Equivalently:
the image of `ιT` lies inside a number subfield of `ℚ̄_ℓ`.

PROOF.  `T` is spanned over `ℤ` by a finite set `S`, so every `t : T` is
integral over `ℤ` (`IsIntegral.of_finite`) and `ιT t` is integral over `ℤ`,
hence over `ℚ`.  Put `E₀ := ℚ(ιT '' S) ⊆ ℚ̄_ℓ`, which is finite-dimensional
over `ℚ` because `S` is finite and each generator is integral
(`IntermediateField.finiteDimensional_adjoin`), so `E₀` is a number field.
Every `ιT t` lies in `E₀`: `t` is a `ℤ`-combination of `S`, and `E₀` is
closed under addition and under multiplication by `Int.cast`
(`Submodule.span_induction`).  Finally `E₀ : Type 0`, so it is transported
to `Type u` along `ULift.ringEquiv` / `ULift.algEquiv`, exactly as
`exists_numberField_surjection_of_finite` above does.

WHY THIS IS NOT THE DELETED `isIntegral_heckeEigenvalues` (2026-07-26 — read
this before concluding the retired Carayol/Shimura sub-cut has been
resurrected).  That node was asked to prove `IsIntegral ℚ (aF w)` from
hypotheses that pinned `aF w` only inside `ιO O ⊆ ℚ̄_ℓ`, where `O` is
module-finite over `ℤ_[ℓ]`; integrality over `ℤ_[ℓ]` is orthogonal to
integrality over `ℤ`, so it had no admissible discharge and was correctly
deleted.  The hypothesis HERE is module-finiteness over `ℤ`, not over
`ℤ_[ℓ]`, and that single change makes the statement not merely provable but
easy.  It is also the mechanism the FAITHFULNESS REPAIR of
`exists_heckeEigensystem_of_congruentSeed` below already names in prose —
"`𝕋` is generated over `ℤ` by the Hecke operators `T_w`, so a point of `𝕋`
has values in a finite extension of `ℚ` by construction" — and all that is
done here is to make that sentence mechanical, so that the citation below
need not also assert it. -/
theorem exists_numberField_ringHom_of_moduleFinite_int
    {ℓ : ℕ} [Fact ℓ.Prime]
    (T : Type u) [CommRing T] [Module.Finite ℤ T]
    (ιT : T →+* AlgebraicClosure ℚ_[ℓ]) :
    ∃ (E : Type u) (_ : Field E) (_ : NumberField E)
      (ψ : E →+* AlgebraicClosure ℚ_[ℓ]) (g : T → E),
      ∀ t : T, ψ (g t) = ιT t := by
  classical
  obtain ⟨S, hS⟩ : (⊤ : Submodule ℤ T).FG := Module.finite_def.mp inferInstance
  have hint : ∀ t : T, IsIntegral ℚ (ιT t) := fun t =>
    ((IsIntegral.of_finite ℤ t).map ιT.toIntAlgHom).tower_top
  set E₀ : IntermediateField ℚ (AlgebraicClosure ℚ_[ℓ]) :=
    IntermediateField.adjoin ℚ (ιT '' (S : Set T))
  haveI : FiniteDimensional ℚ E₀ :=
    IntermediateField.finiteDimensional_adjoin (fun x hx => by
      obtain ⟨t, _, rfl⟩ := hx
      exact hint t)
  haveI : NumberField E₀ := {}
  have hmem : ∀ t : T, ιT t ∈ E₀ := by
    intro t
    have ht : t ∈ Submodule.span ℤ (S : Set T) := by rw [hS]; trivial
    induction ht using Submodule.span_induction with
    | mem x hx => exact IntermediateField.subset_adjoin _ _ ⟨x, hx, rfl⟩
    | zero => simp
    | add x y _ _ hx hy => simpa [map_add] using E₀.add_mem hx hy
    | smul c x _ hx =>
        have hc : ιT (c • x) = (c : AlgebraicClosure ℚ_[ℓ]) * ιT x := by
          simp [zsmul_eq_mul, map_mul, map_intCast]
        rw [hc]
        exact E₀.mul_mem (E₀.intCast_mem c) hx
  haveI : CharZero (ULift.{u} E₀) := (ULift.ringEquiv (R := E₀)).toRingHom.charZero
  haveI : FiniteDimensional ℚ (ULift.{u} E₀) :=
    LinearEquiv.finiteDimensional (ULift.algEquiv (R := ℚ) (A := E₀)).toLinearEquiv.symm
  haveI : NumberField (ULift.{u} E₀) := {}
  exact ⟨ULift.{u} E₀, inferInstance, inferInstance,
    E₀.subtype.comp (ULift.ringEquiv (R := E₀)).toRingHom,
    fun t => ULift.up ⟨ιT t, hmem t⟩, fun t => rfl⟩

/-! #### The modularity-lifting cut, SPLIT AT ITS TWO LITERATURE JOINTS
(2026-07-27)

`exists_heckeTraceAlgebra_of_congruentSeed` below is no longer a sorry node:
it is an assembly over the two leaves in this section plus
`exists_finset_superset_of_places_mem`.  The split is the one the ROUTE AUDIT
in that node's docstring describes, taken at the joint the literature itself
uses:

* **potential modularity at the GIVEN `F`** — the seed newform's Hecke algebra
  exists, at minimal level (`nonempty_hilbertHeckeAlgebra_of_moretBaillySeed`);
* **modularity lifting over `F`, i.e. `R_F = T_F`** — the lift `ρ|_{G_F}`, being
  a deformation of the same residual representation, is a point of that Hecke
  algebra (`exists_classifyingHom_hilbertHeckeAlgebra`).

Everything else that node used to assert — the `ℤ`-form and hence
`Module.Finite ℤ T`, the level `badF ⊇ {w ∣ ℓ}`, and the `coeff 1`/sign
bookkeeping between a Frobenius characteristic polynomial and a Hecke
eigenvalue — is now DISCHARGED, from `HilbertHeckeAlgebra`'s own fields
(`T₀`, `moduleFiniteT₀`, `heckeT₀`, `heckeT_eq`, `charFrobT`) and from
`exists_finset_superset_of_places_mem`.  This is the consumption of the
`ℤ`-RATIONAL STRUCTURE repair of 2026-07-27 that item 3 of that audit
announced was available and that nothing had yet used.

WHY THE `HilbertHeckeAlgebra` VOCABULARY.  Stating the residue in the
abstract-Hecke-algebra language of `HardlyRamified/HilbertModularity.lean`
rather than in raw `∃ T, ∃ ιT, …` form is what makes the in-tree `R_F = T_F`
stack directly applicable: `exists_hilbertHeckeDatum_of_hilbertHeckeAlgebra`,
`surjective_classifyingMap_hilbertHeckeDatum` and
`injective_classifyingMap_hilbertHeckeDatum` all take a
`HilbertHeckeAlgebra ℓ F ρbar` as an ordinary argument, so the second leaf
below is one composition away from them.  It costs the `public import` of that
module added at the head of this file, and no module in any cone. -/

/-- **Potential modularity at the GIVEN totally real base `F`** (SORRY leaf,
cut 2026-07-27 out of `exists_heckeTraceAlgebra_of_congruentSeed` below):
the Moret–Bailly seed over `F` is the eigensystem of a Hilbert newform whose
localized Hecke algebra, at MINIMAL level, exists as a
`HilbertHeckeAlgebra ℓ F ρbar`.

Note what this leaf does NOT mention: the lift `ρ`, its coefficient ring `O`,
the reduction `π` and the congruence `hcong` are all absent.  Producing the
seed's Hecke algebra is a statement about `ρbar` and the seed alone; the lift
enters only in `exists_classifyingHom_hilbertHeckeAlgebra` below.  Keeping the
two hypothesis packages disjoint is what makes each half independently
attackable.

CLASSICAL CONTENT.  `seed.modular₀` says the seed representation `σ` has the
Frobenius characteristic polynomials of a Hilbert newform `g` of parallel
weight `2` over `F`, and `seed.residual₀` says `σ` reduces to
`ρbar|_{G_F}`.  What has to be produced is the localization at the maximal
ideal of the Hecke algebra of `g`'s level attached to `ρbar|_{G_F}`, together
with the Galois representation `ρT` valued in it (Carayol/Taylor attachment
with local–global compatibility), the `ℤ`-form `T₀` (the classical rational
structure of the space of Hilbert cusp forms), and — this is the arithmetic
step, not the bookkeeping one — `isHilbertHardlyRamified` for `ρT`.  That last
field is what makes this LEVEL LOWERING over a totally real field: a
`HilbertHeckeAlgebra` is of the minimal level BY FIAT (see the FORMAL-CONTENT
AUDIT of `exists_hilbertHeckeDatum_of_hilbertHeckeAlgebra`), so the passage
from the seed's level — which `MoretBaillySeed` constrains only through the
finite set `bad₀` — to the minimal one is Fujiwara/Jarvis/Rajaei.  The same
obligation is recorded, for the `F` that `HilbertModularity.lean` produces
itself, in `nonempty_potentialHeckeDatum_of_five_le`; this leaf is its twin
for an `F` handed in from outside.

RELATION TO `nonempty_potentialHeckeDatum_of_five_le`, and why that leaf does
NOT discharge this one.  That leaf produces its own `F` together with the
extra field `residueCardTwo`; this one is handed an `F` that carries no such
guarantee.  A `PotentialHeckeDatum` therefore cannot be substituted — its `F`
is not this `F`, and this leaf's consumer states its conclusion about the
places of the `F` it is given.  See item 4 of the ROUTE AUDIT below.

Literature: Taylor, *Remarks on a conjecture of Fontaine and Mazur*, J. Inst.
Math. Jussieu 1 (2002), Theorem B; Carayol, Ann. Sci. ÉNS 19 (1986); Taylor,
*On Galois representations associated to Hilbert modular forms*, Invent. Math.
98 (1989); Fujiwara, *Deformation rings and Hecke algebras in the totally real
case*; Jarvis, Math. Ann. 313 (1999); Rajaei, J. reine angew. Math. 537 (2001).

CIRCULARITY GUARD (inherited from pillar β, load-bearing): no discharge
through `Family.lean`, `Lift.lean`, or `Modularity/Interface.lean`. -/
theorem nonempty_hilbertHeckeAlgebra_of_moretBaillySeed
    {ℓ : ℕ} (hℓodd : Odd ℓ) [Fact ℓ.Prime] (hℓ5 : 5 ≤ ℓ)
    {k : Type u} [Field k] [Finite k] [Algebra ℤ_[ℓ] k]
    [TopologicalSpace k] [DiscreteTopology k]
    {W : Type v} [AddCommGroup W] [Module k W] [Module.Finite k W]
    [Module.Free k W]
    (hW : Module.rank k W = 2) {ρbar : GaloisRep ℚ k W}
    (hρbar : IsHardlyRamified hℓodd hW ρbar)
    (hirr : ρbar.IsIrreducible)
    (F : Type u) [Field F] [NumberField F]
    (hFtr : NumberField.IsTotallyReal F) (hFgal : IsGalois ℚ F)
    (hirrF : (ρbar.map (algebraMap ℚ F)).IsIrreducible)
    (seed : MoretBaillySeed ℓ F (ρbar.map (algebraMap ℚ F))) :
    Nonempty (HilbertHeckeAlgebra ℓ F ρbar) :=
  sorry

/-- **`R_F = T_F` at the given `F`, in classifying-map form** (SORRY leaf, cut
2026-07-27 out of `exists_heckeTraceAlgebra_of_congruentSeed` below): the
hardly ramified lift `ρ`, restricted to `G_F` and residually congruent to
`ρbar|_{G_F}`, is a POINT of any Hilbert Hecke algebra of `ρbar` over `F` —
i.e. there is a ring homomorphism `φ : T → O` carrying the characteristic
polynomial of `ρT` to that of `ρ|_{G_F}`, at every element of `G_F`.

Taking `charpoly` at every `g` rather than `charFrob` at good places is
deliberate and matches `HilbertDeformationDatum.resid`,
`HilbertHeckeAlgebra.residT` and the three `IsWeaklyUniversal`
compatibilities, all of which are stated that way; the good-place Frobenius
statement is the instance at
`Field.absoluteGaloisGroup.map (algebraMap F (w.adicCompletion F))
(Field.AbsoluteGaloisGroup.adicArithFrob w)`, which is how the assembly below
consumes it (the same instantiation `HilbertHeckeAlgebra.residualT` uses).

## THE IN-TREE ROUTE, and it is a composition of PROVEN pieces

Quantifying over an ARBITRARY `H` is not a strengthening this leaf cannot
afford: `surjective_classifyingMap_hilbertHeckeDatum` and
`injective_classifyingMap_hilbertHeckeDatum` both take the Hecke algebra as an
ordinary argument, so the in-tree `R_F = T_F` already asserts `R ≃ T` for every
`H` satisfying the structure's axioms.  Concretely, with `𝒟'` the `F`-level
datum of `ρ|_{G_F}` (coefficients `O`), `𝒟` a weakly universal
trace-generated datum and `(𝒟T, e)` the datum of `H` from
`exists_hilbertHeckeDatum_of_hilbertHeckeAlgebra`:

* `𝒟.IsWeaklyUniversal` supplies BOTH `f : 𝒟.R → O` and `ψ : 𝒟.R → 𝒟T.R`,
  each carrying `∀ g, ((𝒟.ρ g).charpoly).map · = (·.ρ g).charpoly`;
* `ψ` is bijective by the two `classifyingMap` lemmas;
* `φ := f ∘ ψ⁻¹ ∘ e⁻¹` is the conclusion, the charpoly clause composing.

Building `𝒟'` from `ρ` needs `IsNoetherianRing O` (`IsNoetherianRing.of_finite`),
`IsAdic (maximalIdeal O)` and `IsAdicComplete` (from `[Module.Finite ℤ_[ℓ] O]`
and `[IsModuleTopology ℤ_[ℓ] O]` through
`ProfiniteLocalNoetherian.isAdic_isAdicComplete_of_isOpen_of_fg`, whose `hopen`
is mathlib's `IsLocalRing.isOpen_maximalIdeal`), and its `resid` clause in the
`∀ σ` form, which is `forall_charpoly_map_eq_of_charFrob_map_eq` above applied
to `hcong`.  Only the `hbasis` clause — that `nhds 0` in `O` has a basis of
open IDEALS, witnessed by `Ideal.map (algebraMap ℤ_[ℓ] O) ((maximalIdeal ℤ_[ℓ]) ^ n)`
— still has to be written out; the basis homeomorphism `O ≃ₜ (ι → ℤ_[ℓ])` used
at `Threeadic.lean`'s `exists_residue_package` is the intended input, `O` being
`ℤ_[ℓ]`-free as a domain with `hZinj` (`Module.free_of_finite_type_torsion_free'`).

## THE ONE REAL BLOCKER: the splitting condition at `2`, and it is NOT here

`exists_isWeaklyUniversal_hilbertDeformationDatum` and
`exists_heckeAlgebra_algEquiv_of_isWeaklyUniversal` both carry

    hw2 : ∀ w : HeightOneSpectrum (𝓞 F), ((2 : ℕ) : 𝓞 F) ∈ w.asIdeal →
      ¬ ((ℓ : ℤ) ∣ ((Nat.card (𝓞 F ⧸ w.asIdeal) : ℤ) ^ 2 - 1))

and this leaf is handed an `F` with no such constraint.  `hw2` CANNOT be added
as a hypothesis about a given totally real Galois `F` and then discharged
downstream — it is simply false for many of them (`F = ℚ(√5)` has `2` inert,
`N(w) = 4`, `N(w)² − 1 = 15`, divisible by `ℓ = 5`; the refutation block above
`isHilbertTameAtTwo_of_fibreProduct` records a machine-checked counterexample
at `ℓ = 5`, `F = ℚ(μ₅)`, `N(w) = 16`).  It has to be arranged where `F` is
BORN, i.e. by demanding `2 ∈ S` in the Moret–Bailly geometric chain
`exists_moretBailly_seed_of_five_le` → `exists_hilbertBlumenthalPoint_of_five_le`
→ … → `exists_normalSplitPoint_of_affine_curve`, which already produces an `F`
split completely at a prescribed finite set `S` — the obstruction being that
`S` is chosen ABOVE the Weil–Hensel bound `B` of
`exists_bound_forall_padicPoint_of_geometricallyIrreducible`, and `2` is below
it, so `2 ∈ S` costs a genuine `ℚ₂`-point of the twisted Hilbert–Blumenthal
variety lying on the Bertini curve.  That is the `Ω_2 ⊆ X(ℚ_2)` of
`PotentialHeckeDatum.residueCardTwo`.  **Refuting check: read
`exists_normalSplitPoint_of_affine_curve` in `Modularity/MoretBailly.lean` and
see whether its `S` is still constrained to lie above `B`.**

Consequently a discharge of THIS leaf along the in-tree route needs the
geometric chain repaired first, and the repair is a cut-level change to
`MoretBaillySeed`'s production, not to this statement.  Route (ii) — collapse,
the hypothesis package being classically unsatisfiable at `ℓ ≥ 5`, this
module's headline — remains available as it is for every leaf in this cluster.

WARNING ON THE INJECTIVITY HALF (2026-07-27, from the owner of the
Taylor–Wiles-prime cluster).  `injective_classifyingMap_hilbertHeckeDatum` is
the Taylor–Wiles patching half and rests on the open leaves
`exists_hilbertTaylorWilesPrimeSet` and `exists_hilbertPatchedModule`; on
branch `flt-lean-59` those are decomposed further and that decomposition
contains a FALSE leaf (`exists_hilbertFixing_rootsOfUnity_discrim_isSquare`,
refuted at `ℓ = 7`, curve 54b1).  Nothing here is tainted — none of those
declarations is in this tree and the two `classifyingMap` bricks are
axiom-clean — but expect the injectivity half to arrive with an ENLARGED
residual field `k`, and check that `HilbertHeckeAlgebra.πT`'s target survives
that enlargement before building on it.

Literature: Kisin, *Moduli of finite flat group schemes, and modularity*, Ann.
of Math. 170 (2009), Theorem (0.1); Taylor, *On the meromorphic continuation of
degree two L-functions*, Doc. Math. Extra Vol. (2006), Theorem 5.4; Fujiwara,
*Deformation rings and Hecke algebras in the totally real case*;
Skinner–Wiles; the FLT blueprint ch. 4.

CIRCULARITY GUARD (inherited from pillar β, load-bearing): no discharge
through `Family.lean`, `Lift.lean`, or `Modularity/Interface.lean`. -/
theorem exists_classifyingHom_hilbertHeckeAlgebra
    {ℓ : ℕ} (hℓodd : Odd ℓ) [Fact ℓ.Prime] (hℓ5 : 5 ≤ ℓ)
    {O : Type u} [CommRing O] [IsDomain O] [TopologicalSpace O]
    [IsTopologicalRing O] [Algebra ℤ_[ℓ] O] [IsLocalRing O]
    [Module.Finite ℤ_[ℓ] O] [IsModuleTopology ℤ_[ℓ] O]
    (hZinj : Function.Injective (algebraMap ℤ_[ℓ] O))
    {ρ : GaloisRep ℚ O (Fin 2 → O)}
    (hrank : Module.rank O (Fin 2 → O) = 2)
    (hρ : IsHardlyRamified hℓodd hrank ρ)
    {k : Type u} [Field k] [Finite k] [Algebra ℤ_[ℓ] k]
    [TopologicalSpace k] [DiscreteTopology k]
    {W : Type v} [AddCommGroup W] [Module k W] [Module.Finite k W]
    [Module.Free k W]
    (hW : Module.rank k W = 2) {ρbar : GaloisRep ℚ k W}
    (hρbar : IsHardlyRamified hℓodd hW ρbar)
    (hirr : ρbar.IsIrreducible)
    (π : O →+* k) (hπsurj : Function.Surjective π)
    (F : Type u) [Field F] [NumberField F]
    (hFtr : NumberField.IsTotallyReal F) (hFgal : IsGalois ℚ F)
    (hirrF : (ρbar.map (algebraMap ℚ F)).IsIrreducible)
    (badρ : Finset (HeightOneSpectrum (NumberField.RingOfIntegers F)))
    (hcong : ∀ w ∉ badρ,
      ((ρ.map (algebraMap ℚ F)).charFrob w).map π =
        (ρbar.map (algebraMap ℚ F)).charFrob w)
    (H : HilbertHeckeAlgebra ℓ F ρbar) :
    ∃ φ : H.T →+* O, ∀ g : Field.absoluteGaloisGroup F,
      ((H.ρT g).charpoly).map φ = ((ρ.map (algebraMap ℚ F)) g).charpoly :=
  sorry

/-- **`R = 𝕋` over the totally real base, in Hecke-algebra form** (PROVEN
2026-07-27 as an ASSEMBLY over the two leaves immediately above — it was a
sorry node from its cut on 2026-07-26 until then; the audit that follows is
kept because it is what the two leaves inherit).

Same hypotheses as `exists_heckeEigensystem_of_congruentSeed`; the
conclusion produces, instead of a number field and an `E`-valued
eigensystem, the object the Taylor–Wiles–Kisin argument actually
constructs: a HECKE ALGEBRA `T` that is **module-finite over `ℤ`**, an
embedding `ιT : T → ℚ̄_ℓ`, a genuine level `badF` containing the places
over `ℓ`, and Hecke operators `t w ∈ T` whose images are the Frobenius
traces of `ρ|_{G_F}` away from `badF`.

WHY THIS IS THE RIGHT PLACE TO CUT (2026-07-26).  The FAITHFULNESS REPAIR
recorded on the node below observes, correctly, that rationality is not a
theorem downstream of `R = 𝕋` but part of what `R = 𝕋` asserts — because
`𝕋` is generated over `ℤ` by the Hecke operators, so a point of `𝕋` has
values in a finite extension of `ℚ` "by construction".  That last phrase
was doing real work in PROSE and none in Lean.  Splitting it off turns it
into `exists_numberField_ringHom_of_moduleFinite_int` above (PROVEN, three
lines of commutative algebra), and leaves here exactly the automorphic
assertion.  Nothing is duplicated and nothing is deferred twice: the node
below is now an assembly of these two.

NON-VACUITY.  The `ℤ`-module-finiteness of `T` is what carries the whole
statement, and it is not satisfiable by the objects already in scope:
`T := O` fails because `O` is module-finite over `ℤ_[ℓ]`, which contains
an uncountable copy of `ℤ_[ℓ]` and is not a finite `ℤ`-module (this is
precisely the distinction on which the deleted `isIntegral_heckeEigenvalues`
foundered); `T := ℤ` fails because it would force every Frobenius trace to
be a rational integer.  `badF` is a `Finset` over the infinite place set of
`F`, so the clause is a genuine statement about cofinitely many places, and
the required `badF ⊇ {w ∣ ℓ}` only weakens it (enlarging `badF` is free —
`exists_finset_superset_of_places_mem` above).

RELATION TO `HardlyRamified/HilbertModularity.lean` — READ THIS BEFORE
ATTACKING (2026-07-26; this module's MISSING MACHINERY list was STALE).
That file, which is in this module's import cone through
`HardlyRamified/Deformation.lean`, already carries an `R_F = T_F`
development over a totally real base:

* `HilbertHeckeAlgebra ℓ F ρbar` — an abstract Hecke algebra `T` with
  `heckeT : places → T`, `charFrobT` (`(ρT.charFrob w).coeff 1 = -heckeT w`,
  literally the shape of the conclusion here) and residual modularity;
* `exists_heckeAlgebra_algEquiv_of_isWeaklyUniversal` — `R_F ≃ₐ[ℤ_[ℓ]] T`,
  PROVEN over its own leaves, i.e. Taylor–Wiles–Kisin patching over `F`;
* `nonempty_potentialHeckeDatum_of_five_le` — the potential-modularity
  production leaf.

So item (4) of the missing-machinery list below EXISTS IN THIS TREE, and
item (2) exists in abstract form.

## ROUTE AUDIT, 2026-07-26 (SECOND PASS — it CORRECTS the first pass, which
named the wrong repair).  State the check that refutes each item, per the
standing rule; every claim below was re-run against the tree on that date.

The in-tree assembly that WOULD close this leaf is completely explicit, and
it is worth writing down because three of its four ingredients are already
present.  Take `𝒟'` the `F`-level datum of `ρ|_{G_F}` (coefficients `O`),
`𝒟` a weakly universal trace-generated datum, `𝒟T` the datum of the Hecke
algebra.  Then `𝒟.IsWeaklyUniversal` supplies BOTH classifying maps —
`f : 𝒟.R → O` and `ψ : 𝒟.R → 𝒟T.R` — each carrying
`∀ g, ((𝒟.ρ g).charpoly).map · = (·.ρ g).charpoly`; `ψ` is bijective by
`surjective_classifyingMap_hilbertHeckeDatum` and
`injective_classifyingMap_hilbertHeckeDatum` (both EXPORTED, both taking the
classifying map explicitly, so the ρ-compatibility that
`exists_heckeAlgebra_algEquiv_of_isWeaklyUniversal` discards is recoverable
without touching that file); and
`exists_hilbertHeckeDatum_of_hilbertHeckeAlgebra` is PROVEN with
`𝒟T.ρ = T.ρT` on the nose.  So `ιT := ιO ∘ f ∘ ψ⁻¹` and `t w := heckeT w`
give the conclusion verbatim, `charFrobT` supplying the sign.

WARNING ON THE INJECTIVITY HALF (2026-07-27, from the owner of the
Taylor–Wiles-prime cluster; recorded here because this audit RECOMMENDS that
route).  `injective_classifyingMap_hilbertHeckeDatum` is the Taylor–Wiles
patching half, and in THIS tree it rests on the open leaves
`exists_hilbertTaylorWilesPrimeSet` and `exists_hilbertPatchedModule`.  On
branch `flt-lean-59` those have been decomposed further, and that
DECOMPOSITION contains a FALSE leaf:
`exists_hilbertFixing_rootsOfUnity_discrim_isSquare` is refuted by ℓ = 7,
curve 54b1, `F = F₀·M` with `F₀ ⊂ ℚ(E[7])` the fixed field of `ρ̄⁻¹(H)`,
`H = N(T_ns) ∩ SL₂(𝔽₇)` of order 16 — every element of `H` has
`tr² − 4·det ∈ {0, 3, 5}` and `3`, `5` are non-squares mod `7`, so the
conclusion already fails at `n = 0`.  (Re-verified independently here by
direct enumeration of `SL₂(𝔽₇)`: `|N(T_ns)| = 16` and the discriminant set
is exactly `{0, 3, 5}` against squares `{0, 1, 2, 4}`.)

Nothing in THIS module is tainted — none of those declarations exists in
this tree, and the two bricks above are axiom-clean
`[propext, Classical.choice, Quot.sound]`, hence consume no sorried leaf at
all.  What the refutation costs is the SHAPE of the patching input: the
falsity is manufactured by quantifying over arbitrary number fields `F`
while demanding eigenvalues in a FIXED residual field `k`, and the repair is
to thread the quadratic enlargement of `k` through `IsTaylorWilesPrimeSet`.
So a future owner closing this leaf along the route above should expect the
injectivity half to arrive with an ENLARGED `k`, and should check that
`HilbertHeckeAlgebra.πT`'s target survives that enlargement before building
on it.

FOUR blockers stood in the way.  TWO ARE NOW GONE:

1. *(REMOVED 2026-07-26.)* `HilbertDeformationDatum.resid` is quantified over
   ALL of `Γ F`, while this leaf is handed only the Frobenius-level `hcong`.
   The `∀ σ` form was already derived inside the proof of
   `exists_residualCongruence_over_base` and thrown away; it is now exported
   as `forall_charpoly_map_eq_of_charFrob_map_eq` above.  Refuting check:
   grep that name.
2. *(REMOVED, modulo one commutative-algebra brick.)* Building `𝒟'` needs
   `IsNoetherianRing O`, `IsAdic (maximalIdeal O)` and `IsAdicComplete`.
   `IsNoetherianRing.of_finite ℤ_[ℓ] O` gives the first; the other two follow
   from `[Module.Finite ℤ_[ℓ] O] [IsModuleTopology ℤ_[ℓ] O]` via
   `ProfiniteLocalNoetherian.isAdic_isAdicComplete_of_isOpen_of_fg`, whose
   `hopen` is mathlib's `IsLocalRing.isOpen_maximalIdeal`
   (`Mathlib/Topology/Algebra/Ring/Compact.lean`, which also has
   `isOpen_maximalIdeal_pow`) and whose compact-Hausdorff input is the basis
   homeomorphism `O ≃ₜ (ι → ℤ_[ℓ])` used verbatim at `Threeadic.lean`'s
   `exists_residue_package` (`O` is `ℤ_[ℓ]`-FREE because it is a domain with
   `hZinj`, hence torsion-free over a PID —
   `Module.free_of_finite_type_torsion_free'`).  Only the `hbasis` clause —
   that `nhds 0` has a basis of open IDEALS — still has to be written out;
   the intended witnesses are the ideals
   `Ideal.map (algebraMap ℤ_[ℓ] O) ((maximalIdeal ℤ_[ℓ]) ^ n)`, which the
   basis homeomorphism carries to `Set.pi univ (fun _ => ℓ ^ n • ℤ_[ℓ])`.
   Refuting check: read `Threeadic.lean:135-150`.

ONE REMAINS (item 4).  Item 3 was retired on 2026-07-27 by running its own
refuting check; the record of what it claimed, and why it is now false, is kept
below so that the next audit does not re-derive it:

3. *(REMOVED 2026-07-27 — REFUTED BY ITS OWN REFUTING CHECK.)*  This item
   said `HilbertHeckeAlgebra.T` is module-finite over `ℤ_[ℓ]` and not over
   `ℤ`, that the `ℚ`-rational (Shimura-rationality) structure "is recorded
   nowhere", and that closing it costs a `Tℤ`/`jℤ`/`tℤ` package plus a
   producing leaf.  **All three claims are now false.**  Running the check
   this item itself prescribes — `grep 'Module.Finite ℤ ' HilbertModularity.lean`
   — returns hits, because the `ℤ`-RATIONAL STRUCTURE repair of 2026-07-27
   added the `ℤ`-form to the structure directly: `HilbertHeckeAlgebra` now
   carries the fields `T₀`, `[commRingT₀]`, `[moduleFiniteT₀ : Module.Finite ℤ T₀]`
   and `[moduleFreeT₀ : Module.Free ℤ T₀]`, with `T` pinned to the local factor
   of `W(k) ⊗_{ℤ_[ℓ]} (ℤ_[ℓ] ⊗_ℤ T₀)` at `𝔪` through `TEquiv`.  So the `ℤ`-form
   is not a cost to be paid here; it is a hypothesis this leaf may consume.
     The consumer is already PROVEN and already in this file:
   `exists_numberField_ringHom_of_moduleFinite_int` takes exactly
   `[Module.Finite ℤ T]` plus `ιT : T →+* ℚ̄_ℓ` and produces the number field
   `E` with `ψ : E ↪ ℚ̄_ℓ` factoring `ιT` — which is precisely the `Module.Finite ℤ T`
   conjunct of this leaf's own conclusion.  It is applied that way at
   `exists_hilbertNewform_of_heckeTraceAlgebra` below.
     **Do not re-derive Shimura rationality for this leaf.**  What remains is
   item 4 alone.

4. **THE REAL BLOCKER, AND IT IS NOT THE ONE THIS DOCSTRING USED TO NAME.**
   The first pass said the repair was to "re-plumb this leaf's consumer chain
   so that `F` comes from `PotentialHeckeDatum` rather than from
   `MoretBaillySeed`".  That is NOT possible and NOT the repair: this leaf's
   conclusion is about the places of the `F` it is HANDED, so a `F` produced
   elsewhere cannot be substituted.  What `PotentialHeckeDatum` really
   contributes is one FIELD, `residueCardTwo` — every `w ∣ 2` has residue
   field `𝔽₂` — and the `F`-level deformation category genuinely needs it:
   `exists_isWeaklyUniversal_hilbertDeformationDatum` demands
   `ℓ ∤ N(w)² − 1` at every `w ∣ 2`, and the refutation block above
   `isHilbertTameAtTwo_of_fibreProduct` records a machine-checked
   counterexample (`ℓ = 5`, `F = ℚ(μ₅)`, `N(w) = 16`) without it.

   `residueCardTwo` CANNOT be added as a hypothesis or a leaf about a GIVEN
   `F` — that would be a FALSE leaf, since a general totally real Galois `F`
   has `2` inert (`ℚ(√5)`).  It has to be arranged where `F` is BORN, and in
   this module `F` is born in the geometric chain
   `exists_moretBailly_seed_of_five_le` → `exists_hilbertBlumenthalPoint_of_five_le`
   → `exists_totallyReal_point_of_geometricallyIrreducible` →
   `exists_totallyReal_point_of_affine_geometricallyIrreducible` →
   `exists_normalRealPoint_of_affine_curve` → `exists_normalSplitPoint_of_affine_curve`.

   That chain ALREADY produces an `F` split completely at a prescribed finite
   set `S` of primes — so the mechanism exists.  What blocks `2 ∈ S` is that
   `S` is chosen by `exists_primes_forall_sup_eq_top_of_isOpen` ABOVE the
   Weil–Hensel bound `B` of
   `exists_bound_forall_padicPoint_of_geometricallyIrreducible`, precisely so
   that local solvability is free.  `2` is below that bound, so demanding
   `2 ∈ S` costs a genuine `X(ℚ₂)`-point of the twisted Hilbert–Blumenthal
   variety — exactly the `Ω_2 ⊆ X(ℚ_2)` that
   `PotentialHeckeDatum.residueCardTwo`'s own docstring says the citation
   pays for — and, because the chain passes through a BERTINI cut to an
   affine curve, that `ℚ₂`-point must additionally be arranged to lie on the
   curve.  Refuting check: read `exists_normalRealPoint_of_affine_curve` and
   see whether its `S` is still constrained to lie above `B`.

Consequently the cut-level repair is NOT on `MoretBaillySeed`'s side at all:
it is (3) on the Hecke algebra, and (4) on the MORET–BAILLY GEOMETRIC CHAIN,
whose Moret–Bailly statement is currently specialized to `S = {∞}` and must
gain finite-place local conditions (BLGGT Prop. 3.1.1 has the general `S`;
Taylor 2002 uses it with `2 ∈ S`).  Anyone attacking this leaf should start
at (4), because (1)–(3) are cheap and (4) is what actually decides whether
the in-tree route exists.

## ASSEMBLY (2026-07-27) — THIS NODE IS NO LONGER A SORRY NODE

The audit above is now the docstring of two leaves rather than of this one.
Its item (3) is CONSUMED here — nothing further to do — and its item (4) is
inherited verbatim by `exists_classifyingHom_hilbertHeckeAlgebra`, where it
belongs, because it is the `F`-level DEFORMATION category that needs the
splitting condition at `2` and not the production of the Hecke algebra.  The
proof is:

* `nonempty_hilbertHeckeAlgebra_of_moretBaillySeed` (SORRY — potential
  modularity at the given `F`, i.e. the seed newform's minimal-level Hecke
  algebra) gives `H : HilbertHeckeAlgebra ℓ F ρbar`;
* `exists_classifyingHom_hilbertHeckeAlgebra` (SORRY — `R_F = T_F`) gives
  `φ : H.T →+* O` with `∀ g, ((H.ρT g).charpoly).map φ = ((ρ|_{G_F}) g).charpoly`;
* `T := H.T₀`, whose `Module.Finite ℤ` is the structure field
  `moduleFiniteT₀` added by the `ℤ`-RATIONAL STRUCTURE repair of 2026-07-27;
* `ιT := ιO ∘ φ ∘ TEquiv.symm ∘ heckeZFormMap`, so that `ιT (heckeT₀ w)` is
  `ιO (φ (heckeT w))` by `heckeT_eq`;
* `badF` from `exists_finset_superset_of_places_mem H.bad ℓ`, which is what
  supplies the `{w ∣ ℓ} ⊆ badF` clause;
* the trace identity is `charFrobT` (`(ρT.charFrob w).coeff 1 = -heckeT w`)
  fed through `φ` at `coeff 1`, exactly as `HilbertHeckeAlgebra.residualT`
  does with `πT`.

FORMAL-CONTENT NOTE.  Two hypotheses of this statement are NOT used by the
assembly and are underscore-prefixed so that the fact is mechanically visible
rather than merely asserted:

* `_hπ`, the `ℚ`-level residual congruence at the good rational primes, is
  subsumed by `hcong`, the `F`-level congruence, which is also handed in and
  is the one the deformation-theoretic argument consumes;
* `_hιO`, injectivity of the coefficient embedding, is not needed once the
  Hecke algebra is produced with its own embedding — the conclusion is an
  identity of elements of `ℚ̄_ℓ`, true for any ring map `ιO`.

Neither is removed from the signature: the consumer
`exists_heckeEigensystem_of_congruentSeed` applies this node positionally, and
a future owner who reinstates a stronger conclusion (say one asserting that
`ιT` is injective) inherits the binders it will need.

CIRCULARITY GUARD (inherited from pillar β, load-bearing): no discharge
through `Family.lean`, `Lift.lean`, or `Modularity/Interface.lean`. -/
theorem exists_heckeTraceAlgebra_of_congruentSeed
    {ℓ : ℕ} (hℓodd : Odd ℓ) [Fact ℓ.Prime] (hℓ5 : 5 ≤ ℓ)
    {O : Type u} [CommRing O] [IsDomain O] [TopologicalSpace O]
    [IsTopologicalRing O] [Algebra ℤ_[ℓ] O] [IsLocalRing O]
    [Module.Finite ℤ_[ℓ] O] [IsModuleTopology ℤ_[ℓ] O]
    (hZinj : Function.Injective (algebraMap ℤ_[ℓ] O))
    {ρ : GaloisRep ℚ O (Fin 2 → O)}
    (hrank : Module.rank O (Fin 2 → O) = 2)
    (hρ : IsHardlyRamified hℓodd hrank ρ)
    {k : Type u} [Field k] [Finite k] [Algebra ℤ_[ℓ] k]
    [TopologicalSpace k] [DiscreteTopology k]
    {W : Type v} [AddCommGroup W] [Module k W] [Module.Finite k W]
    [Module.Free k W]
    (hW : Module.rank k W = 2) {ρbar : GaloisRep ℚ k W}
    (hρbar : IsHardlyRamified hℓodd hW ρbar)
    (hirr : ρbar.IsIrreducible)
    (π : O →+* k) (hπsurj : Function.Surjective π)
    (_hπ : ∀ (q : ℕ) (hq : q.Prime), q ≠ 2 → q ≠ ℓ →
      (ρ.charFrob hq.toHeightOneSpectrumRingOfIntegersRat).map π =
        ρbar.charFrob hq.toHeightOneSpectrumRingOfIntegersRat)
    (F : Type u) [Field F] [NumberField F]
    (hFtr : NumberField.IsTotallyReal F) (hFgal : IsGalois ℚ F)
    (hirrF : (ρbar.map (algebraMap ℚ F)).IsIrreducible)
    (seed : MoretBaillySeed ℓ F (ρbar.map (algebraMap ℚ F)))
    (badρ : Finset (HeightOneSpectrum (NumberField.RingOfIntegers F)))
    (hcong : ∀ w ∉ badρ,
      ((ρ.map (algebraMap ℚ F)).charFrob w).map π =
        (ρbar.map (algebraMap ℚ F)).charFrob w)
    (ιO : O →+* AlgebraicClosure ℚ_[ℓ]) (_hιO : Function.Injective ιO) :
    ∃ (T : Type u) (_ : CommRing T) (_ : Module.Finite ℤ T)
      (ιT : T →+* AlgebraicClosure ℚ_[ℓ])
      (badF : Finset (HeightOneSpectrum (NumberField.RingOfIntegers F)))
      (t : HeightOneSpectrum (NumberField.RingOfIntegers F) → T),
      (∀ w : HeightOneSpectrum (NumberField.RingOfIntegers F),
          (ℓ : NumberField.RingOfIntegers F) ∈ w.asIdeal → w ∈ badF) ∧
      ∀ w ∉ badF,
        ιO (((ρ.map (algebraMap ℚ F)).charFrob w).coeff 1) = -ιT (t w) := by
  classical
  -- potential modularity at the given `F`: the seed newform's Hecke algebra
  obtain ⟨H⟩ := nonempty_hilbertHeckeAlgebra_of_moretBaillySeed hℓodd hℓ5 hW
    hρbar hirr F hFtr hFgal hirrF seed
  -- `R_F = T_F`: the lift `ρ|_{G_F}` is a point of that Hecke algebra
  obtain ⟨φ, hφ⟩ := exists_classifyingHom_hilbertHeckeAlgebra hℓodd hℓ5 hZinj
    hrank hρ hW hρbar hirr π hπsurj F hFtr hFgal hirrF badρ hcong H
  haveI := H.charPK
  have hℓne : ((ℓ : ℕ) : NumberField.RingOfIntegers F) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Fact.out (p := ℓ.Prime)).ne_zero
  obtain ⟨badF, hsub, hbadℓ⟩ :=
    exists_finset_superset_of_places_mem H.bad ((ℓ : ℕ) : NumberField.RingOfIntegers F) hℓne
  refine ⟨H.T₀, inferInstance, inferInstance,
    ιO.comp (φ.comp (H.TEquiv.symm.toAlgHom.toRingHom.comp
      (heckeZFormMap ℓ k H.T₀ H.𝔪 H.𝔪_isMaximal))),
    badF, H.heckeT₀, hbadℓ, ?_⟩
  intro w hw
  have hwbad : w ∉ H.bad := fun h => hw (hsub h)
  -- the charpoly compatibility at the arithmetic Frobenius over `w`
  have key : (H.ρT.charFrob w).map φ = (ρ.map (algebraMap ℚ F)).charFrob w :=
    hφ (Field.absoluteGaloisGroup.map (algebraMap F (w.adicCompletion F))
      (Field.AbsoluteGaloisGroup.adicArithFrob w))
  have hc : φ ((H.ρT.charFrob w).coeff 1) =
      ((ρ.map (algebraMap ℚ F)).charFrob w).coeff 1 := by
    rw [← key, Polynomial.coeff_map]
  -- the `ℤ`-form's Hecke operator is the Hecke operator
  have hZ : H.TEquiv.symm (heckeZFormMap ℓ k H.T₀ H.𝔪 H.𝔪_isMaximal (H.heckeT₀ w)) =
      H.heckeT w := by
    rw [← H.heckeT_eq w, H.TEquiv.symm_apply_apply]
  simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
    AlgEquiv.coe_toAlgHom, hZ]
  rw [← hc, H.charFrobT w hwbad, map_neg, map_neg]

/-- **`R = 𝕋` over the totally real base** (sub-leaf (a) of
the modularity-lifting cut — Kisin 2009 / Taylor 2006, the
Taylor–Wiles patching argument over `F`): given the modular seed `σ`
over `F` and the residual congruence `hcong` identifying `ρ|_{G_F}`
and `σ` as lifts of one irreducible residual representation, the lift
`ρ|_{G_F}` is ITSELF modular: away from a finite bad set its Frobenius
characteristic polynomial is the Hecke polynomial
`X² − a_w·X + Nw` of a Hilbert newform, read inside `ℚ̄_ℓ` through a
coefficient embedding `ιO` of the lift's coefficient ring.

RESTATED 2026-07-26 — READ THE FAITHFULNESS REPAIR AT THE END OF THIS
DOCSTRING BEFORE COMPARING WITH ANY OLDER DESCRIPTION.  The conclusion
now carries the three things `R = 𝕋` actually delivers and the old raw
form did not:

* a NUMBER FIELD `E` with an embedding `ψℓ : E ↪ ℚ̄_ℓ` — the Hecke
  field of the attached newform, together with the place of `E` over
  `ℓ` at which its `λ`-adic realization is `ρ|_{G_F}`.  Rationality is
  not a theorem downstream of `R = 𝕋`; it is PART of what `R = 𝕋`
  asserts, because `𝕋` is generated over `ℤ` by the `T_w` and the
  point of `𝕋` cut out by `ρ|_{G_F}` therefore has values in a finite
  extension of `ℚ`.
* a GENUINE level/bad set: `badF` is required to contain every place
  over `ℓ`.  At `w | ℓ` the representation is ramified and
  `charFrob w` is the charpoly of an arbitrarily chosen Frobenius
  LIFT, not a Hecke polynomial — the cyclotomic character is ramified
  there and takes values in an open subgroup of `ℤ_[ℓ]ˣ`, almost all
  of which are transcendental over `ℚ`.  Quantifying the conclusion
  over those places would make it false for the intended objects.
* the EIGENVALUE (trace) datum only.  The constant coefficient needs
  no automorphic input whatever: away from `ℓ` the cyclotomic
  determinant clause of `hρ` forces it to be the rational integer `Nw`
  (`charFrob_baseChange_coeff_zero_eq_absNorm`), and the assembly
  `charFrob_map_eq_heckePolynomial_of_heckeTrace` below reconstructs
  the full Hecke polynomial `X² − a_w·X + Nw` from the trace.  So the
  citation asks for exactly the automorphic content and nothing else.

The coefficient embedding `ιO : O ↪ ℚ̄_ℓ` is now a HYPOTHESIS rather
than part of the conclusion: it is generic commutative algebra
(`exists_injective_ringHom_algebraicClosure_of_moduleFinite` above,
applied by the consumer) and has no business inside a citation of
Kisin–Taylor.

Classically: the seed `σ` is modular (`seed.modular₀`) and residually
`ρbar|_{G_F}` (`seed.residual₀`); by `hcong` the lift `ρ|_{G_F}` has
the same residual representation, and `hirrF` makes it irreducible, so
both are points of one deformation problem — the minimal problem
attached to `ρbar|_{G_F}` with the local conditions imported from
`hρ` (cyclotomic determinant, unramified outside the places over `2`
and `ℓ`, flat at the places over `ℓ`, tame at the places over `2`),
which is the "`S`-good" problem of the FLT blueprint ch. 4 transported
to `F`.  Modularity of the seed makes the corresponding Hecke algebra
`𝕋` nonzero, and the Taylor–Wiles–Kisin patching argument identifies
the universal deformation ring with `𝕋`; the point of `R` given by
`ρ|_{G_F}` is therefore a point of `𝕋`, i.e. a Hilbert newform `f` of
parallel weight `2` over `F`, and Carayol's local-global
compatibility at the places where everything is unramified turns the
eigenvalue system of `f` into the Frobenius characteristic
polynomials above.  The Taylor–Wiles hypothesis
(`ρbar|_{G_{F(ζ_ℓ)}}` absolutely irreducible) is part of the
Moret–Bailly avoidance of leaf (i); its pin-stateable trace `hirrF` is
carried formally, the rest lives in this citation.

Literature: Kisin, *Moduli of finite flat group schemes, and
modularity*, Ann. of Math. 170 (2009), Theorem (0.1) (the totally real
modularity lifting theorem in the flat/low-weight case used here);
Taylor, *On the meromorphic continuation of degree two L-functions*,
Doc. Math. Extra Vol. (2006), Theorem 5.4 (the variant tolerating the
small residual image left by the Moret–Bailly construction); Fujiwara,
*Deformation rings and Hecke algebras in the totally real case*
(1996/2006), and Skinner–Wiles for the earlier totally real `R = 𝕋`;
Taylor's 2018 Stanford course and the FLT blueprint ch. 4 for the
statement form used here; Carayol, Ann. Sci. ÉNS 19 (1986) for the
identification of Frobenius data with Hecke data.

PATCHING NOTE (2026-07-24): see the section audit above — the
project's own Taylor–Wiles machinery (`Patching.lean`) is hard-pinned
to base `ℚ` through `IsHardlyRamified`'s local conditions at the
rational primes `2` and `ℓ`; its commutative-algebra half
(`PatchedModule`, the Auslander–Buchsbaum/depth chain, the
power-series stratum, `TaylorWilesSystem` and its tower) is
base-agnostic and IS the reusable part, so if those pillars are ever
generalized over a totally real base, THIS leaf — not its consumer —
is the natural consumer of the generalization.

SOUNDNESS AUDIT (both ways, 2026-07-24): (i) direct — for the intended
instantiation (`F`, `seed` from `exists_moretBailly_seed_of_five_le`,
`ρ` the KW minimal lift, `hcong` from sub-leaf (c)) this is the MLT
chain above; for an abstract `(F, seed, badρ, hcong)` the
abstract-quantification caveat applies (not every formally admissible
package satisfies the unstated Taylor–Wiles conditions — in
particular absolute irreducibility over `F(ζ_ℓ)` and the local
conditions at the places over `2`), and (ii) collapse — the
hypothesis set (an irreducible hardly ramified mod-`ℓ`
representation, `ℓ ≥ 5`) is classically unsatisfiable (headline
below), so the statement is classically true for every package.

FAITHFULNESS REPAIR (2026-07-26 — THIS IS WHAT THE PRESENT STATEMENT
IS, AND WHY IT IS SORRIED WHERE THE OLD ONE WAS PROVEN).  The node used
to conclude

    ∃ badF aF dF ιO (_ : Injective ιO), ∀ w ∉ badF,
      (charFrob w).map ιO = X² − C (aF w)·X + C (dF w)

with `aF`, `dF` and `badF` all existentially quantified and tied to no
Hecke datum.  That conclusion is derivable from the SHAPE of `charFrob`
alone: `(ρ|_{G_F}).charFrob w` is the characteristic polynomial of an
endomorphism of the free rank-`2` module `Fin 2 → O`, hence monic of
degree `2`, so `aF w := −ιO((charFrob w).coeff 1)`,
`dF w := ιO((charFrob w).coeff 0)` and `badF := ∅` discharged it for
ANY `ρ` whatsoever.  Nothing of Kisin/Taylor/Fujiwara was formalized by
it; every arithmetic hypothesis was underscore-prefixed, unused.

Two separate defects followed, and both are repaired here rather than
downstream:

1. *The rationality was DOUBLE-COUNTED.*  The raw form deferred
   algebraicity of the eigenvalues to a separate "Shimura rationality"
   citation, as if it were a theorem downstream of `R = 𝕋`.  It is not:
   `𝕋` is generated over `ℤ` by the Hecke operators `T_w`, so a point
   of `𝕋` has values in a finite extension of `ℚ` by construction, and
   an honest `R = 𝕋` conclusion already carries the Hecke field.
   Asking for it twice created a leaf nobody could close.
2. *The bad set was `∅`.*  The downstream citations were therefore
   instantiated at EVERY place of `F`, including the places over `2`
   and `ℓ` where `charFrob` is the charpoly of an arbitrary Frobenius
   LIFT of a ramified representation and is classically not algebraic.
   At that instantiation those citations were FALSE for the intended
   objects, and no appeal to Shimura could have discharged them.

Six downstream declarations existed only to manufacture what (a) now
supplies, and were DELETED as part of this repair (the five-node sub-cut
proper, plus its parent `exists_heckeField_of_eigensystem`):
`exists_heckeField_of_eigensystem`,
`exists_heckeField_mem_range_of_eigensystem`,
`exists_heckeSubfield_of_eigenvalues`,
`exists_heckeSubfield_of_determinants` (a vacuous node),
`exists_heckeGenerators_of_eigenvalues` and `isIntegral_heckeEigenvalues`
(both SORRIED leaves with no admissible discharge: the second, in
particular, was asked to prove `IsIntegral ℚ (aF w)` from hypotheses
that pin `aF w` inside `ιO O ⊆ ℚ̄_ℓ`, where integrality over `ℚ_[ℓ]` is
orthogonal to integrality over `ℚ`).  Their disappearance is a fully
successful outcome of the repair, not a loss: they were the symptom.

FORMAL-CONTENT AUDIT of the NEW statement (2026-07-26).  It is NOT
discharged by the shape of `charFrob`, and it has no junk witness:

* `E` must be a `NumberField`, so `Set.range ψℓ` is countable and
  algebraic over `ℚ`, while `ιO(tr ρ(Frob_w))` ranges over `ιO O`,
  which is algebraic over `ℚ_[ℓ]` and generically transcendental over
  `ℚ`.  No choice of `E`, `ψℓ`, `a` discharges the trace clause for an
  arbitrary `ρ`.
* `badF` is a `Finset`, so the clause cannot be evaded by declaring
  every place bad; the assertion is genuinely about cofinitely many
  places.
* Consequently every hypothesis is retained WITHOUT an underscore, and
  the classical content — modularity of the seed, the residual
  congruence, the Taylor–Wiles conditions carried by `hρ`/`hirrF` — is
  what a discharge must consume.  Route (ii) (collapse: the hypothesis
  package is classically unsatisfiable at `ℓ ≥ 5`, this module's
  headline) remains available as before.

ASSEMBLY (2026-07-26 — THIS NODE IS NO LONGER A SORRY NODE).  It is now
a two-line assembly over the cut immediately above:

* `exists_heckeTraceAlgebra_of_congruentSeed` (PROVEN 2026-07-27 as an
  assembly over `nonempty_hilbertHeckeAlgebra_of_moretBaillySeed` and
  `exists_classifyingHom_hilbertHeckeAlgebra`, the two SORRY leaves that now
  carry the citation between them)
  produces the Hecke algebra `T`, **module-finite over `ℤ`**, its
  embedding `ιT : T ↪ ℚ̄_ℓ`, the level `badF ⊇ {w ∣ ℓ}`, and the Hecke
  operators whose images are the Frobenius traces;
* `exists_numberField_ringHom_of_moduleFinite_int` (PROVEN) turns
  `ℤ`-module-finiteness into a number field `E`, the place `ψℓ`, and the
  `E`-valued `a`.

The split is exactly the sentence of the FAITHFULNESS REPAIR above —
"`𝕋` is generated over `ℤ` by the Hecke operators, so a point of `𝕋` has
values in a finite extension of `ℚ` by construction" — made mechanical.
Note it is NOT a revival of the deleted Carayol/Shimura sub-cut: see the
paragraph WHY THIS IS NOT THE DELETED `isIntegral_heckeEigenvalues` on
the brick, whose hypothesis is finiteness over `ℤ` where the deleted node
had only finiteness over `ℤ_[ℓ]`.

MISSING MACHINERY, in dependency order, for a discharge along route
(i) — PARTIALLY STALE AS WRITTEN, CORRECTED 2026-07-26: (1) Hilbert
modular forms of parallel weight `2` over a totally real field; (2) the
Hecke operators `T_w` and the Hecke algebra of a given level, acting on a
finite-dimensional space of cusp forms with a `ℚ`-rational structure —
which is exactly what makes the eigensystem number-field-valued and is
the reason `E` belongs in THIS conclusion; (3) Carayol/Taylor attachment
of `λ`-adic representations with local-global compatibility; (4) the
Taylor–Wiles–Kisin patching argument over `F`, i.e. `R = 𝕋` proper.

The claim that the tree has none of (1)–(4) is true of the MATHLIB PIN
(`grep Hilbert` over `Mathlib/NumberTheory/`: only Hilbert's theorem 90
and Hilbert basis) and of `~/cs/FLT`, but it is FALSE of this project:
`HardlyRamified/HilbertModularity.lean` — in this module's import cone
through `HardlyRamified/Deformation.lean` — carries (4) as
`exists_heckeAlgebra_algEquiv_of_isWeaklyUniversal` (PROVEN over its own
leaves) and (2) in abstract `ℤ_[ℓ]` form as `HilbertHeckeAlgebra`.  The
first of the two obstructions that used to remain — the absent `ℚ`-rational
structure of the Hecke algebra — is GONE, supplied by `HilbertHeckeAlgebra`'s
`T₀`/`heckeT₀`/`heckeT_eq` fields and consumed by
`exists_heckeTraceAlgebra_of_congruentSeed`'s assembly above.  The second —
the SPLITTING CONDITION AT `2` that the `F`-level deformation category needs
and the Moret–Bailly geometric chain does not produce — survives, and it now
sits on exactly one leaf, `exists_classifyingHom_hilbertHeckeAlgebra`, whose
docstring states it with its refuting check.  Anyone attacking this cluster
should read that leaf and the ROUTE AUDIT above it FIRST; note in particular
that the audit's 2026-07-26 SECOND PASS retracts the earlier "re-plumb `F`
from `PotentialHeckeDatum`" diagnosis, which is not possible (the conclusion
is about the places of the `F` that is handed in) and was not the repair.

CIRCULARITY GUARD (inherited from pillar β, load-bearing): no
discharge through `Family.lean`, `Lift.lean`, or
`Modularity/Interface.lean`. -/
theorem exists_heckeEigensystem_of_congruentSeed
    {ℓ : ℕ} (hℓodd : Odd ℓ) [Fact ℓ.Prime] (hℓ5 : 5 ≤ ℓ)
    {O : Type u} [CommRing O] [IsDomain O] [TopologicalSpace O]
    [IsTopologicalRing O] [Algebra ℤ_[ℓ] O] [IsLocalRing O]
    [Module.Finite ℤ_[ℓ] O] [IsModuleTopology ℤ_[ℓ] O]
    (hZinj : Function.Injective (algebraMap ℤ_[ℓ] O))
    {ρ : GaloisRep ℚ O (Fin 2 → O)}
    (hrank : Module.rank O (Fin 2 → O) = 2)
    (hρ : IsHardlyRamified hℓodd hrank ρ)
    {k : Type u} [Field k] [Finite k] [Algebra ℤ_[ℓ] k]
    [TopologicalSpace k] [DiscreteTopology k]
    {W : Type v} [AddCommGroup W] [Module k W] [Module.Finite k W]
    [Module.Free k W]
    (hW : Module.rank k W = 2) {ρbar : GaloisRep ℚ k W}
    (hρbar : IsHardlyRamified hℓodd hW ρbar)
    (hirr : ρbar.IsIrreducible)
    (π : O →+* k) (hπsurj : Function.Surjective π)
    (hπ : ∀ (q : ℕ) (hq : q.Prime), q ≠ 2 → q ≠ ℓ →
      (ρ.charFrob hq.toHeightOneSpectrumRingOfIntegersRat).map π =
        ρbar.charFrob hq.toHeightOneSpectrumRingOfIntegersRat)
    (F : Type u) [Field F] [NumberField F]
    (hFtr : NumberField.IsTotallyReal F) (hFgal : IsGalois ℚ F)
    (hirrF : (ρbar.map (algebraMap ℚ F)).IsIrreducible)
    (seed : MoretBaillySeed ℓ F (ρbar.map (algebraMap ℚ F)))
    (badρ : Finset (HeightOneSpectrum (NumberField.RingOfIntegers F)))
    (hcong : ∀ w ∉ badρ,
      ((ρ.map (algebraMap ℚ F)).charFrob w).map π =
        (ρbar.map (algebraMap ℚ F)).charFrob w)
    (ιO : O →+* AlgebraicClosure ℚ_[ℓ]) (hιO : Function.Injective ιO) :
    ∃ (E : Type u) (_ : Field E) (_ : NumberField E)
      (ψℓ : E →+* AlgebraicClosure ℚ_[ℓ])
      (badF : Finset (HeightOneSpectrum (NumberField.RingOfIntegers F)))
      (a : HeightOneSpectrum (NumberField.RingOfIntegers F) → E),
      (∀ w : HeightOneSpectrum (NumberField.RingOfIntegers F),
          (ℓ : NumberField.RingOfIntegers F) ∈ w.asIdeal → w ∈ badF) ∧
      ∀ w ∉ badF,
        ιO (((ρ.map (algebraMap ℚ F)).charFrob w).coeff 1) = -ψℓ (a w) := by
  -- the automorphic half: the Hecke algebra, module-finite over `ℤ`
  obtain ⟨T, iT, hTfin, ιT, badF, t, hbadℓ, htr⟩ :=
    exists_heckeTraceAlgebra_of_congruentSeed hℓodd hℓ5 hZinj hrank hρ hW hρbar
      hirr π hπsurj hπ F hFtr hFgal hirrF seed badρ hcong ιO hιO
  letI : CommRing T := iT
  haveI : Module.Finite ℤ T := hTfin
  -- the commutative-algebra half: its image lies in a number field
  obtain ⟨E, iE, hNE, ψℓ, g, hg⟩ :=
    exists_numberField_ringHom_of_moduleFinite_int (ℓ := ℓ) T ιT
  refine ⟨E, iE, hNE, ψℓ, badF, fun w => g (t w), hbadℓ, fun w hw => ?_⟩
  rw [htr w hw, hg (t w)]

/-! ### The Carayol/Shimura sub-cut — RETIRED 2026-07-26

This section used to carry a five-node sub-cut of sub-leaf (b):
`exists_heckeField_mem_range_of_eigensystem`,
`exists_heckeSubfield_of_eigenvalues`,
`exists_heckeSubfield_of_determinants`,
`exists_heckeGenerators_of_eigenvalues` and `isIntegral_heckeEigenvalues`.
All five have been DELETED, together with their parent
`exists_heckeField_of_eigensystem`, and the reason is recorded in full in
the FAITHFULNESS REPAIR paragraph of
`exists_heckeEigensystem_of_congruentSeed` above.  In short: they existed
to recover, downstream of `R = 𝕋`, the rationality that `R = 𝕋` already
delivers — `𝕋` is generated over `ℤ` by the `T_w` — and they were being
handed `badF := ∅`, i.e. an instantiation at which the ramified places
were included and the statements were classically FALSE for the intended
objects.  Two of them were sorried leaves with no admissible discharge.

Do not re-cut along that seam.  Three separate owners worked the three
downstream leaves and two independently reached the same diagnosis: the
leaves are not hard, they are STARVED, and the repair belongs one node
upstream.  In particular the (b-i-a) split recorded here as "strictly
stronger than the parent, since it also names the generators" was NOT a
strengthening: `𝔥.FG`, the conjunction of the two sub-leaves, and the
parent's own conclusion are all three EQUIVALENT (the last direction via
`IntermediateField.essFiniteType_iff`).  That claim appeared twice in this
module's prose and both copies were wrong; both are removed with the
nodes they described.

What SURVIVES of the sub-cut, because it is genuine algebraic number
theory and carries no automorphic input, is the DETERMINANT half:

* `cyclotomicCharacter_adicArithFrob_base_eq_absNorm` — at a place `w ∤ ℓ`
  of `F` the `ℓ`-adic cyclotomic character takes the value `Nw` on the
  global image of the arithmetic Frobenius at `w` (PROVEN, over the
  roots-of-unity brick `adicArithFrob_rootsOfUnity_pow_base` below);
* `charFrob_baseChange_coeff_zero_eq_absNorm` — hence the constant
  coefficient of the base-changed Frobenius charpoly is the rational
  integer `Nw` (PROVEN);
* `charFrob_map_eq_heckePolynomial_of_heckeTrace` — hence the full Hecke
  polynomial `X² − a_w·X + Nw` over the Hecke field is reconstructed from
  the TRACE datum alone (PROVEN).

So the modularity-lifting cut now rests on exactly one citation,
`exists_heckeEigensystem_of_congruentSeed`, which is the `R = 𝕋` theorem
itself and nothing else.
-/

set_option backward.isDefEq.respectTransparency false in
/-- **The arithmetic Frobenius at a place `w ∤ ℓ` of the base `F` raises
`ℓ`-power roots of unity to the `Nw`-th power** (PROVEN; the
roots-of-unity input of sub-leaf (b-ii)): for a root of unity `t` of
`ℓ`-power order in `ℚᵃˡᵍ`, the image in `G_ℚ` of the arithmetic
Frobenius at `w` — pushed down the tower `G_{F_w} → G_F → G_ℚ` — sends
`t` to `t ^ Nw`, with `Nw = ‖w‖` the absolute norm.

This is the `F`-analogue of `adicArithFrob_rootsOfUnity_pow_of_ne`
later in this module (the rational-prime case, where the exponent is
the prime `q` itself).  Two things differ, and only two:

* the descent runs down TWO steps rather than one — `Γ F_w → Γ F` and
  then `Γ F → Γ ℚ` — each discharged by
  `Field.absoluteGaloisGroup.lift_map` against the injectivity of the
  corresponding `AlgebraicClosure.map`;
* the exponent of the `IsArithFrobAt` specification is the residue
  cardinality at `w`, which is `Nw` by
  `IsDedekindDomain.HeightOneSpectrum.natCard_under_maximalIdeal`
  (`CompletionTransport.lean`) composed with
  `Ideal.absNorm_apply`/`Submodule.cardQuot_apply`.  In the rational
  case this bookkeeping is `natCard_residue_quotient_toHeightOneSpectrum`.

The hypothesis `hwℓ` enters exactly once, and essentially: it is what
makes `ℓ` — hence `ℓⁿ` — a unit in the completed integers at `w`, which
is the side condition of `AlgHom.IsArithFrobAt.apply_of_pow_eq_one`.
Here it is used through the `LiesOver` instance identifying `w.asIdeal`
with the contraction of the maximal ideal of `𝒪_w`, which is cleaner
than the rational route's valuation computation. -/
theorem adicArithFrob_rootsOfUnity_pow_base
    {ℓ : ℕ} [hℓ : Fact ℓ.Prime] (F : Type u) [Field F] [NumberField F]
    (w : HeightOneSpectrum (NumberField.RingOfIntegers F))
    (hwℓ : (ℓ : NumberField.RingOfIntegers F) ∉ w.asIdeal) (n : ℕ) :
    ∀ t ∈ rootsOfUnity (ℓ ^ n) (AlgebraicClosure ℚ),
      ((Field.absoluteGaloisGroup.map (algebraMap ℚ F)
        (Field.absoluteGaloisGroup.map
          (algebraMap F (HeightOneSpectrum.adicCompletion F w))
          (Field.AbsoluteGaloisGroup.adicArithFrob w))).toRingEquiv) t =
        t ^ ((Ideal.absNorm w.asIdeal : ZMod (ℓ ^ n)).val) := by
  intro t ht
  classical
  set g : ℚ →+* F := algebraMap ℚ F with hgdef
  set h : F →+* HeightOneSpectrum.adicCompletion F w :=
    algebraMap F (HeightOneSpectrum.adicCompletion F w) with hhdef
  -- the residue cardinality of the `IsArithFrobAt` specification at `w` is `Nw`
  have hcard : Nat.card (↥(w.adicCompletionIntegers F) ⧸
      (IsLocalRing.maximalIdeal (IntegralClosure ↥(w.adicCompletionIntegers F)
        (AlgebraicClosure (w.adicCompletion F)))).under ↥(w.adicCompletionIntegers F)) =
      Ideal.absNorm w.asIdeal := by
    rw [IsDedekindDomain.HeightOneSpectrum.natCard_under_maximalIdeal w,
      Ideal.absNorm_apply, Submodule.cardQuot_apply]
  -- the root of unity and its images down the tower `ℚᵃˡᵍ → Fᵃˡᵍ → F_wᵃˡᵍ`
  have htL : ((t : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ) ^ (ℓ ^ n) = 1 := by
    have h1 := (mem_rootsOfUnity _ _).mp ht
    calc ((t : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ) ^ (ℓ ^ n)
        = ((t ^ (ℓ ^ n) : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ) := by
          push_cast; rfl
      _ = 1 := by rw [h1]; rfl
  set u : AlgebraicClosure F :=
    AlgebraicClosure.map g ((t : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ) with hudef
  have hupow : u ^ (ℓ ^ n) = 1 := by rw [hudef, ← map_pow, htL, map_one]
  set ζ : AlgebraicClosure (HeightOneSpectrum.adicCompletion F w) :=
    AlgebraicClosure.map h u with hζdef
  have hζpow : ζ ^ (ℓ ^ n) = 1 := by rw [hζdef, ← map_pow, hupow, map_one]
  -- `ζ` is integral over the completed integers (it kills `X^{ℓⁿ} - 1`)
  have hint : IsIntegral (w.adicCompletionIntegers F) ζ := by
    refine ⟨Polynomial.X ^ (ℓ ^ n) - 1, ?_, ?_⟩
    · have := Polynomial.monic_X_pow_sub_C
        (R := w.adicCompletionIntegers F) (1 : _) (n := ℓ ^ n)
        (pow_ne_zero _ hℓ.out.pos.ne')
      simpa [Polynomial.C_1] using this
    · simp [Polynomial.eval₂_sub, hζpow]
  set ζ' : IntegralClosure (w.adicCompletionIntegers F)
      (AlgebraicClosure (HeightOneSpectrum.adicCompletion F w)) := ⟨ζ, hint⟩ with hζ'def
  have hζ'pow : ζ' ^ (ℓ ^ n) = 1 := by
    apply Subtype.ext
    push_cast [hζ'def]
    exact hζpow
  -- `ℓ` is a unit at `w` (`w ∤ ℓ`), so `ℓⁿ` avoids the maximal ideal upstairs
  have hpnotin : ((ℓ : ℕ) ^ n : IntegralClosure (w.adicCompletionIntegers F)
      (AlgebraicClosure (HeightOneSpectrum.adicCompletion F w))) ∉
      IsLocalRing.maximalIdeal _ := by
    have hunit : IsUnit ((ℓ : ℕ) : w.adicCompletionIntegers F) := by
      by_contra hnu
      refine hwℓ ?_
      have hover : w.asIdeal =
          (HeightOneSpectrum.completionIdeal F w).under
            (NumberField.RingOfIntegers F) := Ideal.LiesOver.over
      rw [hover, Ideal.under_def, Ideal.mem_comap]
      show algebraMap (NumberField.RingOfIntegers F) (w.adicCompletionIntegers F)
        ((ℓ : ℕ) : NumberField.RingOfIntegers F) ∈ _
      rw [map_natCast]
      exact (IsLocalRing.mem_maximalIdeal _).mpr (mem_nonunits_iff.mpr hnu)
    have hunitIC : IsUnit (((ℓ : ℕ) ^ n) : IntegralClosure (w.adicCompletionIntegers F)
        (AlgebraicClosure (HeightOneSpectrum.adicCompletion F w))) := by
      have h1 := hunit.map (algebraMap (w.adicCompletionIntegers F)
        (IntegralClosure (w.adicCompletionIntegers F)
          (AlgebraicClosure (HeightOneSpectrum.adicCompletion F w))))
      rw [map_natCast] at h1
      exact h1.pow n
    intro hmem
    exact ((IsLocalRing.mem_maximalIdeal _).mp hmem) hunitIC
  -- the Frobenius specification at `w`, read in `F_wᵃˡᵍ`
  have hfrob := AlgHom.IsArithFrobAt.apply_of_pow_eq_one
    (Field.AbsoluteGaloisGroup.isArithFrobAt_adicArithFrob (v := w))
    hζ'pow (by exact_mod_cast hpnotin)
  rw [hcard] at hfrob
  have hfrobK : Field.AbsoluteGaloisGroup.adicArithFrob w ζ =
      ζ ^ Ideal.absNorm w.asIdeal := by
    have h1 := hfrob
    rw [MulSemiringAction.toAlgHom_apply] at h1
    have h2 := congrArg Subtype.val h1
    rw [IntegralClosure.coe_smul] at h2
    have h3 : ((⟨ζ, hint⟩ : IntegralClosure _ _) ^ Ideal.absNorm w.asIdeal).1 =
        ζ ^ Ideal.absNorm w.asIdeal := SubmonoidClass.coe_pow _ _
    simpa [hζ'def, AlgEquiv.smul_def] using h2.trans h3
  -- descend one step: the value at `u ∈ Fᵃˡᵍ` of the image in `Γ F`
  have hstepF : (Field.absoluteGaloisGroup.map h
      (Field.AbsoluteGaloisGroup.adicArithFrob w)) u = u ^ Ideal.absNorm w.asIdeal := by
    apply (AlgebraicClosure.map h).injective
    rw [Field.absoluteGaloisGroup.lift_map h
      (Field.AbsoluteGaloisGroup.adicArithFrob w) u, map_pow]
    exact hfrobK
  -- descend the second step: the value at `t ∈ ℚᵃˡᵍ` of the image in `Γ ℚ`
  have hmain : (Field.absoluteGaloisGroup.map g
      (Field.absoluteGaloisGroup.map h (Field.AbsoluteGaloisGroup.adicArithFrob w)))
      ((t : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ) =
      ((t : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ) ^ Ideal.absNorm w.asIdeal := by
    apply (AlgebraicClosure.map g).injective
    rw [Field.absoluteGaloisGroup.lift_map g
      (Field.absoluteGaloisGroup.map h (Field.AbsoluteGaloisGroup.adicArithFrob w))
      ((t : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ), map_pow]
    exact hstepF
  show (Field.absoluteGaloisGroup.map g
      (Field.absoluteGaloisGroup.map h (Field.AbsoluteGaloisGroup.adicArithFrob w)))
      ((t : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ) = _
  rw [hmain]
  -- the exponent-mod juggle: `t^Nw = t^(Nw mod ℓⁿ)` since `t^{ℓⁿ} = 1`
  haveI : NeZero (ℓ ^ n) := ⟨pow_ne_zero _ hℓ.out.pos.ne'⟩
  have hval : ((Ideal.absNorm w.asIdeal : ZMod (ℓ ^ n))).val =
      Ideal.absNorm w.asIdeal % ℓ ^ n := ZMod.val_natCast _ _
  conv_lhs => rw [show Ideal.absNorm w.asIdeal =
    ℓ ^ n * (Ideal.absNorm w.asIdeal / ℓ ^ n) + Ideal.absNorm w.asIdeal % ℓ ^ n from
    (Nat.div_add_mod _ (ℓ ^ n)).symm]
  rw [pow_add, pow_mul, htL, one_pow, one_mul, hval]

/-- **The `ℓ`-adic cyclotomic character at a Frobenius of the base `F`**
(PROVEN 2026-07-25; sub-leaf (b-ii) of the Carayol/Shimura sub-cut — pure
algebraic number theory, NO automorphic content): at a place `w` of a
number field `F` which does not lie over `ℓ`, the `ℓ`-adic cyclotomic
character of `G_ℚ` takes the value `Nw = ‖w‖` (the absolute norm of
`w`, i.e. the cardinality of its residue field) on the global image of
the arithmetic Frobenius at `w`.

Classically this is the unramifiedness of the cyclotomic character away
from `ℓ` together with `Frob_w(ζ) = ζ^{Nw}` for every root of unity of
`ℓ`-power order (Serre, *Abelian ℓ-adic Representations*, I.1;
Neukirch, *Algebraic Number Theory*, IV): the residue field at `w` has
`Nw` elements, so the arithmetic Frobenius acts on the `ℓ`-power roots
of unity — which are `w`-integral units, `w ∤ ℓ` — by `Nw`-th powering,
and `ℓ`-adic continuity upgrades the congruences mod `ℓⁿ` to the
identity in `ℤ_[ℓ]`.

DISCHARGE (2026-07-25, CARRIED OUT — the route recommended by the
previous owner worked verbatim): this is the exact `F`-analogue of the
PROVEN rational-prime lemma
`cyclotomicCharacter_adicArithFrob_eq_natCast` later in this module
(with `q` replaced by the residue cardinality `Nw`).  The proof runs:
`PadicInt.ext_of_toZModPow` to reduce to level `ℓⁿ`,
`cyclotomicCharacter.toZModPow` plus `modularCyclotomicCharacter.unique`
to identify the value with the exponent of the Frobenius action on
`μ_{ℓⁿ}`, and `AlgHom.IsArithFrobAt.apply_of_pow_eq_one` for that
action — the last step needing `ℓ` to be a unit in the local integers
at `w`, which is exactly `hwℓ`, and the residue cardinality identity
`Nat.card (𝓞_F ⧸ w) = Ideal.absNorm w.asIdeal` (mathlib's
`Ideal.absNorm_apply`/`Submodule.cardQuot`).  Only the residue-field
cardinality bookkeeping differs from the rational case, where it is
`natCard_residue_quotient_toHeightOneSpectrum`; here it is
`IsDedekindDomain.HeightOneSpectrum.natCard_under_maximalIdeal`
(`CompletionTransport.lean`), which already states the general-number-field
form, so no new residue-cardinality theory was needed.

The roots-of-unity input is the immediately preceding
`adicArithFrob_rootsOfUnity_pow_base`; the only structural difference
from the rational case is that the Frobenius descends down TWO steps,
`Γ F_w → Γ F → Γ ℚ`, each handled by
`Field.absoluteGaloisGroup.lift_map` against injectivity of
`AlgebraicClosure.map`.  No functoriality lemma for
`Field.absoluteGaloisGroup.map` along a composite was needed (and none
exists — `map` depends on an arbitrarily chosen embedding of algebraic
closures, so a `map_comp` equation is not available); descending one
step at a time avoids the question entirely.

SOUNDNESS AUDIT (2026-07-25): this statement is TRUE OUTRIGHT — no
vacuity route is used and no abstract-quantification caveat applies: it
quantifies over an arbitrary number field `F` and an arbitrary place
`w ∤ ℓ`, with no Galois-representation data at all.  It is therefore
the one part of sub-leaf (b) that a future contributor can discharge
without any automorphic input.

CIRCULARITY GUARD (inherited from pillar β, load-bearing): no
discharge through `Family.lean`, `Lift.lean`, or
`Modularity/Interface.lean`. -/
theorem cyclotomicCharacter_adicArithFrob_base_eq_absNorm
    {ℓ : ℕ} [Fact ℓ.Prime] (F : Type u) [Field F] [NumberField F]
    (w : HeightOneSpectrum (NumberField.RingOfIntegers F))
    (hwℓ : (ℓ : NumberField.RingOfIntegers F) ∉ w.asIdeal) :
    ((cyclotomicCharacter (AlgebraicClosure ℚ) ℓ
      ((Field.absoluteGaloisGroup.map (algebraMap ℚ F)
        (Field.absoluteGaloisGroup.map
          (algebraMap F (HeightOneSpectrum.adicCompletion F w))
          (Field.AbsoluteGaloisGroup.adicArithFrob w))).toRingEquiv) :
        ℤ_[ℓ]ˣ) : ℤ_[ℓ]) = (Ideal.absNorm w.asIdeal : ℤ_[ℓ]) := by
  rw [← PadicInt.ext_of_toZModPow]
  intro n
  rw [map_natCast, cyclotomicCharacter.toZModPow]
  exact (modularCyclotomicCharacter.unique
    (hn := HasEnoughRootsOfUnity.natCard_rootsOfUnity (AlgebraicClosure ℚ) (ℓ ^ n))
    _ _ (adicArithFrob_rootsOfUnity_pow_base F w hwℓ n)).symm

/-- **The determinant coefficient of the base-changed Frobenius charpoly
is `Nw`** (PROVEN from the cyclotomic leaf above; the `d`-half of the
Carayol/Shimura sub-cut): for a hardly ramified `ρ` on a rank-`2`
module and a place `w` of the base `F` not lying over `ℓ`, the constant
coefficient of the Frobenius characteristic polynomial of `ρ|_{G_F}` at
`w` is the rational integer `Nw`.

Proof: for a rank-`2` charpoly `det = (-1)² · coeff 0`
(`LinearMap.det_eq_sign_charpoly_coeff`); the base-changed local
Frobenius is, by the two `rfl`-lemmas `GaloisRep.toLocal_apply` and
`GaloisRep.map_apply`, the element of `G_ℚ` obtained by pushing the
arithmetic Frobenius at `w` through `G_{F_w} → G_F → G_ℚ`, so its
determinant is the cyclotomic-character value by
`IsHardlyRamified.det`; and that value is `Nw` by
`cyclotomicCharacter_adicArithFrob_base_eq_absNorm`.

This is the `F`-analogue of the PROVEN rational-prime lemma
`charFrob_coeff_zero_eq_natCast_of_isHardlyRamified` later in this
module, and it is what makes the DETERMINANT half of sub-leaf (b)
free of automorphic input: away from `ℓ` the constant coefficient is a
rational integer, hence lies in every number field. -/
theorem charFrob_baseChange_coeff_zero_eq_absNorm {ℓ : ℕ}
    (hℓodd : Odd ℓ) [Fact ℓ.Prime]
    {O : Type u} [CommRing O] [TopologicalSpace O] [IsTopologicalRing O]
    [IsLocalRing O] [Algebra ℤ_[ℓ] O]
    {ρ : GaloisRep ℚ O (Fin 2 → O)}
    (hrank : Module.rank O (Fin 2 → O) = 2)
    (hρ : IsHardlyRamified hℓodd hrank ρ)
    (F : Type u) [Field F] [NumberField F]
    (w : HeightOneSpectrum (NumberField.RingOfIntegers F))
    (hwℓ : (ℓ : NumberField.RingOfIntegers F) ∉ w.asIdeal) :
    ((ρ.map (algebraMap ℚ F)).charFrob w).coeff 0 =
      (Ideal.absNorm w.asIdeal : O) := by
  have hfinrank : Module.finrank O (Fin 2 → O) = 2 :=
    Module.finrank_eq_of_rank_eq hrank
  -- the constant coefficient of a rank-`2` charpoly is the determinant
  have hdet := LinearMap.det_eq_sign_charpoly_coeff
    ((ρ.map (algebraMap ℚ F)).toLocal w
      (Field.AbsoluteGaloisGroup.adicArithFrob w))
  rw [hfinrank, neg_one_sq, one_mul] at hdet
  -- the cyclotomic determinant of `ρ` at the global image of `Frob_w`
  have hcyclo := hρ.det (Field.absoluteGaloisGroup.map (algebraMap ℚ F)
    (Field.absoluteGaloisGroup.map
      (algebraMap F (HeightOneSpectrum.adicCompletion F w))
      (Field.AbsoluteGaloisGroup.adicArithFrob w)))
  rw [GaloisRep.det_apply,
    cyclotomicCharacter_adicArithFrob_base_eq_absNorm F w hwℓ,
    map_natCast] at hcyclo
  -- the base-changed local Frobenius IS that global element
  have hdetw : LinearMap.det ((ρ.map (algebraMap ℚ F)).toLocal w
      (Field.AbsoluteGaloisGroup.adicArithFrob w)) =
      (Ideal.absNorm w.asIdeal : O) := by
    rw [GaloisRep.toLocal_apply, GaloisRep.map_apply]
    exact hcyclo
  rw [show (ρ.map (algebraMap ℚ F)).charFrob w =
      ((ρ.map (algebraMap ℚ F)).toLocal w
        (Field.AbsoluteGaloisGroup.adicArithFrob w)).charpoly from rfl,
    ← hdet, hdetw]

/-- **The Hecke polynomial from the Hecke trace** (PROVEN 2026-07-26;
sub-leaf (b) of the modularity-lifting cut, and ALL that survives of the
old Carayol/Shimura sub-cut — see the retired-section note above): given
the `E`-valued eigenvalue (trace) datum that `R = 𝕋` supplies, together
with the fact that the places over `ℓ` are bad, the Frobenius
characteristic polynomial of `ρ|_{G_F}` at every good place IS the Hecke
polynomial

    `X² − a_w·X + Nw`

of a Hilbert newform, read inside `ℚ̄_ℓ` through `ιO` on the left and
`ψℓ` on the right.

This node carries NO automorphic input.  Everything it adds to the trace
datum is algebraic number theory already proven in this module:

* `charFrob_map_eq_quadratic_of_rank_two` — `charFrob w` is the charpoly
  of an endomorphism of the free rank-`2` module `Fin 2 → O`, hence monic
  of degree `2`, so its `ιO`-image is
  `X² − C(−ιO(coeff 1))·X + C(ιO(coeff 0))`;
* `charFrob_baseChange_coeff_zero_eq_absNorm` — at `w ∤ ℓ` the cyclotomic
  determinant clause of `hρ` forces `coeff 0 = Nw`, a RATIONAL INTEGER,
  which therefore lies in `ψℓ(E)` for free.  This is where `hbadℓ` is
  consumed, and it is the only place it is needed: at `w | ℓ` the
  cyclotomic character is ramified and the constant coefficient is the
  cyclotomic value of an arbitrarily chosen Frobenius lift — a generic
  element of `ℤ_[ℓ]ˣ`, transcendental over `ℚ` and lying in no finite
  extension of it.

WHY IT IS SPLIT OFF FROM THE CITATION.  The trace and the determinant of
a rank-`2` Frobenius have completely different statuses: only the trace
carries automorphic content.  Keeping them apart is what lets
`exists_heckeEigensystem_of_congruentSeed` ask for exactly the Hecke
eigenvalue and nothing else — the same trace/determinant split this
module already makes at every stage of the solvable descent tower
(`heckeSystemDescendsTo_of_prime_cyclic_step`).

REPLACES `exists_heckeField_of_eigensystem` (deleted 2026-07-26).  That
node had to CONSTRUCT the Hecke field and the `E`-valued functions by
choice out of a "Shimura rationality" citation, because the raw form of
`R = 𝕋` above it produced neither.  Both are now produced upstream, where
`R = 𝕋` produces them classically, so nothing here is existential and
nothing here is a citation. -/
theorem charFrob_map_eq_heckePolynomial_of_heckeTrace
    {ℓ : ℕ} (hℓodd : Odd ℓ) [Fact ℓ.Prime]
    {O : Type u} [CommRing O] [TopologicalSpace O] [IsTopologicalRing O]
    [IsLocalRing O] [Algebra ℤ_[ℓ] O]
    {ρ : GaloisRep ℚ O (Fin 2 → O)}
    (hrank : Module.rank O (Fin 2 → O) = 2)
    (hρ : IsHardlyRamified hℓodd hrank ρ)
    (F : Type u) [Field F] [NumberField F]
    {E : Type u} [Field E] (ψℓ : E →+* AlgebraicClosure ℚ_[ℓ])
    (badF : Finset (HeightOneSpectrum (NumberField.RingOfIntegers F)))
    (a : HeightOneSpectrum (NumberField.RingOfIntegers F) → E)
    (ιO : O →+* AlgebraicClosure ℚ_[ℓ])
    (hbadℓ : ∀ w : HeightOneSpectrum (NumberField.RingOfIntegers F),
      (ℓ : NumberField.RingOfIntegers F) ∈ w.asIdeal → w ∈ badF)
    (htr : ∀ w ∉ badF,
      ιO (((ρ.map (algebraMap ℚ F)).charFrob w).coeff 1) = -ψℓ (a w)) :
    ∀ w ∉ badF,
      ((ρ.map (algebraMap ℚ F)).charFrob w).map ιO =
        (X ^ 2 - C (a w) * X + C ((Ideal.absNorm w.asIdeal : E))).map ψℓ := by
  intro w hw
  have hwℓ : (ℓ : NumberField.RingOfIntegers F) ∉ w.asIdeal := fun h => hw (hbadℓ w h)
  rw [charFrob_map_eq_quadratic_of_rank_two w (ρ.map (algebraMap ℚ F)) hrank ιO,
    htr w hw, charFrob_baseChange_coeff_zero_eq_absNorm hℓodd hrank hρ F w hwℓ]
  simp [Polynomial.map_add, Polynomial.map_sub, Polynomial.map_mul,
    Polynomial.map_pow, map_natCast]

/-- **Modularity lifting over the totally real base** (PROVEN
2026-07-24 as an assembly over the three sub-leaves of the
modularity-lifting cut — see the section note above and the ASSEMBLY
paragraph at the end of this docstring; the depth now lives in
`exists_residualCongruence_over_base`,
`exists_heckeEigensystem_of_congruentSeed` and
`charFrob_map_eq_heckePolynomial_of_heckeTrace`): over the Moret–Bailly base
`F`, the Khare–Wintenberger lift `ρ|_{G_F}` is itself modular — its
Frobenius characteristic polynomials away from a finite bad set are
the Hecke polynomials of a Hilbert newform, recorded through a number
field `E`, embeddings `ψℓ`, `ιO` into `ℚ̄_ℓ`, and the matching clause
that becomes the carrier's `modularF`.

Classically: the seed `σ` is modular (`seed.modular₀`) and residually
congruent to `ρbar|_{G_F}` (`seed.residual₀`); `ρ|_{G_F}` is a lift
of the same residual representation (`hπ`, transported to `F`-places
by Chebotarev — the mod-`ℓ` semisimplifications over `G_F` agree by
Brauer–Nesbitt, and `hirrF` upgrades agreement to conjugacy); `ρ` is
flat at `ℓ` with cyclotomic determinant and is unramified outside
`{2, ℓ}` (`hρ`, restricted to `G_F`), matching the weight-`2` minimal
flat deformation condition. The modularity lifting theorem over
totally real fields (Kisin, *Moduli of finite flat group schemes, and
modularity*, Ann. of Math. 170 (2009); Taylor, *On the meromorphic
continuation of degree two L-functions*, Doc. Math. (2006), for the
technical variants at small residual image; Taylor's 2018 Stanford
course and the FLT blueprint ch. 4 for the statement form used here)
concludes that `ρ|_{G_F}` arises from a Hilbert newform `f` of
parallel weight `2` over `F`; `E` is the Hecke field of `f`
(Shimura), and Carayol's local-global compatibility at unramified
places identifies `charFrob` with the Hecke polynomials inside
`ℚ̄_ℓ`. The Taylor–Wiles hypothesis `ρbar|_{G_{F(ζ_ℓ)}}` absolutely
irreducible is part of the Moret–Bailly avoidance (leaf (i)); its
pin-stateable trace `hirrF` is carried formally, the rest lives in
this citation (abstract-quantification caveat below).

SOUNDNESS AUDIT (both ways, 2026-07-24): (i) direct — for the
intended instantiation (`F` and `seed` produced by
`exists_moretBailly_seed_of_five_le`, `ρ` the KW minimal lift) this
is the MLT chain above; for an abstract `(F, seed)` the
abstract-quantification caveat applies (not every formally admissible
`F` satisfies the unstated Taylor–Wiles conditions), and (ii)
collapse — the hypothesis set (an irreducible hardly ramified
mod-`ℓ` representation, `ℓ ≥ 5`) is classically unsatisfiable
(headline below), so the statement is classically true for every
package.

MLT-SHARING NOTE (2026-07-24, SUPERSEDED BY THE SECTION AUDIT ABOVE):
the project's deformation-theoretic patching vocabulary
(`Patching.lean`: `HardlyRamifiedFiniteDeformation`, strict Mazur
representability, `exists_conj_of_charFrob_eq_away`) is pinned to base
field `ℚ` — `IsHardlyRamified` itself hard-codes the local conditions
at the rational places `2` and `ℓ` — so this leaf cannot yet be
discharged through a shared general-base MLT node.  The
PATCHING-GENERALIZATION AUDIT of the section note above refines this:
`Patching.lean` splits into a base-agnostic commutative-algebra half
(reusable verbatim over any base), a `ℚ`-pinned arithmetic half
(needing genuine re-derivation over `F`), and an entirely absent
Hilbert-modular Hecke input; and the natural consumer of any future
general-base patching node is now the sub-leaf
`exists_heckeEigensystem_of_congruentSeed`, not this assembly.

ASSEMBLY (2026-07-24, REBUILT 2026-07-26 over the repaired `R = 𝕋`
node — PROVEN).  Three steps, of which only the second is a citation:

* the residual bridge over `F` (`exists_residualCongruence_over_base` —
  Chebotarev + Brauer–Nesbitt + base change) produces the bad set
  `badρ` and the congruence `hcong` identifying `ρ|_{G_F}` and the seed
  `σ` as lifts of one residual representation;
* the coefficient embedding `ιO : O ↪ ℚ̄_ℓ` is produced HERE
  (`exists_injective_ringHom_algebraicClosure_of_moduleFinite` — generic
  commutative algebra over `hZinj` and module-finiteness), and handed
  DOWN to the citation rather than demanded from it;
* `R = 𝕋` over `F` (`exists_heckeEigensystem_of_congruentSeed` —
  Kisin/Taylor patching over the totally real base) produces the Hecke
  field `E`, the place `ψℓ`, a genuine level `badF` containing the
  places over `ℓ`, and the `E`-valued eigenvalue function `a`;
* `charFrob_map_eq_heckePolynomial_of_heckeTrace` (PROVEN, no
  automorphic input) turns that trace datum into the full Hecke
  polynomial, the determinant coefficient being the rational integer
  `Nw` by the cyclotomic determinant clause of `hρ`.

The glue below therefore sets `heckeF w := X² − a w · X + Nw` over `E`
and is a single application of the last item.  The 2026-07-26 rebuild
also removed the `badF`-enlargement step this proof used to perform at
`ℓ`: the citation now returns a `badF` that already contains those
places, which is what a level IS.

CIRCULARITY GUARD (inherited from pillar β, load-bearing): no
discharge through `Family.lean`, `Lift.lean`, or
`Modularity/Interface.lean`; it binds each of the three sub-leaves. -/
theorem exists_heckePackage_of_seed
    {ℓ : ℕ} (hℓodd : Odd ℓ) [Fact ℓ.Prime] (hℓ5 : 5 ≤ ℓ)
    {O : Type u} [CommRing O] [IsDomain O] [TopologicalSpace O]
    [IsTopologicalRing O] [Algebra ℤ_[ℓ] O] [IsLocalRing O]
    [Module.Finite ℤ_[ℓ] O] [IsModuleTopology ℤ_[ℓ] O]
    (hZinj : Function.Injective (algebraMap ℤ_[ℓ] O))
    {ρ : GaloisRep ℚ O (Fin 2 → O)}
    (hrank : Module.rank O (Fin 2 → O) = 2)
    (hρ : IsHardlyRamified hℓodd hrank ρ)
    {k : Type u} [Field k] [Finite k] [Algebra ℤ_[ℓ] k]
    [TopologicalSpace k] [DiscreteTopology k]
    {W : Type v} [AddCommGroup W] [Module k W] [Module.Finite k W]
    [Module.Free k W]
    (hW : Module.rank k W = 2) {ρbar : GaloisRep ℚ k W}
    (hρbar : IsHardlyRamified hℓodd hW ρbar)
    (hirr : ρbar.IsIrreducible)
    (π : O →+* k) (hπsurj : Function.Surjective π)
    (hπ : ∀ (q : ℕ) (hq : q.Prime), q ≠ 2 → q ≠ ℓ →
      (ρ.charFrob hq.toHeightOneSpectrumRingOfIntegersRat).map π =
        ρbar.charFrob hq.toHeightOneSpectrumRingOfIntegersRat)
    (F : Type u) [Field F] [NumberField F]
    (hFtr : NumberField.IsTotallyReal F) (hFgal : IsGalois ℚ F)
    (hirrF : (ρbar.map (algebraMap ℚ F)).IsIrreducible)
    (seed : MoretBaillySeed ℓ F (ρbar.map (algebraMap ℚ F))) :
    ∃ (E : Type u) (_ : Field E) (_ : NumberField E)
      (badF : Finset (HeightOneSpectrum (NumberField.RingOfIntegers F)))
      (heckeF : HeightOneSpectrum (NumberField.RingOfIntegers F) →
        Polynomial E)
      (ψℓ : E →+* AlgebraicClosure ℚ_[ℓ])
      (ιO : O →+* AlgebraicClosure ℚ_[ℓ]) (_ : Function.Injective ιO),
      ∀ w ∉ badF,
        ((ρ.map (algebraMap ℚ F)).charFrob w).map ιO =
          (heckeF w).map ψℓ := by
  classical
  -- (c) the residual bridge: `ρ|_{G_F}` is a lift of `ρbar|_{G_F}`
  obtain ⟨badρ, hcong⟩ :=
    exists_residualCongruence_over_base hℓodd hℓ5 hZinj hrank hρ hW hρbar
      hirr π hπsurj hπ F hFtr hFgal hirrF
  -- the coefficient embedding `ιO : O ↪ ℚ̄_ℓ` (generic commutative algebra:
  -- `O` is a `ℤ_ℓ`-finite domain receiving `ℤ_ℓ` injectively).  It is
  -- produced HERE and handed down, rather than demanded from the citation.
  obtain ⟨ιO, hιO⟩ :=
    exists_injective_ringHom_algebraicClosure_of_moduleFinite (ℓ := ℓ) O hZinj
  -- (a) `R = 𝕋` over `F`: the Hecke field `E`, the place `ψℓ`, a genuine
  -- level `badF` containing the places over `ℓ`, and the `E`-valued
  -- eigenvalue function `a`
  obtain ⟨E, hE, hNE, ψℓ, badF, a, hbadℓ, htr⟩ :=
    exists_heckeEigensystem_of_congruentSeed hℓodd hℓ5 hZinj hrank hρ hW
      hρbar hirr π hπsurj hπ F hFtr hFgal hirrF seed badρ hcong ιO hιO
  letI : Field E := hE
  -- (b) the determinant half, PROVEN: the constant coefficient is the
  -- rational integer `Nw` away from `ℓ`, so the trace datum already
  -- assembles the Hecke polynomial `X² − a_w·X + Nw` over `E`
  refine ⟨E, hE, hNE, badF,
    fun w => X ^ 2 - C (a w) * X + C ((Ideal.absNorm w.asIdeal : E)), ψℓ, ιO,
    hιO, ?_⟩
  exact charFrob_map_eq_heckePolynomial_of_heckeTrace hℓodd hrank hρ F ψℓ badF
    a ιO hbadℓ htr

/-- **Free-lattice normalization over `ℤ_p`** (PROVEN, 2026-07-24; the
formal half of the Hilbert-modular `3`-adic realization leaf below): a
commutative ring `B` which is an integral DOMAIN, module-finite over
`ℤ_p`, and which receives `ℤ_p` injectively, is automatically FREE as
a `ℤ_p`-module.

This is the lattice bookkeeping that the Carayol/Taylor citation would
otherwise have to carry. Classically `B` is the ring of integers of a
finite extension `E_λ/ℚ_p` and its `ℤ_p`-freeness is quoted as "the
integers of a local field form a free lattice"; formally it is a
consequence of the structure theorem for finitely generated modules
over a principal ideal domain:

* `ℤ_p` is a discrete valuation ring
  (`PadicInt.instIsDiscreteValuationRing`), hence a principal ideal
  domain;
* between domains, injectivity of `algebraMap ℤ_p B` is exactly
  `ℤ_p`-torsion-freeness of `B`
  (`Module.isTorsionFree_iff_algebraMap_injective`);
* a finitely generated torsion-free module over a PID is free
  (`Module.free_of_finite_type_torsion_free'`).

Factoring this step out makes the citation leaf below STRICTLY WEAKER:
it no longer has to assert freeness of the coefficient ring, only that
the ring is a domain containing `ℤ_p` — which is literally what
Carayol's construction produces (the integers of the completion
`E_λ`). No arithmetic input, no vacuity route needed: this is a true
theorem of commutative algebra with no hypotheses about Galois
representations at all. -/
theorem free_of_finite_of_algebraMap_padicInt_injective {p : ℕ}
    [Fact p.Prime] {B : Type*} [CommRing B] [IsDomain B]
    [Algebra ℤ_[p] B] [Module.Finite ℤ_[p] B]
    (hinj : Function.Injective (algebraMap ℤ_[p] B)) :
    Module.Free ℤ_[p] B := by
  haveI : Module.IsTorsionFree ℤ_[p] B :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr hinj
  infer_instance

/-- **`ℤ_p` embeds into every characteristic-zero field it maps to**
(PROVEN, 2026-07-25; first of the five coefficient-ring bricks that
shrink the Carayol/Taylor citation below): any ring homomorphism
`ℤ_p → C` with `C` a field of characteristic zero is injective.

`ℤ_p` is a discrete valuation ring, so a nonzero `x` factors as
`unit * p ^ n` (`PadicInt.unitCoeff_spec`); its image is then a unit
times `(p : C) ^ n`, and both factors are nonzero in a
characteristic-zero field. No completeness or valuation theory is
needed beyond that factorization. -/
theorem injective_of_padicInt_ringHom_charZero {p : ℕ} [Fact p.Prime]
    {C : Type*} [Field C] [CharZero C] (g : ℤ_[p] →+* C) :
    Function.Injective g := by
  rw [injective_iff_map_eq_zero g]
  intro x hx
  by_contra hx0
  rw [PadicInt.unitCoeff_spec hx0, map_mul, map_pow, map_natCast] at hx
  rcases mul_eq_zero.mp hx with h | h
  · exact (IsUnit.map g (PadicInt.unitCoeff hx0).isUnit).ne_zero h
  · exact (Nat.cast_ne_zero.mpr (Fact.out (p := p.Prime)).ne_zero)
      (pow_eq_zero_iff'.mp h).1

/-- **The comparison map out of a `3`-adic coefficient ring is
automatically injective** (PROVEN, 2026-07-25; second coefficient-ring
brick): if `B` is an integral domain, module-finite over `ℤ_p`, then
EVERY ring homomorphism `B → C` into a characteristic-zero field is
injective.

Proof: `RingHom.ker f` contracts to `⊥` in `ℤ_p`, because
`f ∘ algebraMap ℤ_p B` is injective by
`injective_of_padicInt_ringHom_charZero`; and an ideal of an integral
extension of a domain lying over `⊥` IS `⊥`
(`Ideal.eq_bot_of_comap_eq_bot`, using `Algebra.IsIntegral ℤ_p B` from
module-finiteness — a nonzero element of the ideal contributes a
nonzero element of the contraction through its integral equation).

This is why the citation leaf below no longer has to assert
`Function.Injective ιB`: for the coefficient rings the construction
produces, injectivity of the comparison embedding is a THEOREM, not a
piece of input data. -/
theorem injective_of_finite_padicInt_charZero {p : ℕ} [Fact p.Prime]
    {B : Type*} [CommRing B] [IsDomain B] [Algebra ℤ_[p] B]
    [Module.Finite ℤ_[p] B] {C : Type*} [Field C] [CharZero C]
    (f : B →+* C) : Function.Injective f := by
  rw [RingHom.injective_iff_ker_eq_bot]
  refine Ideal.eq_bot_of_comap_eq_bot (R := ℤ_[p]) ?_
  rw [RingHom.comap_ker, ← RingHom.injective_iff_ker_eq_bot]
  exact injective_of_padicInt_ringHom_charZero (f.comp (algebraMap ℤ_[p] B))

/-- **`ℤ_p → B` is automatically injective once `B` maps to a
characteristic-zero field** (PROVEN, 2026-07-25; the same brick read on
the structure map): the composite `ℤ_p → B → C` is injective by
`injective_of_padicInt_ringHom_charZero`, hence so is its first factor.

Consequence for the cut below: the citation leaf need not assert
`Function.Injective (algebraMap ℤ_3 B)` either — the comparison
embedding `ιB` it produces already forces it, and the downstream
free-lattice normalization
(`free_of_finite_of_algebraMap_padicInt_injective`) is fed from here. -/
theorem injective_algebraMap_of_ringHom_charZero {p : ℕ} [Fact p.Prime]
    {B : Type*} [CommRing B] [Algebra ℤ_[p] B] {C : Type*} [Field C]
    [CharZero C] (f : B →+* C) :
    Function.Injective (algebraMap ℤ_[p] B) := by
  have h := injective_of_padicInt_ringHom_charZero (f.comp (algebraMap ℤ_[p] B))
  exact fun x y hxy => h (by simp only [RingHom.coe_comp, Function.comp_apply, hxy])

/-- **The module topology on a module-finite `ℤ_p`-algebra is a ring
topology** (PROVEN, 2026-07-25; third coefficient-ring brick): a
commutative ring `B` which is a `ℤ_p`-algebra and module-finite over
`ℤ_p` becomes a topological ring when given the `ℤ_p`-module topology,
which of course satisfies `IsModuleTopology ℤ_p B` by construction.

This is `IsModuleTopology.isTopologicalRing` (multiplication on a
module-finite algebra is `ℤ_p`-bilinear, and bilinear maps out of
finite modules with the module topology are continuous) applied to
`R = ℤ_p`.

Consequence for the cut below: the citation leaf need not produce a
topology on its coefficient ring at all — the topology is CANONICAL
(the module topology, which `IsModuleTopology` pins uniquely anyway),
and both `IsTopologicalRing` and `IsModuleTopology` are theorems here
rather than asserted components of the citation. -/
theorem isTopologicalRing_moduleTopology_of_finite (p : ℕ) [Fact p.Prime]
    (B : Type*) [CommRing B] [Algebra ℤ_[p] B] [Module.Finite ℤ_[p] B] :
    letI := moduleTopology ℤ_[p] B
    IsTopologicalRing B :=
  letI := moduleTopology ℤ_[p] B
  IsModuleTopology.isTopologicalRing ℤ_[p] B

/-- **Membership in `J • ⊤` inside a finite product is coordinatewise**
(PROVEN, 2026-07-25; first step of the locality brick below): for a
finite index type `ι`, an element of `ι → R` lies in `J • ⊤` exactly
when each of its coordinates lies in `J`.

One inclusion is `Submodule.smul_induction_on`; the other writes
`x = ∑ i, Pi.single i (x i)` and observes
`Pi.single i (x i) = x i • Pi.single i 1`. -/
theorem mem_ideal_smul_top_pi {R : Type*} [CommRing R] (J : Ideal R)
    {ι : Type*} [Fintype ι] [DecidableEq ι] (x : ι → R) :
    x ∈ J • (⊤ : Submodule R (ι → R)) ↔ ∀ i, x i ∈ J := by
  constructor
  · intro hx
    refine Submodule.smul_induction_on hx ?_ ?_
    · intro r hr n _ i
      exact J.mul_mem_right _ hr
    · intro a b ha hb i
      exact J.add_mem (ha i) (hb i)
  · intro hx
    rw [← Finset.univ_sum_single x]
    refine Submodule.sum_mem _ fun i _ => ?_
    have hsingle : Pi.single i (x i) = x i • (Pi.single i (1 : R) : ι → R) := by
      ext j
      by_cases h : j = i <;> simp [h]
    rw [hsingle]
    exact Submodule.smul_mem_smul (hx i) Submodule.mem_top

/-- **A finite product of a `J`-precomplete ring is `J`-precomplete**
(PROVEN, 2026-07-25): Cauchy sequences for the `J`-adic filtration on
`ι → R` are Cauchy coordinatewise, by `mem_ideal_smul_top_pi`, so the
limit can be assembled coordinate by coordinate. -/
theorem isPrecomplete_pi {R : Type*} [CommRing R] (J : Ideal R)
    {ι : Type*} [Fintype ι] [DecidableEq ι] [IsPrecomplete J R] :
    IsPrecomplete J (ι → R) where
  prec' := by
    intro f hf
    have hf' : ∀ i : ι, ∀ {m n : ℕ}, m ≤ n →
        f m i ≡ f n i [SMOD J ^ m • (⊤ : Submodule R R)] := by
      intro i m n hmn
      have h := hf hmn
      rw [SModEq.sub_mem] at h ⊢
      rw [smul_eq_mul, Ideal.mul_top]
      exact ((mem_ideal_smul_top_pi (J ^ m) _).mp h) i
    choose L hL using fun i => IsPrecomplete.prec' (I := J) (fun k => f k i) (hf' i)
    refine ⟨L, fun n => ?_⟩
    rw [SModEq.sub_mem, mem_ideal_smul_top_pi]
    intro i
    have h := hL i n
    rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top] at h
    exact h

/-- **`IsPrecomplete` transports along a linear equivalence** (PROVEN,
2026-07-25): a linear equivalence carries `J ^ n • ⊤` to `J ^ n • ⊤`
(`Submodule.map_smul''` plus surjectivity), so it carries Cauchy
sequences to Cauchy sequences and limits to limits. -/
theorem isPrecomplete_of_linearEquiv {R : Type*} [CommRing R]
    {M N : Type*} [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (J : Ideal R) (e : M ≃ₗ[R] N)
    [IsPrecomplete J M] : IsPrecomplete J N where
  prec' := by
    intro f hf
    have key : ∀ (n : ℕ) (y : N), y ∈ J ^ n • (⊤ : Submodule R N) ↔
        e.symm y ∈ J ^ n • (⊤ : Submodule R M) := by
      intro n y
      have hmap : Submodule.map (e.symm : N →ₗ[R] M) (J ^ n • (⊤ : Submodule R N)) =
          J ^ n • (⊤ : Submodule R M) := by
        rw [Submodule.map_smul'', Submodule.map_top]
        congr 1
        exact LinearMap.range_eq_top.mpr e.symm.surjective
      constructor
      · intro hy
        rw [← hmap]
        exact Submodule.mem_map_of_mem hy
      · intro hy
        rw [← hmap] at hy
        obtain ⟨z, hz, hze⟩ := hy
        have hyz : z = y := by
          have h := congrArg e hze
          simpa using h
        exact hyz ▸ hz
    have hf' : ∀ {m n : ℕ}, m ≤ n →
        e.symm (f m) ≡ e.symm (f n) [SMOD J ^ m • (⊤ : Submodule R M)] := by
      intro m n hmn
      have h := hf hmn
      rw [SModEq.sub_mem] at h ⊢
      rw [← map_sub]
      exact (key m _).mp h
    obtain ⟨L, hL⟩ := IsPrecomplete.prec' (I := J) (fun n => e.symm (f n)) hf'
    refine ⟨e L, fun n => ?_⟩
    have h := hL n
    rw [SModEq.sub_mem] at h ⊢
    refine (key n _).mpr ?_
    rw [map_sub]
    simpa using h

/-- **A finite free module over a `J`-precomplete ring is
`J`-precomplete** (PROVEN, 2026-07-25): choose a basis and transport
`isPrecomplete_pi` along `Basis.equivFun`.

The pin has `IsHausdorff` for finite modules over a Noetherian local
ring (`Mathlib/RingTheory/AdicCompletion/Noetherian.lean`) but NO
precompleteness statement for finite modules — that half is supplied
here, and the two together give `IsAdicComplete`. -/
theorem isPrecomplete_of_free_finite {R : Type*} [CommRing R] [Nontrivial R]
    (J : Ideal R) [IsPrecomplete J R]
    {M : Type*} [AddCommGroup M] [Module R M] [Module.Free R M] [Module.Finite R M] :
    IsPrecomplete J M := by
  classical
  let b := Module.Free.chooseBasis R M
  have hfin : Finite (Module.Free.ChooseBasisIndex R M) := Module.Finite.finite_basis b
  cases nonempty_fintype (Module.Free.ChooseBasisIndex R M)
  haveI := isPrecomplete_pi (R := R) J (ι := Module.Free.ChooseBasisIndex R M)
  exact isPrecomplete_of_linearEquiv J b.equivFun.symm

/-- **In a finite monoid some positive power of every element is
idempotent** (PROVEN, 2026-07-25): pigeonhole gives `a < b` with
`x ^ a = x ^ b`; with `d = b - a` the exponent map is then `d`-periodic
above `a`, and `n = (a + 1) * d` is both `≥ a` and a multiple of `d`,
so `x ^ (2 * n) = x ^ n`. -/
theorem exists_pos_pow_mul_self_eq {M : Type*} [Monoid M] [Finite M] (x : M) :
    ∃ n : ℕ, 0 < n ∧ x ^ n * x ^ n = x ^ n := by
  have aux : ∀ a b : ℕ, a < b → x ^ a = x ^ b → ∃ n : ℕ, 0 < n ∧ x ^ n * x ^ n = x ^ n := by
    intro a b hab h
    set d := b - a with hd
    have hd0 : 0 < d := by omega
    have hb : a + d = b := by omega
    have key : ∀ k : ℕ, a ≤ k → x ^ (k + d) = x ^ k := by
      intro k hk
      obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hk
      have hrw : a + t + d = a + d + t := by omega
      rw [hrw, hb, pow_add, ← h, ← pow_add]
    have key2 : ∀ (m : ℕ) (k : ℕ), a ≤ k → x ^ (k + m * d) = x ^ k := by
      intro m
      induction m with
      | zero => intro k _; simp
      | succ m ih =>
        intro k hk
        have hrw : k + (m + 1) * d = k + m * d + d := by ring
        rw [hrw, key _ (le_trans hk (Nat.le_add_right _ _)), ih k hk]
    refine ⟨(a + 1) * d, ?_, ?_⟩
    · exact Nat.mul_pos (Nat.succ_pos a) hd0
    · have hge : a ≤ (a + 1) * d := by
        calc a ≤ a + 1 := by omega
        _ = (a + 1) * 1 := by ring
        _ ≤ (a + 1) * d := by exact Nat.mul_le_mul_left _ hd0
      rw [← pow_add]
      exact key2 (a + 1) _ hge
  obtain ⟨i, j, hne, h⟩ := Finite.exists_ne_map_eq_of_infinite (fun n : ℕ => x ^ n)
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · exact aux i j hlt h
  · exact aux j i hlt h.symm

/-- **The residue ring of `ℤ_p` is finite** (PROVEN, 2026-07-25):
`PadicInt.residueField` identifies it with `ZMod p`. -/
instance finite_quotient_maximalIdeal_padicInt (p : ℕ) [Fact p.Prime] :
    Finite (ℤ_[p] ⧸ IsLocalRing.maximalIdeal ℤ_[p]) :=
  Finite.of_equiv (ZMod p) (PadicInt.residueField (p := p)).symm.toEquiv

/-- **A domain module-finite over `ℤ_p` is LOCAL** (PROVEN, 2026-07-25;
fifth coefficient-ring brick, and the one the 2026-07-25 audit on the
Carayol citation below recorded as still missing): if `B` is an
integral domain, module-finite over `ℤ_p`, receiving `ℤ_p` injectively,
then `B` is a local ring.

This is the Henselian property of `ℤ_p` in the only form the citation
needs, and it is proven here from the `p`-adic completeness of `B`
rather than from valuation theory:

* `B` is finite free over `ℤ_p`
  (`free_of_finite_of_algebraMap_padicInt_injective`), hence
  `p`-adically PRECOMPLETE (`isPrecomplete_of_free_finite`, built above
  because the pin has only the `IsHausdorff` half for finite modules);
  with the pin's Hausdorff instance this gives
  `IsAdicComplete (𝔪 ℤ_p) B`, and `IsAdicComplete.map_algebraMap_iff`
  moves it to the ideal `I = 𝔪 ℤ_p · B`;
* hence `HenselianRing B I` (`IsAdicComplete.henselianRing`) and
  `I ≤ jacobson ⊥`;
* `B ⧸ I` is FINITE (`Submodule.finite_quotient_smul` over the finite
  residue ring of `ℤ_p`), so for every `x` some positive power of its
  class is idempotent (`exists_pos_pow_mul_self_eq`);
* that idempotent lifts through `I` by Hensel applied to `X ^ 2 - X`
  — whose derivative `2 * a - 1` is a unit mod `I` because
  `(2 * a - 1) ^ 2 = 4 * (a ^ 2 - a) + 1` — and `B` is a DOMAIN, so the
  lift is `0` or `1`;
* if it is `1` then `x ^ n` is `1` modulo the Jacobson radical, hence a
  unit, hence `x` is; if it is `0` then `x ^ n ∈ I`, and
  `(∑ i < n, x ^ i) * (1 - x) = 1 - x ^ n` is a unit, hence `1 - x` is.

So `∀ x, IsUnit x ∨ IsUnit (1 - x)`, which is
`IsLocalRing.of_isUnit_or_isUnit_one_sub_self`.

WHY THE OBVIOUS ROUTES DO NOT WORK (recorded so they are not
re-derived). The 2026-07-25 audit on the citation proposed reading
locality off the uniqueness of the extension of the `p`-adic valuation
to `Frac B`; that needs the unbundled `spectralNorm` layer to be
bundled first, a much larger project. The purely ideal-theoretic route
— maximal ideals of `B` all lie over `(p)`, so it suffices to bound
the maximal ideals of `B ⧸ I` — cannot be closed WITHOUT completeness:
`ℤ[X]/(X ^ 2 + X + 1)` localized away from nothing is a domain,
module-finite over `ℤ`, with two maximal ideals over `(7)`. Completeness
is exactly what rules that out, and it enters only through the
idempotent lift.

Consequence for the cut below: `IsLocalRing B` is GONE from the
Carayol citation.

REDUNDANCY NOTE (2026-07-26, round 3 of the Carayol audit — recorded so
nobody re-derives either half). This lemma is STRICTLY REDUNDANT
against `isLocalRing_of_finite_padicInt` far below, which proves the
same conclusion WITHOUT the `hinj` hypothesis, by a Henselian-pair
argument that also covers the case where `p` dies in `B`. The two
coexist only because of Lean's declaration order: the general one sits
about four thousand lines further down, behind
`IsLocalRing.of_henselianRing_of_isDomain`, so the consumer here
cannot reach it. The clean fix is to hoist that pair above this point
and delete this lemma; it was deliberately NOT done here, because it is
a two-hundred-line relocation inside a file with several concurrent
owners and the gain is cosmetic. Whoever next needs to touch this
region should do it then. The "WHY THE OBVIOUS ROUTES DO NOT WORK"
paragraph above is the part worth preserving in any such merge. -/
theorem isLocalRing_of_finite_padicInt_domain {p : ℕ} [Fact p.Prime]
    {B : Type*} [CommRing B] [IsDomain B] [Algebra ℤ_[p] B]
    [Module.Finite ℤ_[p] B]
    (hinj : Function.Injective (algebraMap ℤ_[p] B)) : IsLocalRing B := by
  classical
  haveI : Module.Free ℤ_[p] B := free_of_finite_of_algebraMap_padicInt_injective hinj
  haveI : IsPrecomplete (IsLocalRing.maximalIdeal ℤ_[p]) B := isPrecomplete_of_free_finite _
  haveI : IsAdicComplete (IsLocalRing.maximalIdeal ℤ_[p]) B := ⟨⟩
  set I : Ideal B := (IsLocalRing.maximalIdeal ℤ_[p]).map (algebraMap ℤ_[p] B)
  haveI hcomp : IsAdicComplete I B :=
    (IsAdicComplete.map_algebraMap_iff (IsLocalRing.maximalIdeal ℤ_[p]) B).mpr inferInstance
  -- the residue ring `B ⧸ I` is finite
  haveI hsub : Subsingleton (B ⧸ (⊤ : Submodule ℤ_[p] B)) := by
    refine ⟨fun a b => ?_⟩
    obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ a
    obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective _ b
    rw [Submodule.Quotient.eq]
    exact Submodule.mem_top
  haveI : Finite (B ⧸ (⊤ : Submodule ℤ_[p] B)) := Finite.of_subsingleton
  haveI hfin1 : Finite (B ⧸ (IsLocalRing.maximalIdeal ℤ_[p]) • (⊤ : Submodule ℤ_[p] B)) :=
    Submodule.finite_quotient_smul _ Module.Finite.fg_top
  have hle : (IsLocalRing.maximalIdeal ℤ_[p]) • (⊤ : Submodule ℤ_[p] B) ≤
      LinearMap.ker ((Ideal.Quotient.mkₐ ℤ_[p] I).toLinearMap) := by
    intro y hy
    have hmem : y ∈ Submodule.restrictScalars ℤ_[p] I := by
      rw [← Ideal.smul_top_eq_map]; exact hy
    simpa [Ideal.Quotient.eq_zero_iff_mem] using hmem
  haveI hfinI : Finite (B ⧸ I) := by
    refine Finite.of_surjective
      (Submodule.liftQ ((IsLocalRing.maximalIdeal ℤ_[p]) • (⊤ : Submodule ℤ_[p] B))
        ((Ideal.Quotient.mkₐ ℤ_[p] I).toLinearMap) hle) ?_
    intro y
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
    exact ⟨Submodule.Quotient.mk b, rfl⟩
  -- the Henselian dichotomy
  have hjac : I ≤ (⊥ : Ideal B).jacobson := IsAdicComplete.le_jacobson_bot I
  have hunit_one_sub : ∀ j ∈ I, IsUnit (1 - j) := by
    intro j hj
    have h := (Ideal.mem_jacobson_bot.mp (hjac hj)) (-1)
    simpa [sub_eq_add_neg, add_comm] using h
  refine IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun x => ?_
  obtain ⟨n, hn, hidem⟩ := exists_pos_pow_mul_self_eq (Ideal.Quotient.mk I x)
  -- lift the idempotent `(mk x) ^ n` through the Henselian ideal `I`
  have hasq : Ideal.Quotient.mk I (x ^ n) * Ideal.Quotient.mk I (x ^ n)
      = Ideal.Quotient.mk I (x ^ n) := by
    rw [map_pow]; exact hidem
  have hz : Ideal.Quotient.mk I (x ^ n * x ^ n - x ^ n) = 0 := by
    rw [map_sub, map_mul, hasq, sub_self]
  have hmonic : (X ^ 2 - X : B[X]).Monic := by
    refine Polynomial.monic_X_pow_sub (n := 2) (lt_of_le_of_lt Polynomial.degree_X_le ?_)
    exact_mod_cast one_lt_two
  have hroot : (X ^ 2 - X : B[X]).eval (x ^ n) ∈ I := by
    have hev : (X ^ 2 - X : B[X]).eval (x ^ n) = x ^ n * x ^ n - x ^ n := by
      simp [sq]
    rw [hev, ← Ideal.Quotient.eq_zero_iff_mem]
    exact hz
  have hderiv : IsUnit (Ideal.Quotient.mk I ((X ^ 2 - X : B[X]).derivative.eval (x ^ n))) := by
    have hd : (X ^ 2 - X : B[X]).derivative.eval (x ^ n) = 2 * x ^ n - 1 := by
      simp [Polynomial.derivative_sub]
      norm_num
    rw [hd]
    have hexp : (2 * x ^ n - 1) * (2 * x ^ n - 1)
        = 4 * (x ^ n * x ^ n - x ^ n) + 1 := by ring
    have hsq : Ideal.Quotient.mk I (2 * x ^ n - 1) * Ideal.Quotient.mk I (2 * x ^ n - 1) = 1 := by
      rw [← map_mul, hexp, map_add, map_mul, hz, map_one, mul_zero, zero_add]
    exact isUnit_iff_exists_inv.mpr ⟨_, hsq⟩
  obtain ⟨e, he, hee⟩ :=
    HenselianRing.is_henselian (R := B) (I := I) (X ^ 2 - X) hmonic (x ^ n) hroot hderiv
  have hesq : e ^ 2 - e = 0 := by
    have h := he
    simp only [Polynomial.IsRoot, Polynomial.eval_sub, Polynomial.eval_pow,
      Polynomial.eval_X] at h
    exact h
  have hidem2 : e * (e - 1) = 0 := by linear_combination hesq
  rcases mul_eq_zero.mp hidem2 with h0 | h1
  · -- `e = 0`: `x ^ n ∈ I`, so `1 - x` divides the unit `1 - x ^ n`
    right
    have hxn : x ^ n ∈ I := by
      have h' := hee
      rw [h0, zero_sub] at h'
      exact neg_mem_iff.mp h'
    have hunit : IsUnit (1 - x ^ n) := hunit_one_sub _ hxn
    have hgeom : (∑ i ∈ Finset.range n, x ^ i) * (1 - x) = 1 - x ^ n := by
      have h := geom_sum_mul x n
      linear_combination -h
    rw [← hgeom] at hunit
    exact isUnit_of_mul_isUnit_right hunit
  · -- `e = 1`: `1 - x ^ n ∈ I`, so `x ^ n` is a unit
    left
    have he1 : e = 1 := sub_eq_zero.mp h1
    have hxn : (1 : B) - x ^ n ∈ I := by rw [← he1]; exact hee
    have hunit : IsUnit (1 - (1 - x ^ n)) := hunit_one_sub _ hxn
    simp only [sub_sub_cancel] at hunit
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    rw [pow_succ] at hunit
    exact isUnit_of_mul_isUnit_right hunit

/-! ### Coefficient-ring quotient normalization (2026-07-26)

The five declarations below remove `IsDomain B` from the Carayol/Taylor
citation. The mathematics is one line — the kernel of `ιB : B →+* ℚ̄_3` is
prime, so `B ⧸ ker ιB` is a domain, and everything in sight descends to it —
but "everything in sight" includes a Galois representation, so the descent
needs a COEFFICIENT base change with a `charFrob` compatibility.

`Modularity/Patching.lean` has exactly that bridge (`charFrob_baseChange`,
`charFrob_conj`) and it is unusable here twice over: that module is not in
this one's import cone, and its versions are stated over the base field `ℚ`
whereas the Carayol representation lives over `F`. So the two are restated
here for a general number field — the proofs are unchanged, since neither
ever used anything about `ℚ` — under names that cannot collide with
`Patching.lean`'s, because both modules live in this namespace and
`Modularity/Interface.lean` imports both. -/

set_option backward.isDefEq.respectTransparency false in
/-- **`charFrob` commutes with coefficient base change, over any number
field** (PROVEN 2026-07-26; the general-base restatement of
`Modularity/Patching.lean`'s `charFrob_baseChange`, whose proof is
base-field agnostic and is reproduced verbatim). -/
theorem charFrob_baseChange_of_numberField {K : Type*} [Field K] [NumberField K]
    {A : Type*} [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] {B : Type*} [CommRing B] [TopologicalSpace B]
    [IsTopologicalRing B] [Algebra A B] [ContinuousSMul A B]
    {M : Type*} [AddCommGroup M] [Module A M] [Module.Finite A M]
    [Module.Free A M]
    (v : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (ρ : GaloisRep K A M) :
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

set_option backward.isDefEq.respectTransparency false in
/-- **`charFrob` is conjugation-invariant, over any number field** (PROVEN
2026-07-26; the general-base restatement of `Modularity/Patching.lean`'s
`charFrob_conj`). -/
theorem charFrob_conj_of_numberField {K : Type*} [Field K] [NumberField K]
    {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    {M : Type*} [AddCommGroup M] [Module A M] [Module.Finite A M]
    [Module.Free A M]
    {N : Type*} [AddCommGroup N] [Module A N] [Module.Finite A N]
    [Module.Free A N]
    (v : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (ρ : GaloisRep K A M) (e : M ≃ₗ[A] N) :
    (ρ.conj e).charFrob v = ρ.charFrob v := by
  show ((ρ.conj e).toLocal v
      (Field.AbsoluteGaloisGroup.adicArithFrob v)).charpoly =
    ((ρ.toLocal v (Field.AbsoluteGaloisGroup.adicArithFrob v)).charpoly)
  rw [show (ρ.conj e).toLocal v
        (Field.AbsoluteGaloisGroup.adicArithFrob v) =
      (LinearEquiv.conj e) (ρ.toLocal v
        (Field.AbsoluteGaloisGroup.adicArithFrob v)) from rfl,
    LinearEquiv.charpoly_conj]

/-- **A continuous `algebraMap` into a topological ring gives a continuous
scalar action** (PROVEN 2026-07-26): `a • x = algebraMap a * x`. -/
theorem continuousSMul_of_algebraMap_continuous {A : Type*} {B : Type*}
    [CommRing A] [CommRing B] [TopologicalSpace A] [TopologicalSpace B]
    [Algebra A B] [ContinuousMul B] (h : Continuous (algebraMap A B)) :
    ContinuousSMul A B := by
  constructor
  have hc : Continuous fun x : A × B => (algebraMap A B) x.1 * x.2 :=
    continuous_mul.comp ((h.comp continuous_fst).prodMk continuous_snd)
  exact hc.congr fun x => (Algebra.smul_def x.1 x.2).symm

open TensorProduct in
/-- **A framed rank-`2` representation pushes forward along a continuous map
of coefficient rings, multiplying `charFrob` by that map** (PROVEN
2026-07-26): base change the representation and re-frame it by the
base-changed basis. -/
theorem exists_charFrob_map_algebraMap {K : Type*} [Field K] [NumberField K]
    {B : Type*} [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
    {B' : Type*} [CommRing B'] [TopologicalSpace B'] [IsTopologicalRing B']
    [Algebra B B'] [ContinuousSMul B B']
    (τ : GaloisRep K B (Fin 2 → B)) :
    ∃ τ' : GaloisRep K B' (Fin 2 → B'),
      ∀ w : HeightOneSpectrum (NumberField.RingOfIntegers K),
        τ'.charFrob w = (τ.charFrob w).map (algebraMap B B') := by
  classical
  let e : B' ⊗[B] (Fin 2 → B) ≃ₗ[B'] (Fin 2 → B') :=
    ((Pi.basisFun B (Fin 2)).baseChange B').equiv (Pi.basisFun B' (Fin 2))
      (Equiv.refl _)
  refine ⟨(τ.baseChange B').conj e, fun w => ?_⟩
  rw [charFrob_conj_of_numberField, charFrob_baseChange_of_numberField]

/-- **The coefficient ring of a realization may be assumed a DOMAIN**
(PROVEN 2026-07-26 — the brick that removes `IsDomain B` from the
Carayol/Taylor citation below).

Given a framed rank-`2` representation `τ` over a coefficient ring `B` which
is module-finite over `ℤ_p` and carries the `ℤ_p`-module topology, together
with ANY ring map `ιB : B →+* C` into a field, the pair `(B, τ, ιB)` may be
replaced by one whose coefficient ring is a domain, WITHOUT changing any
`ιB`-image of a Frobenius characteristic polynomial: take
`B' := B ⧸ ker ιB`, which is a domain because `ker ιB` is prime, is still
module-finite over `ℤ_p`, and receives the induced embedding.

The representation descends by `exists_charFrob_map_algebraMap`, whose
hypothesis `ContinuousSMul B B'` holds because the quotient map is
`ℤ_p`-linear between two module topologies, hence continuous
(`IsModuleTopology.continuous_of_linearMap`), and multiplication in `B'` is
continuous. Completeness plays no role: this is a quotient, not a lift. -/
theorem exists_domain_coefficientRing_of_ringHom {p : ℕ} [Fact p.Prime]
    {K : Type*} [Field K] [NumberField K]
    {B : Type u} [CommRing B] [Algebra ℤ_[p] B] [Module.Finite ℤ_[p] B]
    [TopologicalSpace B] [IsTopologicalRing B] [IsModuleTopology ℤ_[p] B]
    {C : Type*} [Field C] (ιB : B →+* C)
    (τ : GaloisRep K B (Fin 2 → B)) :
    ∃ (B' : Type u) (_ : CommRing B') (_ : IsDomain B')
      (_ : Algebra ℤ_[p] B') (_ : Module.Finite ℤ_[p] B'),
      letI : TopologicalSpace B' := moduleTopology ℤ_[p] B'
      letI : IsTopologicalRing B' :=
        isTopologicalRing_moduleTopology_of_finite p B'
      ∃ (τ' : GaloisRep K B' (Fin 2 → B')) (ιB' : B' →+* C),
        ∀ w : HeightOneSpectrum (NumberField.RingOfIntegers K),
          (τ'.charFrob w).map ιB' = (τ.charFrob w).map ιB := by
  classical
  haveI hp : (RingHom.ker ιB).IsPrime := RingHom.ker_isPrime ιB
  haveI hfin : Module.Finite ℤ_[p] (B ⧸ RingHom.ker ιB) :=
    Module.Finite.of_surjective
      (Ideal.Quotient.mkₐ ℤ_[p] (RingHom.ker ιB)).toLinearMap
      Ideal.Quotient.mk_surjective
  letI : TopologicalSpace (B ⧸ RingHom.ker ιB) :=
    moduleTopology ℤ_[p] (B ⧸ RingHom.ker ιB)
  haveI : IsModuleTopology ℤ_[p] (B ⧸ RingHom.ker ιB) := ⟨rfl⟩
  haveI hTR : IsTopologicalRing (B ⧸ RingHom.ker ιB) :=
    IsModuleTopology.isTopologicalRing ℤ_[p] (B ⧸ RingHom.ker ιB)
  haveI hcsmul : ContinuousSMul B (B ⧸ RingHom.ker ιB) := by
    refine continuousSMul_of_algebraMap_continuous ?_
    exact IsModuleTopology.continuous_of_linearMap (R := ℤ_[p])
      (Ideal.Quotient.mkₐ ℤ_[p] (RingHom.ker ιB)).toLinearMap
  obtain ⟨τ', hτ'⟩ :=
    exists_charFrob_map_algebraMap (B' := B ⧸ RingHom.ker ιB) τ
  refine ⟨B ⧸ RingHom.ker ιB, inferInstance, inferInstance, inferInstance,
    hfin, τ', Ideal.Quotient.lift (RingHom.ker ιB) ιB (fun a ha => ha),
    fun w => ?_⟩
  rw [hτ', Polynomial.map_map]
  congr 1

/-! ### STEP 1a — the ABHN existence half, cut into a symbol-algebra core
plus four ordinary-algebra bricks and one adelic brick

`exists_totallyDefinite_rigidified_quaternionAlgebra_of_even` (below) is now
a PROVEN assembly over the six declarations of this section — FOUR of which
are open leaves, while `nonempty_algEquiv_quaternion_of_neg` (STEP 1a-iv) and
`isUnit_of_ne_zero_quaternionAlgebra_of_neg_embedding` (STEP 1a-v) are PROVEN
here. The cut replaces an
abstract Brauer-group existence statement by a CONCRETE one: produce a pair
`a b : F` of totally negative elements whose symbol algebra `(a, b)_F` splits
at every finite place, then check by hand that `ℍ[F,a,0,b]` is a totally
definite quaternion division algebra split at every finite place, and finally
patch the local splittings into a rigidification. Everything except the first
and last leaf is char-`≠ 2` linear algebra with no arithmetic in it.

Why a symbol algebra rather than an abstract `D`: over a field of
characteristic `≠ 2` EVERY quaternion algebra is `ℍ[F,a,0,b]` for some
`a, b ∈ Fˣ`, and the three properties the consumer wants become visible
conditions on `a` and `b` — definite at a real place `v` iff `σ_v a < 0` and
`σ_v b < 0`, split at a finite place `w` iff the Hilbert symbol `(a,b)_w`
is trivial. That is what makes the parity bit legible: totally negative
`a, b` are nonsplit at ALL `[F : ℚ]` infinite places, and Hilbert's product
formula then forces `[F : ℚ]` to be even once all finite symbols are
trivial. -/

/-- **STEP 1a-i — THE ARITHMETIC CORE: a totally real field of EVEN degree
carries a totally negative Hilbert symbol that is split at every finite
place** (sorry leaf; CUT 2026-07-27 out of
`exists_totallyDefinite_rigidified_quaternionAlgebra_of_even`, which is now
a PROVEN assembly over this leaf and the five below).

This is the whole class-field-theoretic content of ABHN in this development,
and it is the ONLY leaf of the six that has any arithmetic in it.

Content. Produce `a b : F` such that

* `σ a < 0` and `σ b < 0` for every real embedding `σ` of `F` — with `hFtr`
  that is every infinite place, so `ℍ[F,a,0,b]` is nonsplit (indeed `≃ ℍ`)
  at every archimedean place, i.e. TOTALLY DEFINITE;
* `ℍ[F_w, a, 0, b] ≃ M₂(F_w)` for every finite place `w`, i.e. the Hilbert
  symbol `(a,b)_w` is trivial at every finite place.

Route (ABHN). The Albert–Brauer–Hasse–Noether exact sequence for the Brauer
group of a number field,

    0 → Br(F) → ⨁_v Br(F_v) --Σ inv--> ℚ/ℤ → 0,

says a class in `Br(F)` may be prescribed by arbitrary local invariants,
almost all zero, summing to `0` in `ℚ/ℤ`. Prescribing invariant `1/2` at
each infinite place and `0` at each finite place is admissible exactly
because the number of infinite places is `[F : ℚ]`, which `hFeven` says is
EVEN. The resulting class has order `2`, hence (index = exponent over a
number field) is represented by a quaternion division algebra `D/F`; and
since `char F = 0 ≠ 2`, `D ≃ ℍ[F,a,0,b]` for some `a, b ∈ Fˣ`. Reading off
the local conditions gives exactly the two bullets above: `ℍ[ℝ,x,0,y]` is
nonsplit iff `x < 0 AND y < 0`, so definiteness at every real place is
precisely total negativity of `a` and of `b`.

The pin does NOT have this — mathlib carries only
`Mathlib/Algebra/BrauerGroup/Defs.lean` (definitions of the Brauer group, no
local invariants and no exact sequence), the reference project `~/cs/FLT`
has none of it either, and nothing in this tree computes a local invariant.
So this leaf is a genuine theory build, but a SELF-CONTAINED one: it
mentions no Galois representation, no Hecke algebra and no automorphic form.

A CHEAPER CONCRETE ROUTE, worth recording because it needs only the ℚ-case
plus base change. Over `ℚ` the quaternion algebra ramified at `{∞, q}` is
the explicit symbol algebra `(-1, -q)` for `q ≡ 3 (mod 4)`. If `F/ℚ` is
Galois of even degree, `Gal(F/ℚ)` has an element `σ` of order `2` by Cauchy,
and Chebotarev supplies infinitely many primes `q` with `Frob_q = σ`, hence
with local degree `[F_w : ℚ_q] = 2` at every `w ∣ q`. Base-changing
invariants multiplies by the local degree, so `a := -1`, `b := -q` (pushed
into `F`) has invariant `2 · (1/2) = 0` at every `w ∣ q` and `1 · (1/2)`
at every real place. NOTE this route needs `IsGalois ℚ F`, which the
ultimate consumer HAS (`hFgal`) but which this leaf deliberately does NOT
take — ABHN needs only even degree and total reality. A successor taking the
concrete route must ADD `hFgal` to this statement (a cut-level change: report
it, do not make it silently), and then also add it to the assembly below.

FAITHFULNESS — `hFeven` is NECESSARY, not merely sufficient. Hilbert's
product formula `∏_v (a,b)_v = 1` runs over ALL places. Totally negative
`a, b` give `(a,b)_v = -1` at every one of the `[F : ℚ]` infinite places
(`hFtr`), so if every finite symbol is `+1` the number of `-1`s is
`[F : ℚ]`, which must therefore be even. For totally real `F` of ODD degree
the statement is FALSE, not merely unproven. This is where the node's parity
bit is spent.

CIRCULARITY GUARD (inherited from pillar β, load-bearing): no discharge
through `Family.lean`, `Lift.lean`, or `Modularity/Interface.lean`. -/
theorem exists_totallyNegative_split_quaternionSymbol_of_even
    (F : Type u) [Field F] [NumberField F]
    (hFtr : NumberField.IsTotallyReal F)
    (hFeven : Even (Module.finrank ℚ F)) :
    ∃ a b : F,
      (∀ (v : NumberField.InfinitePlace F) (hv : v.IsReal),
        NumberField.InfinitePlace.embedding_of_isReal hv a < 0 ∧
        NumberField.InfinitePlace.embedding_of_isReal hv b < 0) ∧
      (∀ w : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F),
        Nonempty (_root_.QuaternionAlgebra (w.adicCompletion F)
            (algebraMap F (w.adicCompletion F) a) 0 (algebraMap F (w.adicCompletion F) b)
          ≃ₐ[w.adicCompletion F] Matrix (Fin 2) (Fin 2) (w.adicCompletion F))) := by
  sorry

/-- **STEP 1a-ii — a symbol algebra with invertible parameters is a
quaternion algebra: central, simple, of dimension `4`** (sorry leaf; CUT
2026-07-27, ordinary algebra with no arithmetic in it).

`IsQuaternionAlgebra F D` bundles `IsSimpleRing D`, `Algebra.IsCentral F D`
and `Module.rank F D = 4`. For `D = ℍ[F,a,0,b]` the rank is
`QuaternionAlgebra.rank_eq_four`, already in the pin. What is missing from
the pin — checked: `grep -rn "IsCentral.*Quaternion" .lake/packages/mathlib`
returns nothing, and `Mathlib/Algebra/BrauerGroup/Defs.lean` has no symbol
algebras — is CENTRALITY and SIMPLICITY.

Both are the standard computation with the basis `1, i, j, k`, `i² = a`,
`j² = b`, `ij = k = -ji`, and both need `2 ≠ 0` (in characteristic `2` the
generalised `ℍ[F,c₁,c₂,c₃]` with `c₂ = 0` degenerates and this is false):

* CENTRE. `x = x₀ + x₁ i + x₂ j + x₃ k` commutes with `i` iff
  `2 a x₂ = 2 a x₃ = 0`, hence (using `a ≠ 0`, `2 ≠ 0`) `x₂ = x₃ = 0`;
  commuting with `j` then forces `x₁ = 0`. So the centre is `F`.
* SIMPLICITY. A nonzero two-sided ideal `I` contains some `x ≠ 0`; the
  conjugation trick `x ↦ x + i x i⁻¹ + j x j⁻¹ + k x k⁻¹ = 4 x₀` (this is
  where `2 ≠ 0` is used twice) either produces a nonzero element of `F ∩ I`,
  giving `I = ⊤`, or kills the real part, and iterating on `i x`, `j x`,
  `k x` shows every coordinate of `x` vanishes.

Alternatively, an in-tree route that avoids the hand computation: a
four-dimensional algebra with an anisotropic-or-hyperbolic norm form is
central simple by Wedderburn plus a rank count, and
`IsQuaternionAlgebra.nomepty_algEquiv_matrix_or_forall_isUnit` shows the
converse direction is already usable once this is in place.

Stated over an arbitrary field with `2 ≠ 0` rather than over a number field
on purpose: the consumer needs it only over `F`, but the general statement is
what would go to mathlib. -/
theorem isQuaternionAlgebra_quaternionAlgebra_of_ne_zero {F : Type*} [Field F]
    (h2 : (2 : F) ≠ 0) {a b : F} (ha : a ≠ 0) (hb : b ≠ 0) :
    _root_.IsQuaternionAlgebra F (_root_.QuaternionAlgebra F a 0 b) := by
  sorry

/-- **STEP 1a-iii — BASE CHANGE of a symbol algebra:
`K ⊗_F ℍ[F,a,0,b] ≃ ℍ[K,a,0,b]`** (sorry leaf; CUT 2026-07-27, ordinary
algebra with no arithmetic in it).

This is the brick that turns the local conditions of STEP 1a-i into
statements about `ℝ ⊗_F D` and `F_w ⊗_F D`, which is the shape both
`IsQuaternionAlgebra.IsTotallyDefinite` and the rigidification leaf want.

Checked absent from the pin: `grep -rn "baseChange" Mathlib/Algebra/Quaternion*`
returns nothing. It is a one-page construction from the universal property
`QuaternionAlgebra.lift : Basis A c₁ c₂ c₃ ≃ (ℍ[R,c₁,c₂,c₃] →ₐ[R] A)`
(`Mathlib/Algebra/QuaternionBasis.lean`):

* FORWARD: `Algebra.TensorProduct.lift` of `Algebra.ofId K ℍ[K,a,0,b]` and
  the `F`-algebra map `ℍ[F,a,0,b] →ₐ[F] ℍ[K,a,0,b]` obtained from
  `Basis.liftHom` applied to `⟨i, j, k⟩` of `ℍ[K,a,0,b]` — the defining
  relations transport along `algebraMap F K` by `IsScalarTower`.
* BACKWARD: `Basis.liftHom` applied to `⟨1 ⊗ₜ i, 1 ⊗ₜ j, 1 ⊗ₜ k⟩`.
* The two composites are the identity by `QuaternionAlgebra.hom_ext`
  (agreement on `i` and `j` suffices) and by `TensorProduct.induction_on`.

Only `CommRing` is asked of `K`, because that is all the construction uses;
the consumer instantiates it at the field `ℝ` (through
`(embedding_of_isReal hv).toAlgebra`) and at the completions `F_w`. -/
theorem nonempty_algEquiv_quaternionAlgebra_baseChange
    (F : Type*) [CommRing F] (K : Type*) [CommRing K] [Algebra F K] (a b : F) :
    Nonempty (_root_.TensorProduct F K (_root_.QuaternionAlgebra F a 0 b) ≃ₐ[K]
      _root_.QuaternionAlgebra K (algebraMap F K a) 0 (algebraMap F K b)) := by
  sorry

open scoped Quaternion in
/-- **STEP 1a-iv — CLASSIFICATION OVER `ℝ`: a symbol algebra with both
parameters NEGATIVE is Hamilton's `ℍ`** (PROVEN 2026-07-27; CUT 2026-07-27,
ordinary algebra with no arithmetic in it).

`ℍ` is `Quaternion ℝ = ℍ[ℝ,-1,0,-1]`, so this is the rescaling
`i ↦ √(-x) · i`, `j ↦ √(-y) · j`, `k ↦ √(-x)·√(-y) · k`, which is legitimate
exactly because `-x > 0` and `-y > 0` have real square roots. Verify the
defining relations: `(√(-x) i)² = (-x)(i²) = (-x)(-1) = x`, likewise for `j`,
and the product `(√(-x) i)(√(-y) j) = √(-x)√(-y) k` is the `k` demanded.
Build it with `QuaternionAlgebra.lift` in both directions and close with
`QuaternionAlgebra.hom_ext`.

This is the leaf that makes `IsQuaternionAlgebra.IsTotallyDefinite` provable:
that class asks literally for `Nonempty (ℝ ⊗[F] D ≃ₐ[ℝ] ℍ)` at each real
place, and STEP 1a-iii reduces it to this statement at
`x = σ a`, `y = σ b`.

CONVERSE (not needed here, but it is what makes STEP 1a-i's total negativity
the RIGHT hypothesis rather than a convenient one): if `x > 0` or `y > 0`
then `ℍ[ℝ,x,0,y] ≃ M₂(ℝ)`. So over `ℝ` the symbol is nonsplit precisely on
the totally negative pairs.

PROVEN 2026-07-27, exactly as described: `Bf` is the rescaled basis of `ℍ`
with parameters `(x, 0, y)`, `Bg` the inversely rescaled basis of
`ℍ[ℝ,x,0,y]` with parameters `(-1, 0, -1)`, and the two `liftHom`s are
mutually inverse by `hom_ext`. The `(-1 : ℝ)` ascriptions on `Bg` are
load-bearing: without them the numerals default to `ℤ` and the resulting
`liftHom` is a `ℤ`-algebra map out of `ℍ[ℤ,-1,0,-1]`. -/
theorem nonempty_algEquiv_quaternion_of_neg {x y : ℝ} (hx : x < 0) (hy : y < 0) :
    Nonempty (_root_.QuaternionAlgebra ℝ x 0 y ≃ₐ[ℝ] _root_.Quaternion ℝ) := by
  obtain ⟨p, hp0, hp⟩ : ∃ p : ℝ, p ≠ 0 ∧ p ^ 2 = -x :=
    ⟨Real.sqrt (-x), Real.sqrt_ne_zero'.mpr (by linarith), Real.sq_sqrt (by linarith)⟩
  obtain ⟨q, hq0, hq⟩ : ∃ q : ℝ, q ≠ 0 ∧ q ^ 2 = -y :=
    ⟨Real.sqrt (-y), Real.sqrt_ne_zero'.mpr (by linarith), Real.sq_sqrt (by linarith)⟩
  let Bf : _root_.QuaternionAlgebra.Basis (_root_.Quaternion ℝ) x 0 y :=
    { i := ⟨0, p, 0, 0⟩
      j := ⟨0, 0, q, 0⟩
      k := ⟨0, 0, 0, p * q⟩
      i_mul_i := by (ext <;> simp); linarith [hp]
      j_mul_j := by (ext <;> simp); linarith [hq]
      i_mul_j := by ext <;> simp
      j_mul_i := by (ext <;> simp); ring1 }
  let Bg : _root_.QuaternionAlgebra.Basis
      (_root_.QuaternionAlgebra ℝ x 0 y) (-1 : ℝ) 0 (-1 : ℝ) :=
    { i := ⟨0, p⁻¹, 0, 0⟩
      j := ⟨0, 0, q⁻¹, 0⟩
      k := ⟨0, 0, 0, (p * q)⁻¹⟩
      i_mul_i := by (ext <;> simp); field_simp; linarith [hp]
      j_mul_j := by (ext <;> simp); field_simp; linarith [hq]
      i_mul_j := by (ext <;> simp); field_simp
      j_mul_i := by ext <;> simp }
  let f : _root_.QuaternionAlgebra ℝ x 0 y →ₐ[ℝ] _root_.Quaternion ℝ := Bf.liftHom
  let g : _root_.Quaternion ℝ →ₐ[ℝ] _root_.QuaternionAlgebra ℝ x 0 y := Bg.liftHom
  have hfz : ∀ z : _root_.QuaternionAlgebra ℝ x 0 y,
      f z = algebraMap ℝ (_root_.Quaternion ℝ) z.re + z.imI • Bf.i + z.imJ • Bf.j +
        z.imK • Bf.k := fun _ => rfl
  have hgz : ∀ z : _root_.Quaternion ℝ,
      g z = algebraMap ℝ (_root_.QuaternionAlgebra ℝ x 0 y) z.re + z.imI • Bg.i +
        z.imJ • Bg.j + z.imK • Bg.k := fun _ => rfl
  refine ⟨AlgEquiv.ofAlgHom f g ?_ ?_⟩
  · apply _root_.Quaternion.hom_ext <;>
      simp [hfz, hgz, Bf, Bg] <;> (try ext) <;>
      (try simp [_root_.Quaternion.re_smul, _root_.Quaternion.imI_smul,
        _root_.Quaternion.imJ_smul, _root_.Quaternion.imK_smul]) <;> (try field_simp)
  · apply _root_.QuaternionAlgebra.hom_ext <;>
      simp [hfz, hgz, Bf, Bg] <;> (try field_simp)

/-- **STEP 1a-v — ANISOTROPY: a symbol algebra with both parameters negative
under SOME real embedding is a division ring** (PROVEN 2026-07-27; CUT
2026-07-27, ordinary algebra with no arithmetic in it).

The reduced norm of `x = x₀ + x₁ i + x₂ j + x₃ k` in `ℍ[F,a,0,b]` is
`N(x) = x * star x = x₀² - a x₁² - b x₂² + a b x₃²`, an element of `F`, and
`x` is a unit as soon as `N(x) ≠ 0` (with inverse `N(x)⁻¹ · star x`; note
`star` is already in the pin for the general `ℍ[R,c₁,c₂,c₃]`,
`QuaternionAlgebra.instStarRing`, while `normSq` in the pin is only defined
for `ℍ[R]` and so has to be written out here).

Applying the ring map `σ` with `σ a < 0` and `σ b < 0` turns `σ (N x)` into
`x₀² + (-σa) x₁² + (-σb) x₂² + (σa · σb) x₃²` with all four coefficients
STRICTLY POSITIVE — a positive definite real quadratic form. So `x ≠ 0`
forces `σ (N x) > 0`, hence `N x ≠ 0`, hence `x` is a unit.

This is what supplies the `DivisionRing D` component of the consumer's
conclusion, via `DivisionRing.ofIsUnitOrEqZero`, WITHOUT disturbing the
underlying `Ring` structure — which matters, because the consumer must hand
back an `Algebra F D` and an `IsQuaternionAlgebra F D` for the SAME ring.

Note only ONE real embedding is required, not total negativity: definiteness
at a single archimedean place already kills every zero divisor. -/
theorem isUnit_of_ne_zero_quaternionAlgebra_of_neg_embedding
    {F : Type*} [Field F] (σ : F →+* ℝ) {a b : F} (ha : σ a < 0) (hb : σ b < 0)
    (x : _root_.QuaternionAlgebra F a 0 b) (hx : x ≠ 0) : IsUnit x := by
  obtain ⟨x0, x1, x2, x3⟩ := x
  -- `n` is the reduced norm `x * star x`, written out because the pin's `normSq`
  -- exists only for `ℍ[R]`, not for the general symbol algebra.
  set n : F := x0 ^ 2 - a * x1 ^ 2 - b * x2 ^ 2 + a * b * x3 ^ 2 with hn
  have hn0 : n ≠ 0 := by
    intro h
    have hnσ : σ x0 ^ 2 + (-σ a) * σ x1 ^ 2 + (-σ b) * σ x2 ^ 2
        + (σ a * σ b) * σ x3 ^ 2 = 0 := by
      have : σ n = 0 := by rw [h, map_zero]
      rw [hn] at this
      simp only [map_add, map_sub, map_mul, map_pow] at this
      linarith [this]
    -- all four coefficients are strictly positive under `σ`, so the form is definite
    have hab : 0 < σ a * σ b := mul_pos_of_neg_of_neg ha hb
    have t1 : 0 ≤ (-σ a) * σ x1 ^ 2 := mul_nonneg (by linarith) (sq_nonneg _)
    have t2 : 0 ≤ (-σ b) * σ x2 ^ 2 := mul_nonneg (by linarith) (sq_nonneg _)
    have t3 : 0 ≤ (σ a * σ b) * σ x3 ^ 2 := mul_nonneg (le_of_lt hab) (sq_nonneg _)
    have t0 : 0 ≤ σ x0 ^ 2 := sq_nonneg _
    have e0 : σ x0 = 0 := sq_eq_zero_iff.mp (by linarith)
    have e1 : σ x1 = 0 := by
      have h1 : (-σ a) * σ x1 ^ 2 = 0 := by linarith
      rcases mul_eq_zero.mp h1 with h' | h'
      · linarith
      · exact sq_eq_zero_iff.mp h'
    have e2 : σ x2 = 0 := by
      have h1 : (-σ b) * σ x2 ^ 2 = 0 := by linarith
      rcases mul_eq_zero.mp h1 with h' | h'
      · linarith
      · exact sq_eq_zero_iff.mp h'
    have e3 : σ x3 = 0 := by
      have h1 : (σ a * σ b) * σ x3 ^ 2 = 0 := by linarith
      rcases mul_eq_zero.mp h1 with h' | h'
      · linarith
      · exact sq_eq_zero_iff.mp h'
    have hx0 : x0 = 0 := σ.injective (by simpa using e0)
    have hx1 : x1 = 0 := σ.injective (by simpa using e1)
    have hx2 : x2 = 0 := σ.injective (by simpa using e2)
    have hx3 : x3 = 0 := σ.injective (by simpa using e3)
    exact hx (by ext <;> simp [hx0, hx1, hx2, hx3])
  have hkey : x0 ^ 2 - a * x1 ^ 2 + a * b * x3 ^ 2 - b * x2 ^ 2 ≠ 0 := by
    intro h
    exact hn0 (by rw [hn]; linear_combination h)
  have hmul : (x0 ^ 2 - a * x1 ^ 2 + a * b * x3 ^ 2 - b * x2 ^ 2) *
      (x0 ^ 2 - a * x1 ^ 2 + a * b * x3 ^ 2 - b * x2 ^ 2)⁻¹ = 1 := mul_inv_cancel₀ hkey
  refine ⟨⟨⟨x0, x1, x2, x3⟩, n⁻¹ • star (⟨x0, x1, x2, x3⟩ : _root_.QuaternionAlgebra F a 0 b),
    ?_, ?_⟩, rfl⟩
  · ext <;> simp [hn] <;> first | ring1 | linear_combination hmul
  · ext <;> simp [hn] <;> first | ring1 | linear_combination hmul

/-- **STEP 1a-vi — ADELIC PATCHING: local splittings at every finite place
assemble into a RIGIDIFICATION** (sorry leaf; CUT 2026-07-27; the one leaf of
the six besides STEP 1a-i that is not elementary).

`IsQuaternionAlgebra.NumberField.WithRigidification F D`
(`Fermat/FLT/QuaternionAlgebra/NumberField.lean`) is an `F`-algebra map
`incl : D →ₐ[F] M₂(𝔸_F^∞)` whose `𝔸_F^∞`-linear extension
`D ⊗_F 𝔸_F^∞ → M₂(𝔸_F^∞)` is BIJECTIVE. The finite adeles are a RESTRICTED
product, so a family of local splittings `F_w ⊗_F D ≃ M₂(F_w)` is not by
itself enough: the isomorphisms must be compatible with the integral
structures at ALL BUT FINITELY MANY `w`.

Content of the leaf, and why it is true. Fix a maximal `𝒪_F`-order
`𝒪_D ⊂ D` (`D` is module-finite over `F`, so orders exist and a maximal one
exists by Zorn on the finitely many candidates between a given order and its
dual). Then:

* `D ⊗_F 𝔸_F^∞` is the restricted product of the `D ⊗_F F_w` with respect
  to the `𝒪_D ⊗ 𝒪_w`, because `D` is a finite free `F`-module and the finite
  adeles are the restricted product of the `F_w` with respect to the `𝒪_w`;
* `𝒪_D ⊗_{𝒪_F} 𝒪_w ≃ M₂(𝒪_w)` for almost all `w` — the finitely many
  exceptions are the `w` dividing the (reduced) discriminant of `𝒪_D`, and
  at those `w` the hypothesis `hsplit` still gives `D ⊗ F_w ≃ M₂(F_w)`, so
  a lattice may be moved to make the splitting integral;
* assembling the local splittings componentwise over the restricted product
  gives `incl` and its bijectivity.

The hypothesis is exactly "`D` is split at every finite place"; that
`hsplit` is what the docstring of `WithRigidification` refers to when it says
a rigidification "exists if and only if `D` is unramified at all finite
places".

Stated for an arbitrary quaternion algebra `D` over an arbitrary number
field, with no reference to `F` being totally real and none to the
archimedean behaviour of `D` — this leaf is about the finite adeles only, and
keeping it that way is what makes it independent of STEP 1a-i. -/
theorem nonempty_withRigidification_of_forall_split
    (F : Type*) [Field F] [NumberField F] (D : Type*) [Ring D] [Algebra F D]
    [_root_.IsQuaternionAlgebra F D]
    (hsplit : ∀ w : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F),
      Nonempty (_root_.TensorProduct F (w.adicCompletion F) D ≃ₐ[w.adicCompletion F]
        Matrix (Fin 2) (Fin 2) (w.adicCompletion F))) :
    Nonempty (_root_.IsQuaternionAlgebra.NumberField.WithRigidification F D) := by
  sorry

/-- **STEP 1a of the Carayol node — ALBERT–BRAUER–HASSE–NOETHER: a totally
real field of EVEN degree carries a totally definite quaternion algebra that
is split at every finite place** (PROVEN 2026-07-27 as an assembly over the
six leaves of the section above; CUT 2026-07-27 out of STEP 1,
`exists_totallyDefinite_heckeCharacter_of_heckePackage`, which is now a
PROVEN assembly over this leaf and its sibling
`exists_heckeCharacter_of_totallyDefinite_quaternionAlgebra`).

THE WITNESS IS A SYMBOL ALGEBRA. `exists_totallyNegative_split_quaternionSymbol_of_even`
supplies `a b : F` totally negative with every finite Hilbert symbol
`(a,b)_w` trivial, and the `D` handed back here is literally
`D := ℍ[F,a,0,b] = QuaternionAlgebra F a 0 b`. Each of the five components
of the conclusion is then discharged by a named brick:

* `IsQuaternionAlgebra F D` — `isQuaternionAlgebra_quaternionAlgebra_of_ne_zero`
  (central simple of dimension `4`; `a ≠ 0` and `b ≠ 0` are read off from
  total negativity at any one real place, and `(2 : F) ≠ 0` from `CharZero`);
* `DivisionRing D` — `isUnit_of_ne_zero_quaternionAlgebra_of_neg_embedding`
  at the chosen real place, fed to `DivisionRing.ofIsUnitOrEqZero`. Building
  it this way is deliberate: the resulting `DivisionRing` sits on the SAME
  `Ring` structure, so the `Algebra F D` and `IsQuaternionAlgebra F D`
  returned alongside it are the ones already in scope;
* `IsTotallyDefinite F D` — `nonempty_algEquiv_quaternionAlgebra_baseChange`
  at `K = ℝ` (with `Algebra F ℝ` the one induced by `embedding_of_isReal`,
  for which `algebraMap F ℝ` is that embedding by `rfl`) composed with
  `nonempty_algEquiv_quaternion_of_neg`;
* `Nonempty (WithRigidification F D)` —
  `nonempty_withRigidification_of_forall_split`, whose hypothesis is the
  base change at `K = F_w` composed with the finite-place splittings.

`hFtr` is used TWICE and both uses are essential: to know some infinite
place is real (so `D` is a division ring at all, and `a, b ≠ 0`), and to
turn "definite at every REAL place" into "definite at every INFINITE place",
which is what `IsTotallyDefinite` demands.

FAITHFULNESS. The conclusion is an EXISTENCE statement about `F` alone; it
is true for every totally real `F` of even degree and FALSE for every
totally real `F` of odd degree (the invariants of a quaternion algebra
split at all finite places would then be an odd number of copies of `1/2`,
summing to `1/2 ≠ 0`). So `hFeven` is not merely sufficient here, it is
necessary. After this cut the parity bit is spent entirely inside
`exists_totallyNegative_split_quaternionSymbol_of_even`: `hFeven` is passed
straight through by the assembly below and used nowhere else, which is the
honest bookkeeping — none of the five bricks knows about parity.

CIRCULARITY GUARD (inherited from pillar β, load-bearing): no discharge
through `Family.lean`, `Lift.lean`, or `Modularity/Interface.lean`. The six
leaves respect it: five are pure algebra and the sixth is class field
theory. -/
theorem exists_totallyDefinite_rigidified_quaternionAlgebra_of_even
    (F : Type u) [Field F] [NumberField F]
    (hFtr : NumberField.IsTotallyReal F)
    (hFeven : Even (Module.finrank ℚ F)) :
    ∃ (D : Type u) (_ : DivisionRing D) (_ : Algebra F D)
      (_ : _root_.IsQuaternionAlgebra F D)
      (_ : _root_.IsQuaternionAlgebra.IsTotallyDefinite F D),
      Nonempty (_root_.IsQuaternionAlgebra.NumberField.WithRigidification F D) := by
  classical
  obtain ⟨a, b, hneg, hsplitloc⟩ :=
    exists_totallyNegative_split_quaternionSymbol_of_even F hFtr hFeven
  -- `hFtr` gives a real place; total negativity there gives `a ≠ 0` and `b ≠ 0`.
  obtain ⟨v₀⟩ : Nonempty (NumberField.InfinitePlace F) := inferInstance
  have hv₀ : v₀.IsReal := hFtr.isReal v₀
  have ha : a ≠ 0 := fun h => by simpa [h] using (hneg v₀ hv₀).1
  have hb : b ≠ 0 := fun h => by simpa [h] using (hneg v₀ hv₀).2
  haveI hQ : _root_.IsQuaternionAlgebra F (_root_.QuaternionAlgebra F a 0 b) :=
    isQuaternionAlgebra_quaternionAlgebra_of_ne_zero (by norm_num) ha hb
  have hunit : ∀ x : _root_.QuaternionAlgebra F a 0 b, IsUnit x ∨ x = 0 := by
    intro x
    rcases eq_or_ne x 0 with rfl | hx
    · exact Or.inr rfl
    · exact Or.inl (isUnit_of_ne_zero_quaternionAlgebra_of_neg_embedding
        (NumberField.InfinitePlace.embedding_of_isReal hv₀)
        (hneg v₀ hv₀).1 (hneg v₀ hv₀).2 x hx)
  letI dr : DivisionRing (_root_.QuaternionAlgebra F a 0 b) :=
    DivisionRing.ofIsUnitOrEqZero hunit
  refine ⟨_root_.QuaternionAlgebra F a 0 b, dr, inferInstance, hQ, ⟨fun v hv => ?_⟩, ?_⟩
  · letI : Algebra F ℝ := (NumberField.InfinitePlace.embedding_of_isReal hv).toAlgebra
    obtain ⟨e⟩ := nonempty_algEquiv_quaternionAlgebra_baseChange F ℝ a b
    obtain ⟨f⟩ := nonempty_algEquiv_quaternion_of_neg (hneg v hv).1 (hneg v hv).2
    exact ⟨e.trans f⟩
  · refine nonempty_withRigidification_of_forall_split F
      (_root_.QuaternionAlgebra F a 0 b) ?_
    intro w
    obtain ⟨e⟩ :=
      nonempty_algEquiv_quaternionAlgebra_baseChange F (w.adicCompletion F) a b
    obtain ⟨f⟩ := hsplitloc w
    exact ⟨e.trans f⟩

/-- **A nonzero simultaneous eigenvector for a commutative coefficient algebra
produces an algebra CHARACTER** (PROVEN, 2026-07-27; general linear algebra, no
automorphic input).

`A` is a commutative `E`-algebra acting on an `E`-vector space `V`, compatibly
with the `E`-action (`IsScalarTower E A V`, `SMulCommClass A E V`), and `f ≠ 0`
is a vector every element of `A` scales. Then the scaling factor is an
`E`-algebra homomorphism `A →ₐ[E] E`, and the conclusion is stated in the
"read off the eigenvalue" form `∀ a e, a • f = e • f → θ a = e`, which is what a
consumer actually needs: it both DEFINES `θ` on the generators and gives back the
uniqueness of the eigenvalue, so no separate injectivity argument is needed
downstream.

Well-definedness is the only content: `e • f = e' • f` with `f ≠ 0` forces
`e = e'`, because `(e - e') • f = 0` and `e - e'` would otherwise be invertible.
The algebra-hom axioms are then forced, `map_mul'` using commutativity of the
`A`- and `E`-actions.

This is the brick that turns the Jacquet–Langlands EIGENFORM into the Hecke
CHARACTER the Carayol node consumes; see
`exists_heckeCharacter_of_totallyDefinite_quaternionAlgebra`. -/
theorem exists_algHom_of_smul_eq_smul
    {E : Type*} [Field E] {A : Type*} [CommRing A] [Algebra E A]
    {V : Type*} [AddCommGroup V] [Module E V] [Module A V]
    [IsScalarTower E A V] [SMulCommClass A E V]
    {f : V} (hf : f ≠ 0) (h : ∀ a : A, ∃ e : E, a • f = e • f) :
    ∃ θ : A →ₐ[E] E, ∀ (a : A) (e : E), a • f = e • f → θ a = e := by
  have hinj : ∀ e e' : E, e • f = e' • f → e = e' := by
    intro e e' he
    by_contra hne
    apply hf
    have h0 : (e - e') • f = 0 := by rw [sub_smul, he, sub_self]
    have h1 := congrArg (fun x => (e - e')⁻¹ • x) h0
    simpa [smul_smul, inv_mul_cancel₀ (sub_ne_zero.mpr hne)] using h1
  obtain ⟨θ₀, hθ⟩ : ∃ θ₀ : A → E, ∀ a : A, a • f = θ₀ a • f :=
    ⟨fun a => (h a).choose, fun a => (h a).choose_spec⟩
  refine ⟨{ toFun := θ₀
            map_one' := hinj _ _ (by rw [← hθ, one_smul, one_smul])
            map_mul' := fun x y => hinj _ _ ?_
            map_zero' := hinj _ _ (by rw [← hθ, zero_smul, zero_smul])
            map_add' := fun x y => hinj _ _ ?_
            commutes' := fun e => hinj _ _ ?_ },
    fun a e he => hinj _ _ ((hθ a).symm.trans he)⟩
  · rw [← hθ, mul_smul, hθ y, smul_comm, hθ x, smul_smul, mul_comm]
  · rw [← hθ, add_smul, hθ x, hθ y, add_smul]
  · rw [← hθ, algebraMap_smul]
    simp

/-- **An auxiliary prime for the quaternionic level datum exists** (PROVEN,
2026-07-27; CUT out of STEP 1b, `exists_heckeCharacter_of_totallyDefinite_quaternionAlgebra`).

`TotallyDefiniteQuaternionAlgebra.U₁Data F R p` carries two conditions on `p`
that have NOTHING to do with Jacquet–Langlands: `p.Prime` and
`2 < [F(ζ_p) : F]` (the latter is what makes the `U₁`-level "sufficiently
small", i.e. what kills the units obstruction in
`U₁Data.eq_one_of_pow_eq_one_of_natDegree_le_two`). Since the level datum built
by the transfer half takes trivial characters at the bad places, ANY `p`
satisfying these two conditions serves, so this obligation splits off cleanly
and the citation shrinks by exactly it.

Proof. `[F(ζ_p) : ℚ] = [F : ℚ] · [F(ζ_p) : F]`, and `F(ζ_p)` contains
`ℚ(ζ_p)`, whose degree over `ℚ` is `φ(p) = p - 1` because `cyclotomic p ℚ` is
irreducible (`Polynomial.cyclotomic.irreducible_rat`) and is therefore the
minimal polynomial of a primitive `p`-th root of unity. Hence
`p - 1 ≤ [F : ℚ] · [F(ζ_p) : F]`, and choosing `p ≥ 2·[F : ℚ] + 2` prime
(infinitude of primes) forces `[F(ζ_p) : F] > 2`. Note the argument bounds the
degree from BELOW and so needs no irreducibility of `cyclotomic p F`, which is
false in general. -/
theorem exists_prime_two_lt_finrank_cyclotomicField
    (F : Type u) [Field F] [NumberField F] :
    ∃ p : ℕ, p.Prime ∧ 2 < Module.finrank F (CyclotomicField p F) := by
  classical
  obtain ⟨p, hple, hp⟩ := Nat.exists_infinite_primes (2 * Module.finrank ℚ F + 2)
  refine ⟨p, hp, ?_⟩
  haveI : NeZero p := ⟨hp.ne_zero⟩
  set L := CyclotomicField p F with hLdef
  have hζ : IsPrimitiveRoot (IsCyclotomicExtension.zeta p F L) p :=
    IsCyclotomicExtension.zeta_spec p F L
  set ζ := IsCyclotomicExtension.zeta p F L with hζdef
  have hmin : minpoly ℚ ζ = Polynomial.cyclotomic p ℚ :=
    (hζ.minpoly_eq_cyclotomic_of_irreducible
      (Polynomial.cyclotomic.irreducible_rat hp.pos)).symm
  have hint : IsIntegral ℚ ζ := IsIntegral.of_finite ℚ ζ
  have hdeg : Module.finrank ℚ (IntermediateField.adjoin ℚ ({ζ} : Set L)) = p - 1 := by
    rw [IntermediateField.adjoin.finrank hint, hmin, Polynomial.natDegree_cyclotomic,
      Nat.totient_prime hp]
  have hle : Module.finrank ℚ (IntermediateField.adjoin ℚ ({ζ} : Set L))
      ≤ Module.finrank ℚ L :=
    Nat.le_of_dvd Module.finrank_pos
      ⟨_, (Module.finrank_mul_finrank ℚ (IntermediateField.adjoin ℚ ({ζ} : Set L)) L).symm⟩
  have htow : Module.finrank ℚ F * Module.finrank F L = Module.finrank ℚ L :=
    Module.finrank_mul_finrank ℚ F L
  have hFpos : 0 < Module.finrank ℚ F := Module.finrank_pos
  by_contra hcon
  have hmul : Module.finrank ℚ F * Module.finrank F L ≤ Module.finrank ℚ F * 2 :=
    Nat.mul_le_mul_left _ (Nat.le_of_not_lt hcon)
  omega

/-- **STEP 1b′ of the Carayol node — JACQUET–LANGLANDS proper, in its EIGENFORM
form** (sorry leaf; CUT 2026-07-27 out of STEP 1b,
`exists_heckeCharacter_of_totallyDefinite_quaternionAlgebra`, which is now a
PROVEN assembly over this leaf, `exists_prime_two_lt_finrank_cyclotomicField`
and `exists_algHom_of_smul_eq_smul`).

Content, and what the cut removed from the citation. The parent asked for an
`E`-algebra CHARACTER of `TotallyDefiniteQuaternionAlgebra.HeckeAlgebra D 𝒮`.
Two of the three things that requires are not Jacquet–Langlands at all:

* the auxiliary prime `p` of the level datum (`p.Prime`, `2 < [F(ζ_p) : F]`) —
  now an INPUT, supplied by `exists_prime_two_lt_finrank_cyclotomicField`;
* the passage from a Hecke EIGENVECTOR to an algebra CHARACTER — pure linear
  algebra over a commutative subalgebra of `End_E`, now
  `exists_algHom_of_smul_eq_smul`, using
  `HeckeAlgebra.adjoin_T_U_eq_top` to see that the `T`'s and `U`'s generate.

What is LEFT here is the analytic statement and nothing else: the Hilbert
eigensystem `(E, heckeF)` — automorphic by `hmod` together with the cuspidality
proxy `hirrF` — is matched, place by place outside `badF`, by a NONZERO weight-`2`
automorphic form `f` on `Dˣ` of level `U₁(S, ∅)`, which is a simultaneous
eigenvector for every `T_w` with `w ∉ S`. Jacquet–Langlands, *Automorphic forms
on GL(2)*, Lecture Notes in Math. **114** (1970), §14–16; see also Carayol 1986
§0.9. Classically: `π` cuspidal on `GL₂/F`, discrete series (here: weight `2`)
at every infinite place, transfers to an automorphic representation `π'` of
`Dˣ` with the same finite components, and `f` is the new vector in the
`U₁(S, ∅)`-fixed line of `π'`; the eigenvalues at `w ∉ S` agree because
`π'_w ≅ π_w` is unramified there.

`𝒮.Q = ∅` IS PART OF THE CONCLUSION AND IS NOT A WEAKENING. `Q` is the set of
Taylor–Wiles primes, an AUXILIARY datum imposed by the patching argument
downstream, not by the transfer; the form Jacquet–Langlands produces lives at
the minimal level, with no tame-`p` condition. Pinning it here is what makes the
`U`-generators of the Hecke algebra vacuous, hence what lets the parent's
character be built from the `T`-eigenvalues alone. A successor who finds it
inconvenient may drop it and instead conclude `∀ w ∈ 𝒮.Q, ∀ α ≠ 0, ∃ e,
U D E 𝒮 w _ α _ f = e • f`; the parent assembly would then need that clause in
its `mem` case and nothing else changes.

`a` IS AN OUTPUT AND IS ONLY PINNED OUTSIDE `badF ∪ 𝒮.S`. That asymmetry is
deliberate and necessary: the character has to be defined on `T_w` for EVERY
`w ∉ 𝒮.S`, including the `w ∈ badF \ 𝒮.S` where `hmod` says nothing, so `f` must
be a `T_w`-eigenvector there too — but its eigenvalue is not determined by the
data and must not be asserted to be `-(heckeF w).coeff 1`. This is exactly why
the eigenvalue function `a` is existentially quantified rather than written as
`fun w => -(heckeF w).coeff 1`.

WHY THE DEFINITENESS HYPOTHESIS IS LOAD-BEARING — inherited verbatim from the
parent, and this statement is FALSE without it. `D := M₂(F)` is a rigidified
quaternion algebra over every `F`, and the split algebra has no
compact-mod-centre unit group, so the finite-dimensional space of weight-`2`
forms on `Dˣ` that the vendored `HeckeAlgebra` is built from is not the one
Jacquet–Langlands transfers into. `IsTotallyDefinite F D` together with
`WithRigidification F D` pins `D` completely.

`hFeven` IS DELIBERATELY ABSENT, for the parent's reason: a totally definite `D`
split at every finite place has local invariant `1/2` at each of the `[F : ℚ]`
infinite places and `0` elsewhere, and those must sum to `0` in `ℚ/ℤ`.

CIRCULARITY GUARD (inherited from pillar β, load-bearing): no discharge
through `Family.lean`, `Lift.lean`, or `Modularity/Interface.lean`. -/
theorem exists_eigenform_of_totallyDefinite_quaternionAlgebra
    {ℓ : ℕ} (hℓodd : Odd ℓ) [Fact ℓ.Prime] (hℓ5 : 5 ≤ ℓ)
    {O : Type u} [CommRing O] [IsDomain O] [TopologicalSpace O]
    [IsTopologicalRing O] [Algebra ℤ_[ℓ] O] [IsLocalRing O]
    [Module.Finite ℤ_[ℓ] O] [IsModuleTopology ℤ_[ℓ] O]
    (hZinj : Function.Injective (algebraMap ℤ_[ℓ] O))
    {ρ : GaloisRep ℚ O (Fin 2 → O)}
    (hrank : Module.rank O (Fin 2 → O) = 2)
    (hρ : IsHardlyRamified hℓodd hrank ρ)
    {k : Type u} [Field k] [Finite k] [Algebra ℤ_[ℓ] k]
    [TopologicalSpace k] [DiscreteTopology k]
    {W : Type v} [AddCommGroup W] [Module k W] [Module.Finite k W]
    [Module.Free k W]
    (hW : Module.rank k W = 2) {ρbar : GaloisRep ℚ k W}
    (hρbar : IsHardlyRamified hℓodd hW ρbar)
    (hirr : ρbar.IsIrreducible)
    (π : O →+* k) (hπsurj : Function.Surjective π)
    (hπ : ∀ (q : ℕ) (hq : q.Prime), q ≠ 2 → q ≠ ℓ →
      (ρ.charFrob hq.toHeightOneSpectrumRingOfIntegersRat).map π =
        ρbar.charFrob hq.toHeightOneSpectrumRingOfIntegersRat)
    (F : Type u) [Field F] [NumberField F]
    (hFtr : NumberField.IsTotallyReal F) (hFgal : IsGalois ℚ F)
    (hirrF : (ρbar.map (algebraMap ℚ F)).IsIrreducible)
    (E : Type u) [Field E] [NumberField E]
    (badF : Finset (HeightOneSpectrum (NumberField.RingOfIntegers F)))
    (heckeF : HeightOneSpectrum (NumberField.RingOfIntegers F) →
      Polynomial E)
    (ψℓ : E →+* AlgebraicClosure ℚ_[ℓ])
    (ιO : O →+* AlgebraicClosure ℚ_[ℓ]) (hιO : Function.Injective ιO)
    (hmod : ∀ w ∉ badF,
      ((ρ.map (algebraMap ℚ F)).charFrob w).map ιO =
        (heckeF w).map ψℓ)
    (hbad2 : ∀ w : HeightOneSpectrum (NumberField.RingOfIntegers F),
      (2 : NumberField.RingOfIntegers F) ∈ w.asIdeal → w ∈ badF)
    (hbad3 : ∀ w : HeightOneSpectrum (NumberField.RingOfIntegers F),
      (3 : NumberField.RingOfIntegers F) ∈ w.asIdeal → w ∈ badF)
    (hbadℓ : ∀ w : HeightOneSpectrum (NumberField.RingOfIntegers F),
      (ℓ : NumberField.RingOfIntegers F) ∈ w.asIdeal → w ∈ badF)
    (D : Type u) [DivisionRing D] [Algebra F D]
    [_root_.IsQuaternionAlgebra F D]
    [_root_.IsQuaternionAlgebra.IsTotallyDefinite F D]
    [_root_.IsQuaternionAlgebra.NumberField.WithRigidification F D]
    (p : ℕ) (hp : p.Prime)
    (hcyc : 2 < Module.finrank F (CyclotomicField p F)) :
    ∃ (𝒮 : _root_.TotallyDefiniteQuaternionAlgebra.U₁Data F E p)
      (a : HeightOneSpectrum (NumberField.RingOfIntegers F) → E)
      (f : (_root_.TotallyDefiniteQuaternionAlgebra.U₁ 𝒮).toStruct.form D E),
      𝒮.Q = ∅ ∧ f ≠ 0 ∧
      (∀ (w : HeightOneSpectrum (NumberField.RingOfIntegers F)) (hwS : w ∉ 𝒮.S),
        _root_.TotallyDefiniteQuaternionAlgebra.HeckeOperator.T D E 𝒮 w hwS f = a w • f) ∧
      (∀ w : HeightOneSpectrum (NumberField.RingOfIntegers F), w ∉ 𝒮.S → w ∉ badF →
        (heckeF w).coeff 1 = - a w) := by
  sorry

/-- **STEP 1b of the Carayol node — JACQUET–LANGLANDS proper: the Hilbert
eigensystem `(E, heckeF)` transfers to a GIVEN totally definite rigidified
quaternion algebra** (PROVEN assembly since 2026-07-27; CUT 2026-07-27 out of STEP 1,
`exists_totallyDefinite_heckeCharacter_of_heckePackage`, which is now a
PROVEN assembly over this leaf and its sibling
`exists_totallyDefinite_rigidified_quaternionAlgebra_of_even`).

Content. `D` is handed in, no longer produced: a division algebra over `F`
which is a quaternion algebra, TOTALLY DEFINITE, and carries a
rigidification `D ⊗_F 𝔸_F^∞ ≃ M₂(𝔸_F^∞)`. Jacquet–Langlands transfers the
Hilbert-newform eigensystem underlying `(E, heckeF)` to a weight-`2`
automorphic form on `Dˣ`, i.e. to an `E`-algebra CHARACTER `θ` of the Hecke
algebra `TotallyDefiniteQuaternionAlgebra.HeckeAlgebra D 𝒮` for a suitable
level datum `𝒮`, whose `T_w`-eigenvalue is the trace
`a_w = -(heckeF w).coeff 1` of the Hecke polynomial at every good `w`.
Automorphy of `(E, heckeF)` itself is supplied by `hmod` together with the
cuspidality proxy `hirrF`; the RESIDUAL FAITHFULNESS GAP that leaves is
stated in `carayol_threeadic_realization_of_heckePackage`'s docstring and
is unchanged by this cut.

This WAS a bare citation and is now an ASSEMBLY (2026-07-27) over three
declarations stated immediately above, of which only the first is a citation:

* `exists_eigenform_of_totallyDefinite_quaternionAlgebra` — Jacquet–Langlands
  proper, in its eigenform form: a NONZERO weight-`2` form `f` on `Dˣ` of level
  `U₁(S, ∅)`, simultaneous eigenvector for every `T_w` with `w ∉ S`, whose
  eigenvalue is `-(heckeF w).coeff 1` outside `badF`. Jacquet–Langlands,
  *Automorphic forms on GL(2)*, Lecture Notes in Math. **114** (1970), §14–16;
  see also Carayol 1986 §0.9, which is where the even-degree quaternionic form
  of Théorème (A) comes from in the first place;
* `exists_prime_two_lt_finrank_cyclotomicField` (PROVEN) — the auxiliary prime
  `p` of the level datum. `U₁Data` demands `p.Prime` and `2 < [F(ζ_p) : F]`,
  neither of which is automorphic; with trivial characters at the bad places any
  such `p` serves, so this obligation is not part of the correspondence and is
  now discharged in-tree;
* `exists_algHom_of_smul_eq_smul` (PROVEN) — the passage from Hecke
  EIGENVECTOR to Hecke CHARACTER. `HeckeAlgebra D 𝒮` is a COMMUTATIVE
  subalgebra of `End_E` generated by the `T`'s and `U`'s
  (`HeckeAlgebra.adjoin_T_U_eq_top`), the `U`'s are vacuous because the leaf
  delivers `𝒮.Q = ∅`, so `Algebra.adjoin_induction` propagates "scales `f`"
  from the generators to the whole algebra and the scaling factor IS the
  character.

So what remains cited is exactly the analytic transfer, and the two pieces of
bookkeeping that used to travel with it are gone from the citation.

WHY THE DEFINITENESS HYPOTHESIS IS LOAD-BEARING — this statement is FALSE
without it. Quantified over an ARBITRARY rigidified `D`, the conclusion is
false: `D := M₂(F)` is a rigidified quaternion algebra over every `F` (take
`incl` the base change of the identity), and the split algebra has no
compact-mod-centre unit group, so the finite-dimensional space of weight-`2`
forms on `Dˣ` that the vendored `HeckeAlgebra` is built from is not the one
Jacquet–Langlands transfers into. `IsTotallyDefinite F D` together with
`WithRigidification F D` pins `D` completely: definiteness ramifies it at
every real place, the rigidification splits it at every finite place, and
`hFtr` makes those two conditions exhaust the places — so by ABHN's
uniqueness `D` is THE algebra ramified exactly at the infinite places, the
one the correspondence is stated for. It is exactly this that made the cut
possible; the earlier docstring recorded the two halves as inseparable
because it believed no `IsTotallyDefinite` predicate existed in this tree.

`hFeven` IS DELIBERATELY ABSENT and its absence is not a weakening: the
hypotheses here already IMPLY it. A totally definite `D` split at every
finite place has local invariant `1/2` at each of the `[F : ℚ]` infinite
places and `0` elsewhere, and those must sum to `0` in `ℚ/ℤ`, so `[F : ℚ]`
is even. The parity bit is spent entirely in the sibling leaf, where the
algebra is PRODUCED; here it comes back for free from the datum.

CIRCULARITY GUARD (inherited from pillar β, load-bearing): no discharge
through `Family.lean`, `Lift.lean`, or `Modularity/Interface.lean`. -/
theorem exists_heckeCharacter_of_totallyDefinite_quaternionAlgebra
    {ℓ : ℕ} (hℓodd : Odd ℓ) [Fact ℓ.Prime] (hℓ5 : 5 ≤ ℓ)
    {O : Type u} [CommRing O] [IsDomain O] [TopologicalSpace O]
    [IsTopologicalRing O] [Algebra ℤ_[ℓ] O] [IsLocalRing O]
    [Module.Finite ℤ_[ℓ] O] [IsModuleTopology ℤ_[ℓ] O]
    (hZinj : Function.Injective (algebraMap ℤ_[ℓ] O))
    {ρ : GaloisRep ℚ O (Fin 2 → O)}
    (hrank : Module.rank O (Fin 2 → O) = 2)
    (hρ : IsHardlyRamified hℓodd hrank ρ)
    {k : Type u} [Field k] [Finite k] [Algebra ℤ_[ℓ] k]
    [TopologicalSpace k] [DiscreteTopology k]
    {W : Type v} [AddCommGroup W] [Module k W] [Module.Finite k W]
    [Module.Free k W]
    (hW : Module.rank k W = 2) {ρbar : GaloisRep ℚ k W}
    (hρbar : IsHardlyRamified hℓodd hW ρbar)
    (hirr : ρbar.IsIrreducible)
    (π : O →+* k) (hπsurj : Function.Surjective π)
    (hπ : ∀ (q : ℕ) (hq : q.Prime), q ≠ 2 → q ≠ ℓ →
      (ρ.charFrob hq.toHeightOneSpectrumRingOfIntegersRat).map π =
        ρbar.charFrob hq.toHeightOneSpectrumRingOfIntegersRat)
    (F : Type u) [Field F] [NumberField F]
    (hFtr : NumberField.IsTotallyReal F) (hFgal : IsGalois ℚ F)
    (hirrF : (ρbar.map (algebraMap ℚ F)).IsIrreducible)
    (E : Type u) [Field E] [NumberField E]
    (badF : Finset (HeightOneSpectrum (NumberField.RingOfIntegers F)))
    (heckeF : HeightOneSpectrum (NumberField.RingOfIntegers F) →
      Polynomial E)
    (ψℓ : E →+* AlgebraicClosure ℚ_[ℓ])
    (ιO : O →+* AlgebraicClosure ℚ_[ℓ]) (hιO : Function.Injective ιO)
    (hmod : ∀ w ∉ badF,
      ((ρ.map (algebraMap ℚ F)).charFrob w).map ιO =
        (heckeF w).map ψℓ)
    (hbad2 : ∀ w : HeightOneSpectrum (NumberField.RingOfIntegers F),
      (2 : NumberField.RingOfIntegers F) ∈ w.asIdeal → w ∈ badF)
    (hbad3 : ∀ w : HeightOneSpectrum (NumberField.RingOfIntegers F),
      (3 : NumberField.RingOfIntegers F) ∈ w.asIdeal → w ∈ badF)
    (hbadℓ : ∀ w : HeightOneSpectrum (NumberField.RingOfIntegers F),
      (ℓ : NumberField.RingOfIntegers F) ∈ w.asIdeal → w ∈ badF)
    (D : Type u) [DivisionRing D] [Algebra F D]
    [_root_.IsQuaternionAlgebra F D]
    [_root_.IsQuaternionAlgebra.IsTotallyDefinite F D]
    [_root_.IsQuaternionAlgebra.NumberField.WithRigidification F D] :
    ∃ (p : ℕ) (𝒮 : _root_.TotallyDefiniteQuaternionAlgebra.U₁Data F E p)
      (θ : _root_.TotallyDefiniteQuaternionAlgebra.HeckeAlgebra D 𝒮 →ₐ[E] E),
      ∀ (w : HeightOneSpectrum (NumberField.RingOfIntegers F))
        (hwS : w ∉ 𝒮.S) (hwQ : w ∉ 𝒮.Q), w ∉ badF →
        (heckeF w).coeff 1 =
          -θ (_root_.TotallyDefiniteQuaternionAlgebra.HeckeAlgebra.T D 𝒮 w hwS hwQ) := by
  haveI : NumberField.IsTotallyReal F := hFtr
  -- The auxiliary prime of the level datum: NOT part of the correspondence.
  obtain ⟨p, hp, hcyc⟩ := exists_prime_two_lt_finrank_cyclotomicField F
  -- Jacquet–Langlands proper, as an eigenform at the minimal level `U₁(S, ∅)`.
  obtain ⟨𝒮, a, f, hQ, hf0, hTa, hmatch⟩ :=
    exists_eigenform_of_totallyDefinite_quaternionAlgebra hℓodd hℓ5 hZinj hrank hρ hW hρbar
      hirr π hπsurj hπ F hFtr hFgal hirrF E badF heckeF ψℓ ιO hιO hmod hbad2 hbad3 hbadℓ D
      p hp hcyc
  -- `f` is scaled by every element of the Hecke algebra, not merely by the
  -- generators: `T`'s and `U`'s generate, and the `U`'s are vacuous since
  -- `𝒮.Q = ∅`.
  have hall : ∀ T : _root_.TotallyDefiniteQuaternionAlgebra.HeckeAlgebra D 𝒮,
      ∃ e : E, T • f = e • f := by
    intro T
    induction (_root_.TotallyDefiniteQuaternionAlgebra.HeckeAlgebra.adjoin_T_U_eq_top ..).ge
      (Set.mem_univ T) using Algebra.adjoin_induction with
    | mem x hx =>
        obtain ⟨v, hvS, hvQ, rfl⟩ | ⟨v, hvQ, α, hα, rfl⟩ := hx
        · exact ⟨a v, by
            rw [_root_.TotallyDefiniteQuaternionAlgebra.HeckeAlgebra.T_smul_def]
            exact hTa v hvS⟩
        · rw [hQ] at hvQ; simp at hvQ
    | algebraMap s => exact ⟨s, algebraMap_smul _ _ _⟩
    | add x y _ _ hx hy =>
        obtain ⟨ex, hx⟩ := hx; obtain ⟨ey, hy⟩ := hy
        exact ⟨ex + ey, by rw [add_smul, hx, hy, add_smul]⟩
    | mul x y _ _ hx hy =>
        obtain ⟨ex, hx⟩ := hx; obtain ⟨ey, hy⟩ := hy
        exact ⟨ex * ey, by rw [mul_smul, hy, smul_comm, hx, smul_smul, mul_comm]⟩
  -- The scaling factor is an `E`-algebra character.
  obtain ⟨θ, hθ⟩ := exists_algHom_of_smul_eq_smul hf0 hall
  refine ⟨p, 𝒮, θ, fun w hwS hwQ hwbad => ?_⟩
  have h1 : _root_.TotallyDefiniteQuaternionAlgebra.HeckeAlgebra.T D 𝒮 w hwS hwQ • f
      = a w • f := by
    rw [_root_.TotallyDefiniteQuaternionAlgebra.HeckeAlgebra.T_smul_def]
    exact hTa w hwS
  rw [hθ _ _ h1]
  exact hmatch w hwS hwbad

/-- **STEP 1 of the Carayol node — JACQUET–LANGLANDS: the Hilbert
eigensystem `(E, heckeF)` is seen by a TOTALLY DEFINITE quaternion
algebra over `F`** (PROVEN assembly since 2026-07-27 over the two leaves
`exists_totallyDefinite_rigidified_quaternionAlgebra_of_even` (STEP 1a,
Albert–Brauer–Hasse–Noether) and
`exists_heckeCharacter_of_totallyDefinite_quaternionAlgebra` (STEP 1b,
Jacquet–Langlands proper), declared immediately above; HOISTED 2026-07-27
out of the body of `carayol_threeadic_realization_of_heckePackage`, where
it lived as the internal `have hJL` — an internal `have` cannot be owned or
dispatched at, so the two steps of that node now have names of their own
and the node itself is a PROVEN assembly).

Content. `[F : ℚ]` is EVEN (`hFeven`), so by Albert–Brauer–Hasse–Noether
there is a quaternion division algebra `D/F` ramified at exactly the
infinite places — the ramification set of a quaternion algebra over a
number field is any set of even cardinality, and here it is the set of
infinite places, of cardinality `[F : ℚ]` since `F` is totally real. Such
a `D` is totally definite and SPLIT AT EVERY FINITE PLACE, hence carries a
rigidification `D ⊗_F 𝔸_F^∞ ≅ M₂(𝔸_F^∞)`, which is exactly the datum
`IsQuaternionAlgebra.NumberField.WithRigidification` that the vendored
automorphic development runs on. Jacquet–Langlands then transfers the
Hilbert-newform eigensystem underlying `(E, heckeF)` to a weight-`2`
automorphic form on `Dˣ`, i.e. to an `E`-algebra CHARACTER `θ` of the
Hecke algebra `TotallyDefiniteQuaternionAlgebra.HeckeAlgebra D 𝒮`, whose
`T_w`-eigenvalue is the trace `a_w = -(heckeF w).coeff 1` of the Hecke
polynomial at every good `w`. Automorphy of `(E, heckeF)` itself is
supplied by `hmod` together with the cuspidality proxy `hirrF`; the
RESIDUAL FAITHFULNESS GAP that leaves is stated in the consumer's
docstring and is unchanged by this hoist.

`hFeven` IS CONSUMED HERE AND NOWHERE ELSE in the node. The sibling
`carayol_threeadic_of_totallyDefinite_heckeCharacter` deliberately does not
take it, which makes that division of labour mechanically visible rather
than merely asserted in a comment.

DEFINITENESS IS NOW PINNED — a RETRACTION of the consumer's own docstring
(2026-07-27). That docstring's "JACQUET–LANGLANDS CONSUMER" block, item
(3), recorded that "the vendored development has NO `IsTotallyDefinite`
predicate — definiteness is a source COMMENT there ... so any clause
asserting something about an ARBITRARY rigidified `D` would be false", and
concluded that "nothing in the formal statement PINS the witnessing `D` to
be totally definite, so a future owner discharging STEP 1 must supply
definiteness from outside the formalism (or add the predicate)". That was
true of the REFERENCE project's `AutomorphicForm/` sources and it is FALSE
of this tree: the vendored
`Fermat/FLT/Mathlib/Algebra/IsQuaternionAlgebra.lean` defines the class
`IsQuaternionAlgebra.IsTotallyDefinite F D` (`ℝ ⊗_{F,v} D ≃ₐ[ℝ] ℍ` at every
REAL place `v`, and a totally real `F` has only real places), and
`AutomorphicForm/QuaternionAlgebra/Basic.lean` and
`.../HeckeOperators/Concrete.lean` already consume it as an instance
hypothesis. So the existential below CARRIES it, the witnessing `D` is
genuinely pinned totally definite, and the successor task the consumer
recorded is discharged rather than deferred. Refuting check, one line:
`grep -rn 'class IsTotallyDefinite' Fermat/`.

THE TWO HALVES ARE NOW SPLIT (2026-07-27), and this node proves nothing
itself — it is `obtain`, `obtain`, `exact`:

* the EXISTENCE half is `exists_totallyDefinite_rigidified_quaternionAlgebra_of_even`
  — a quaternion division algebra over `F` ramified exactly at the infinite
  places, by the Albert–Brauer–Hasse–Noether exact sequence for the Brauer
  group of a number field (the local invariants may be prescribed
  arbitrarily subject to summing to zero). `hFeven` is the whole of what it
  needs, and it is the ONLY consumer of `hFeven` in the node. A plausible
  in-tree target: class field theory, not automorphic theory;
* the TRANSFER half is `exists_heckeCharacter_of_totallyDefinite_quaternionAlgebra`
  — the Jacquet–Langlands correspondence for `GL₂/F` against `Dˣ`, in the
  direction "cuspidal Hilbert eigensystem of the right weight ⟹ automorphic
  form on the definite `Dˣ` with the same Hecke eigenvalues at the good
  places". A genuine literature citation: Jacquet–Langlands, *Automorphic
  forms on GL(2)*, Lecture Notes in Math. **114** (1970), §14–16; see also
  Carayol 1986 §0.9, which is where the even-degree quaternionic form of
  Théorème (A) comes from in the first place.

The split was impossible while `IsTotallyDefinite` was believed absent,
for the reason the consumer's docstring gives in another guise: the
transfer half quantified over an ARBITRARY rigidified `D` is FALSE
(`M₂(F)` is a rigidified quaternion algebra over every `F`), so the two
halves can only be separated by keeping the definiteness datum on the
BOUNDARY between them. That is exactly what is done: the existence half
produces `IsTotallyDefinite F D` and the transfer half consumes it as an
instance hypothesis, so neither half is false and the join is an `exact`.

CIRCULARITY GUARD (inherited from pillar β, load-bearing): no discharge
through `Family.lean`, `Lift.lean`, or `Modularity/Interface.lean`. -/
theorem exists_totallyDefinite_heckeCharacter_of_heckePackage
    {ℓ : ℕ} (hℓodd : Odd ℓ) [Fact ℓ.Prime] (hℓ5 : 5 ≤ ℓ)
    {O : Type u} [CommRing O] [IsDomain O] [TopologicalSpace O]
    [IsTopologicalRing O] [Algebra ℤ_[ℓ] O] [IsLocalRing O]
    [Module.Finite ℤ_[ℓ] O] [IsModuleTopology ℤ_[ℓ] O]
    (hZinj : Function.Injective (algebraMap ℤ_[ℓ] O))
    {ρ : GaloisRep ℚ O (Fin 2 → O)}
    (hrank : Module.rank O (Fin 2 → O) = 2)
    (hρ : IsHardlyRamified hℓodd hrank ρ)
    {k : Type u} [Field k] [Finite k] [Algebra ℤ_[ℓ] k]
    [TopologicalSpace k] [DiscreteTopology k]
    {W : Type v} [AddCommGroup W] [Module k W] [Module.Finite k W]
    [Module.Free k W]
    (hW : Module.rank k W = 2) {ρbar : GaloisRep ℚ k W}
    (hρbar : IsHardlyRamified hℓodd hW ρbar)
    (hirr : ρbar.IsIrreducible)
    (π : O →+* k) (hπsurj : Function.Surjective π)
    (hπ : ∀ (q : ℕ) (hq : q.Prime), q ≠ 2 → q ≠ ℓ →
      (ρ.charFrob hq.toHeightOneSpectrumRingOfIntegersRat).map π =
        ρbar.charFrob hq.toHeightOneSpectrumRingOfIntegersRat)
    (F : Type u) [Field F] [NumberField F]
    (hFtr : NumberField.IsTotallyReal F) (hFgal : IsGalois ℚ F)
    (hFeven : Even (Module.finrank ℚ F))
    (hirrF : (ρbar.map (algebraMap ℚ F)).IsIrreducible)
    (E : Type u) [Field E] [NumberField E]
    (badF : Finset (HeightOneSpectrum (NumberField.RingOfIntegers F)))
    (heckeF : HeightOneSpectrum (NumberField.RingOfIntegers F) →
      Polynomial E)
    (ψℓ : E →+* AlgebraicClosure ℚ_[ℓ])
    (ιO : O →+* AlgebraicClosure ℚ_[ℓ]) (hιO : Function.Injective ιO)
    (hmod : ∀ w ∉ badF,
      ((ρ.map (algebraMap ℚ F)).charFrob w).map ιO =
        (heckeF w).map ψℓ)
    (hbad2 : ∀ w : HeightOneSpectrum (NumberField.RingOfIntegers F),
      (2 : NumberField.RingOfIntegers F) ∈ w.asIdeal → w ∈ badF)
    (hbad3 : ∀ w : HeightOneSpectrum (NumberField.RingOfIntegers F),
      (3 : NumberField.RingOfIntegers F) ∈ w.asIdeal → w ∈ badF)
    (hbadℓ : ∀ w : HeightOneSpectrum (NumberField.RingOfIntegers F),
      (ℓ : NumberField.RingOfIntegers F) ∈ w.asIdeal → w ∈ badF) :
    ∃ (D : Type u) (_ : DivisionRing D) (_ : Algebra F D)
      (_ : _root_.IsQuaternionAlgebra F D)
      (_ : _root_.IsQuaternionAlgebra.IsTotallyDefinite F D)
      (_ : _root_.IsQuaternionAlgebra.NumberField.WithRigidification F D)
      (p : ℕ) (𝒮 : _root_.TotallyDefiniteQuaternionAlgebra.U₁Data F E p)
      (θ : _root_.TotallyDefiniteQuaternionAlgebra.HeckeAlgebra D 𝒮 →ₐ[E] E),
      ∀ (w : HeightOneSpectrum (NumberField.RingOfIntegers F))
        (hwS : w ∉ 𝒮.S) (hwQ : w ∉ 𝒮.Q), w ∉ badF →
        (heckeF w).coeff 1 =
          -θ (_root_.TotallyDefiniteQuaternionAlgebra.HeckeAlgebra.T D 𝒮 w hwS hwQ) := by
  -- STEP 1a — ALBERT–BRAUER–HASSE–NOETHER, the ONLY consumer of `hFeven`:
  -- a totally definite quaternion division algebra over `F`, split at every
  -- finite place, hence carrying a rigidification.
  obtain ⟨D, hDdiv, hDalg, hDquat, hDdef, ⟨hDrig⟩⟩ :=
    exists_totallyDefinite_rigidified_quaternionAlgebra_of_even F hFtr hFeven
  -- STEP 1b — JACQUET–LANGLANDS proper, against that `D`. The definiteness
  -- datum `hDdef` produced above is what keeps this half from being false.
  obtain ⟨p, 𝒮, θ, hθ⟩ :=
    exists_heckeCharacter_of_totallyDefinite_quaternionAlgebra hℓodd hℓ5 hZinj hrank hρ
      hW hρbar hirr π hπsurj hπ F hFtr hFgal hirrF E badF heckeF ψℓ ιO hιO hmod
      hbad2 hbad3 hbadℓ D
  exact ⟨D, hDdiv, hDalg, hDquat, hDdef, hDrig, p, 𝒮, θ, hθ⟩

/-- **The module topology on a finite-dimensional `ℚ_p`-algebra is a ring
topology** (PROVEN, 2026-07-27): the exact mirror of
`isTopologicalRing_moduleTopology_of_finite` one level up the tower, over the
FIELD `ℚ_p` rather than over `ℤ_p`.

It exists for the same reason the `ℤ_p`-version does: the field form of the
Carayol citation (`exists_threeadicField_realization_of_totallyDefinite_heckeCharacter`
below) must be able to say `GaloisRep F L (Fin 2 → L)` without asserting a
topology on `L` as a component of the citation. The topology is not a choice —
`Module.Finite ℚ_p L` pins it to the module topology — so both
`IsTopologicalRing` and `IsModuleTopology` are theorems there rather than
assumptions. -/
theorem isTopologicalRing_moduleTopology_of_finite_padic (p : ℕ) [Fact p.Prime]
    (L : Type*) [CommRing L] [Algebra ℚ_[p] L] [Module.Finite ℚ_[p] L] :
    letI := moduleTopology ℚ_[p] L
    IsTopologicalRing L :=
  letI := moduleTopology ℚ_[p] L
  IsModuleTopology.isTopologicalRing ℚ_[p] L

/-! #### The Eichler–Shimura cut of STEP 2a (2026-07-27)

`exists_threeadicField_realization_of_totallyDefinite_heckeCharacter` was a
single sorry carrying the whole of Carayol 1986 §0.9–0.11. The pin has NO
Shimura curves, NO étale cohomology, NO Hilbert modular forms and NO
automorphic forms on an INDEFINITE quaternion algebra (refuting checks, run
2026-07-27 over `Fermat/`, each returning nothing but prose:
`grep -rn 'ShimuraCurve\|ShimuraVariety' --include=*.lean Fermat/`,
`grep -rniE 'etale[A-Za-z]*cohomolog|EtaleSite|SheafCohomology' --include=*.lean Fermat/`,
`grep -rn 'HilbertModularForm' --include=*.lean Fermat/`,
`grep -rn 'IsIndefinite' --include=*.lean Fermat/`. Note the FIRST of these
must be spelled with the full name: a bare `grep Shimura` hits
`EichlerShimuraPackage` in `Interface.lean`, which is a Tate-module carrier
for GL₂/ℚ and not a curve.) So the quaternionic Shimura curve enters as an
INTERFACE STRUCTURE, `CarayolPackage`, in exactly the style
`Modularity/Interface.lean` already uses for the GL₂/ℚ analogue
(`EichlerShimuraPackage`, five successive decompositions of the attachment
leaf `exists_galoisRep_charFrob_of_weightTwoNewform`): its fields are the
classically-true cited facts about the `λ`-adic cohomology of the Shimura
curve that the classical proof consumes, and everything from those facts to
the STEP 2a statement is PROVEN here.

The toolkit below (`Carayol.jointEigenspace`, `Carayol.compressEnd`,
`Carayol.eq_quadratic_of_monic_natDegree_two`) is a PLACE-INDEXED
re-development of `Interface.lean`'s prime-indexed
`heckeEigenspace`/`compressEnd`/`eq_quadratic_of_monic_natDegree_two`. The
duplication is forced, not chosen: `Interface.lean` IMPORTS this module, so
its copies are downstream and unusable here, and this node's CIRCULARITY
GUARD forbids discharge through it in any case. It is deliberately stated
over an ARBITRARY index type `ι` and an arbitrary index subset `S`, so that
`Interface.lean`'s `ℕ`-indexed versions can later be replaced by
instantiations of these rather than the reverse; that hoist is a separate,
purely mechanical task and is NOT attempted here (it would edit another
owner's region of a 60k-line file).

`compressEnd` is the load-bearing device and the reason a bare restriction
will not do: the compressed representation must be CONTINUOUS for the module
topologies, and the module topology sees LINEAR maps
(`IsModuleTopology.continuous_of_linearMap`) while a restriction to an
abstract submodule has no continuity API. Compression is linear on the whole
endomorphism algebra and multiplicative only on the stabiliser of the
subspace (`compressEnd_mul`), which is exactly enough. -/

namespace Carayol

section JointEigenspace

variable {A : Type*} [CommRing A] {V₀ : Type*} [AddCommGroup V₀] [Module A V₀]
  {ι : Type*}

/-- The joint eigenspace of a family `t` of commuting operators indexed by
`ι`, taken over the index subset `S`, for the eigenvalue system `a`: the
intersection over `i ∈ S` of `ker (t i − a i)`. For the `CarayolPackage`
below this carves the `θ`-eigencomponent of the eigensystem out of the
`λ`-adic cohomology of the Shimura curve. -/
def jointEigenspace (S : Set ι) (t : ι → Module.End A V₀) (a : ι → A) :
    Submodule A V₀ :=
  ⨅ (i : ι) (_ : i ∈ S), LinearMap.ker (t i - a i • (1 : Module.End A V₀))

/-- Membership in `jointEigenspace`: a simultaneous eigenvector at every
index in `S`. -/
theorem mem_jointEigenspace_iff {S : Set ι} {t : ι → Module.End A V₀}
    {a : ι → A} {x : V₀} :
    x ∈ jointEigenspace S t a ↔ ∀ i ∈ S, t i x = a i • x := by
  simp [jointEigenspace, Submodule.mem_iInf, LinearMap.mem_ker,
    LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, sub_eq_zero]

end JointEigenspace

section CompressEnd

variable {A : Type*} [CommRing A] {V₀ : Type*} [AddCommGroup V₀]
    [Module A V₀] {n : ℕ} (W : Submodule A V₀) (πW : V₀ →ₗ[A] W)
    (e : W ≃ₗ[A] (Fin n → A))

/-- Compression of an endomorphism of `V₀` to the standard frame of a
distinguished subspace `W`, through a chosen projection `πW` and a chosen
frame `e`. As a map of endomorphism ALGEBRAS it is only multiplicative on the
stabiliser of `W` (`compressEnd_mul`), but as a LINEAR map it is everywhere
defined — which is what makes the compressed Galois representation of the
Carayol assembly continuous for the module topologies. -/
def compressEnd :
    Module.End A V₀ →ₗ[A] Module.End A (Fin n → A) where
  toFun φ :=
    e.toLinearMap ∘ₗ πW ∘ₗ φ ∘ₗ W.subtype ∘ₗ e.symm.toLinearMap
  map_add' φ ψ := by ext x; simp
  map_smul' c φ := by ext x; simp

/-- Evaluation of the compression. -/
theorem compressEnd_apply (φ : Module.End A V₀) (x : Fin n → A) :
    compressEnd W πW e φ x = e (πW (φ ↑(e.symm x))) := rfl

/-- The compression sends the identity to the identity, given that `πW`
retracts the inclusion of `W`. -/
theorem compressEnd_one (hπ : ∀ w : W, πW (w : V₀) = w) :
    compressEnd W πW e 1 = 1 := by
  refine LinearMap.ext fun x => ?_
  rw [compressEnd_apply, Module.End.one_apply, hπ (e.symm x),
    LinearEquiv.apply_symm_apply, Module.End.one_apply]

/-- The compression is multiplicative when the right factor stabilises
`W`. -/
theorem compressEnd_mul (hπ : ∀ w : W, πW (w : V₀) = w)
    (φ ψ : Module.End A V₀) (hψ : ∀ x ∈ W, ψ x ∈ W) :
    compressEnd W πW e (φ * ψ) =
      compressEnd W πW e φ * compressEnd W πW e ψ := by
  refine LinearMap.ext fun x => ?_
  simp only [Module.End.mul_apply, compressEnd_apply,
    LinearEquiv.symm_apply_apply]
  have hmem : ψ ↑(e.symm x) ∈ W := hψ _ (SetLike.coe_mem (e.symm x))
  have hproj : πW (ψ ↑(e.symm x)) = ⟨ψ ↑(e.symm x), hmem⟩ :=
    hπ ⟨_, hmem⟩
  rw [hproj]

/-- The compression of an operator acting on `W` as the scalar `c` is the
scalar `c`. -/
theorem compressEnd_eq_smul_one (hπ : ∀ w : W, πW (w : V₀) = w)
    {φ : Module.End A V₀} {c : A} (hφ : ∀ x ∈ W, φ x = c • x) :
    compressEnd W πW e φ = c • 1 := by
  refine LinearMap.ext fun x => ?_
  rw [compressEnd_apply, hφ _ (SetLike.coe_mem (e.symm x)), map_smul,
    hπ (e.symm x), map_smul, LinearEquiv.apply_symm_apply,
    LinearMap.smul_apply, Module.End.one_apply]

/-- On the stabiliser of `W` the compression is conjugation of the
restriction by the frame — the bridge to `LinearMap.det_conj` for the
determinant transport of the Carayol assembly. -/
theorem compressEnd_eq_conj_restrict (hπ : ∀ w : W, πW (w : V₀) = w)
    {φ : Module.End A V₀} (hφ : ∀ x ∈ W, φ x ∈ W) :
    compressEnd W πW e φ =
      (e : W →ₗ[A] (Fin n → A)) ∘ₗ φ.restrict hφ ∘ₗ
        (e.symm : (Fin n → A) →ₗ[A] W) := by
  refine LinearMap.ext fun x => ?_
  simp only [compressEnd_apply, LinearMap.comp_apply,
    LinearEquiv.coe_coe, LinearMap.restrict_apply]
  exact congrArg e
    (hπ ⟨φ ↑(e.symm x), hφ _ (SetLike.coe_mem (e.symm x))⟩)

end CompressEnd

/-- Quadratic decomposition of a monic degree-2 polynomial (PROVEN glue):
`P = X² + P₁·X + P₀`. Applied to the Frobenius characteristic polynomial and
to the target Hecke polynomial, it turns the coefficientwise information the
Cayley–Hamilton comparison produces into the polynomial identity STEP 2a
demands. The `map`-flavoured companion is
`map_eq_quadratic_of_monic_natDegree_two` above; this is the identity-map
case, stated separately because going through `Polynomial.map_id` costs a
rewrite that `simp` would have to be trusted with (and the project simp set
contains sorried lemmas). -/
theorem eq_quadratic_of_monic_natDegree_two {A : Type*} [CommRing A]
    {p : Polynomial A} (hm : p.Monic) (hd : p.natDegree = 2) :
    p = X ^ 2 + C (p.coeff 1) * X + C (p.coeff 0) := by
  ext n
  match n with
  | 0 => simp
  | 1 => simp
  | 2 =>
      have h2 : p.coeff 2 = 1 := by
        have hlc := hm.coeff_natDegree
        rwa [hd] at hlc
      simp [h2, Polynomial.coeff_X_pow]
  | (m + 3) =>
      have hzero : p.coeff (m + 3) = 0 :=
        Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
      simp [hzero, Polynomial.coeff_X_pow]

end Carayol

open Carayol in
/-- **The quaternionic Shimura-curve package at a place `λ` of `E`** — the
carrier through which Carayol's Théorème (A) enters this development
(2026-07-27, the Eichler–Shimura cut of STEP 2a).

The intended inhabitant is Carayol 1986 §0.10–0.11: `Vlam` is the `λ`-adic
étale cohomology `H¹(M_K ⊗_F F̄, ℱ_λ)` of the Shimura curve `M_K` attached to
a quaternion algebra over `F` split at exactly one infinite place, `tauJ` is
its continuous `Γ_F`-action, `hecke` are the Hecke correspondences, and
`badF` is the exceptional set. Each field is a classically-true cited
assertion about that inhabitant:

* `hecke_comm` — the Hecke correspondences are defined over `F`, hence
  commute with the whole Galois action;
* `congruence` — the EICHLER–SHIMURA congruence relation at a good place:
  `Frob_w² − T_w·Frob_w + N(w) = 0` on the cohomology (the constant is
  written `(P w).coeff 0`, which for the intended inhabitant IS `N(w)`);
* `rank_eigenspace` — MULTIPLICITY ONE: the joint `θ`-eigenspace of the
  Hecke operators is 2-dimensional;
* `det_frob` — the Weil-pairing determinant: `det Frob_w = N(w)` on that
  eigenspace.

`P` is the family of target Hecke polynomials, carried as a PARAMETER rather
than built from `N(w)` and an eigenvalue system: that keeps the whole
integrality/normalisation bookkeeping (`P w` monic of degree `2`, constant
coefficient `N(w)`) inside the package, where it is a fact about the
inhabitant, instead of forcing the consumer to re-derive the shape of
`heckeF w` from `hmod` and the cyclotomic determinant.

FORMAL-CONTENT AUDIT, and it must not be skipped by anyone reading this as a
reduction. **`Nonempty (CarayolPackage F L badF P)` is EQUIVALENT to the
conclusion of STEP 2a over the same `L` and `P`, not weaker than it.** One
direction is `exists_galoisRep_charFrob_of_carayolPackage` below. For the
other, the explicit witness — checked by hand, deliberately NOT committed as
a declaration since nothing would consume it and it would be free-floating —
is: given `τ : GaloisRep F L (Fin 2 → L)` with `τ.charFrob w = P w`, take
`Vlam := Fin 2 → L`, `tauJ := τ`, `hecke w := (-(P w).coeff 1) • 1`. Then
`hecke_comm` is commutation with a scalar, `congruence` is Cayley–Hamilton
(`LinearMap.aeval_self_charpoly`) for `τ (globalFrob w)`, the joint
eigenspace of a family of scalars is everything so `rank_eigenspace` is
`hfr2`, and `det_frob` is `LinearMap.det_eq_sign_charpoly_coeff`.

So this cut RELOCATES the citation rather than shrinking it, and the honest
statement of what it buys is this: the derivation *Eichler–Shimura relation +
multiplicity one + Weil-pairing determinant ⟹ the Frobenius characteristic
polynomial is the Hecke polynomial* — which is the entire content of the
classical argument once the cohomology is in hand — is now MACHINE-CHECKED
instead of assumed, and what remains to be believed is stated in the
vocabulary of the object Carayol actually constructs. That is the same trade
`Interface.lean` took for `EichlerShimuraPackage`, whose own inhabitation is
likewise equivalent-plus-one-field to the attachment statement it feeds.

THE NEXT CUT, recorded so the next owner does not have to find it: follow
`Interface.lean`'s `ModularJacobianPackage`, i.e. replace `rank_eigenspace`
(multiplicity one, a spectral fact) by sharper `θ`-independent module theory
— freeness of `Vlam` of rank `2` over the subalgebra generated by `hecke`,
plus a nonzero idempotent cutting out the `θ`-eigensystem — and PROVE
`rank_eigenspace` from it. That is a genuine reduction rather than a
relocation, and `Interface.lean` carries the proven coordinate lemmas
(`exists_ne_zero_mem_heckeEigenspace_of_free`, `mem_heckeEigenspace_of_free`)
that do it, which would have to be re-developed here for the same
circularity reason as the toolkit above. -/
structure CarayolPackage
    (F : Type u) [Field F] [NumberField F]
    (L : Type u) [Field L] [TopologicalSpace L] [IsTopologicalRing L]
    (badF : Finset (HeightOneSpectrum (NumberField.RingOfIntegers F)))
    (P : HeightOneSpectrum (NumberField.RingOfIntegers F) → Polynomial L) where
  /-- The Galois module: intended `H¹(M_K ⊗_F F̄, ℱ_λ)`. -/
  Vlam : Type u
  [addCommGroup : AddCommGroup Vlam]
  [module : Module L Vlam]
  [moduleFinite : Module.Finite L Vlam]
  /-- The continuous Galois action on the cohomology. -/
  tauJ : GaloisRep F L Vlam
  /-- The Hecke correspondences, acting on the cohomology. -/
  hecke : HeightOneSpectrum (NumberField.RingOfIntegers F) → Module.End L Vlam
  /-- The Hecke correspondences are defined over `F`, so they commute with
  the whole Galois action. -/
  hecke_comm : ∀ (w : HeightOneSpectrum (NumberField.RingOfIntegers F))
    (γ : Field.absoluteGaloisGroup F), hecke w * tauJ γ = tauJ γ * hecke w
  /-- The target Hecke polynomial is monic … -/
  monic : ∀ w ∉ badF, (P w).Monic
  /-- … of degree two. -/
  natDegree_eq : ∀ w ∉ badF, (P w).natDegree = 2
  /-- The Eichler–Shimura congruence relation at a good place:
  `Frob_w² − T_w·Frob_w + N(w) = 0`. -/
  congruence : ∀ w ∉ badF,
    tauJ (globalFrob w) ^ 2 - hecke w * tauJ (globalFrob w)
      + (P w).coeff 0 • 1 = 0
  /-- Multiplicity one: the joint eigenspace of the Hecke operators for the
  eigensystem `w ↦ −(P w).coeff 1` is 2-dimensional. -/
  rank_eigenspace :
    Module.rank L
      (jointEigenspace {w | w ∉ badF} hecke (fun w => -(P w).coeff 1)) = 2
  /-- The Weil-pairing determinant: the Galois determinant on the eigenspace
  is `N(w)` at the `w`-Frobenius. -/
  det_frob : ∀ w ∉ badF,
    ∀ hst : ∀ x ∈ jointEigenspace {w | w ∉ badF} hecke
        (fun w => -(P w).coeff 1),
      tauJ (globalFrob w) x ∈ jointEigenspace {w | w ∉ badF} hecke
        (fun w => -(P w).coeff 1),
    LinearMap.det ((tauJ (globalFrob w)).restrict hst) = (P w).coeff 0

attribute [instance] CarayolPackage.addCommGroup CarayolPackage.module
  CarayolPackage.moduleFinite

open Carayol in
/-- **From the Shimura-curve package to the Galois representation** (PROVEN,
2026-07-27): the `θ`-eigenspace of the `λ`-adic cohomology carries a
continuous 2-dimensional representation of `Γ_F` whose Frobenius
characteristic polynomial at every good place is the target Hecke
polynomial.

This is the whole content of the classical argument once the cohomology is in
hand, and it is the half of Carayol's Théorème (A) that this development
verifies rather than cites. The steps:

1. the eigenspace `W` is `Γ_F`-STABLE, because the Hecke correspondences are
  defined over `F` (`hecke_comm`);
2. `W` is 2-dimensional (`rank_eigenspace`), so it carries a frame
  `e : W ≃ₗ[L] (Fin 2 → L)`; choose a projection `πW` onto it from a
  complement (`Submodule.exists_isCompl`);
3. the compressed map `γ ↦ compressEnd W πW e (tauJ γ)` is a MONOID
  homomorphism, because compression is multiplicative on the stabiliser of
  `W` and every `tauJ γ` stabilises it, and it is CONTINUOUS because
  compression is `L`-LINEAR and the module topology sees linear maps —
  this is why the proof goes through `compressEnd` and not through
  `LinearMap.restrict`, which has no continuity API;
4. on `W` the Hecke operator acts as the scalar `−(P w).coeff 1`, so the
  Eichler–Shimura relation compresses to
  `Φ² + (P w).coeff 1 • Φ + (P w).coeff 0 • 1 = 0`;
5. Cayley–Hamilton (`LinearMap.aeval_self_charpoly`) gives the same identity
  with the charpoly's own coefficients; the constant terms agree by
  `det_frob` and `LinearMap.det_eq_sign_charpoly_coeff`, so the difference is
  `(c₁ − (P w).coeff 1) • Φ = 0`, and `Φ` is INVERTIBLE (it is the
  compression of a group element, and compression is multiplicative on the
  stabiliser), so the scalar vanishes;
6. both polynomials are monic of degree `2`, so agreeing in both
  coefficients makes them equal (`eq_quadratic_of_monic_natDegree_two`).

Step 5's invertibility is where the argument would fail for a general
operator: it is exactly what turns "annihilated by two monic quadratics with
equal constant terms" into "equal linear terms". -/
theorem exists_galoisRep_charFrob_of_carayolPackage
    {F : Type u} [Field F] [NumberField F]
    {L : Type u} [Field L] [TopologicalSpace L] [IsTopologicalRing L]
    {badF : Finset (HeightOneSpectrum (NumberField.RingOfIntegers F))}
    {P : HeightOneSpectrum (NumberField.RingOfIntegers F) → Polynomial L}
    (C : CarayolPackage F L badF P) :
    ∃ τ : GaloisRep F L (Fin 2 → L), ∀ w ∉ badF, τ.charFrob w = P w := by
  classical
  set W : Submodule L C.Vlam :=
    jointEigenspace {w | w ∉ badF} C.hecke (fun w => -(P w).coeff 1) with hWdef
  -- 1. Galois stability of the eigenspace (rationality of the Hecke
  -- correspondences)
  have hstab : ∀ γ : Field.absoluteGaloisGroup F, ∀ x ∈ W, C.tauJ γ x ∈ W := by
    intro γ x hx
    rw [hWdef, mem_jointEigenspace_iff] at hx ⊢
    intro w hw
    have hcomm := LinearMap.congr_fun (C.hecke_comm w γ) x
    rw [Module.End.mul_apply, Module.End.mul_apply, hx w hw, map_smul] at hcomm
    exact hcomm
  -- 2. the eigenspace is 2-dimensional; frame it, and pick a projection
  have hfrW : Module.finrank L W = 2 :=
    Module.finrank_eq_of_rank_eq (by exact_mod_cast C.rank_eigenspace)
  let e : W ≃ₗ[L] (Fin 2 → L) := (Module.finBasisOfFinrankEq L W hfrW).equivFun
  obtain ⟨W', hWc⟩ := Submodule.exists_isCompl W
  let πW : C.Vlam →ₗ[L] W := Submodule.projectionOnto W W' hWc
  have hπ : ∀ w : W, πW (w : C.Vlam) = w := fun w =>
    Submodule.projectionOnto_apply_left hWc w
  -- 3. module topologies on the two endomorphism algebras, and continuity of
  -- the compression
  letI : TopologicalSpace (Module.End L C.Vlam) := moduleTopology L _
  haveI : IsModuleTopology L (Module.End L C.Vlam) := ⟨rfl⟩
  letI : TopologicalSpace (Module.End L (Fin 2 → L)) := moduleTopology L _
  haveI : IsModuleTopology L (Module.End L (Fin 2 → L)) := ⟨rfl⟩
  haveI := IsModuleTopology.toContinuousAdd L (Module.End L (Fin 2 → L))
  have hτc : Continuous fun γ : Field.absoluteGaloisGroup F => C.tauJ γ :=
    ContinuousMonoidHom.continuous_toFun C.tauJ
  have hΛc : Continuous (compressEnd W πW e) :=
    IsModuleTopology.continuous_of_linearMap _
  have hcont : Continuous fun γ : Field.absoluteGaloisGroup F =>
      compressEnd W πW e (C.tauJ γ) := hΛc.comp hτc
  let τmh : Field.absoluteGaloisGroup F →* Module.End L (Fin 2 → L) :=
    { toFun := fun γ => compressEnd W πW e (C.tauJ γ)
      map_one' := by
        show compressEnd W πW e (C.tauJ 1) = 1
        rw [map_one]
        exact compressEnd_one W πW e hπ
      map_mul' := fun γ δ => by
        show compressEnd W πW e (C.tauJ (γ * δ)) =
          compressEnd W πW e (C.tauJ γ) * compressEnd W πW e (C.tauJ δ)
        rw [map_mul]
        exact compressEnd_mul W πW e hπ _ _ (hstab δ) }
  let τ' : GaloisRep F L (Fin 2 → L) := ⟨τmh, hcont⟩
  refine ⟨τ', fun w hw => ?_⟩
  rw [GaloisRep.charFrob_eq_charpoly_globalFrob]
  have happ : τ' (globalFrob w) = compressEnd W πW e (C.tauJ (globalFrob w)) :=
    rfl
  rw [happ]
  -- the compressed Frobenius is invertible …
  have hinv : compressEnd W πW e (C.tauJ (globalFrob w)) *
      compressEnd W πW e (C.tauJ ((globalFrob w)⁻¹)) = 1 := by
    rw [← compressEnd_mul W πW e hπ _ _ (hstab _), ← map_mul,
      mul_inv_cancel, map_one]
    exact compressEnd_one W πW e hπ
  -- 4. … the Hecke operator acts on the eigenspace as its eigenvalue …
  have hΛt : compressEnd W πW e (C.hecke w) = (-(P w).coeff 1) • 1 :=
    compressEnd_eq_smul_one W πW e hπ fun x hx =>
      mem_jointEigenspace_iff.mp hx w hw
  have hcong := C.congruence w hw
  have hQ : compressEnd W πW e (C.tauJ (globalFrob w)) ^ 2
      - (-(P w).coeff 1) • compressEnd W πW e (C.tauJ (globalFrob w))
      + (P w).coeff 0 • 1 = 0 := by
    have h₀ : compressEnd W πW e (C.tauJ (globalFrob w) ^ 2)
        - compressEnd W πW e (C.hecke w * C.tauJ (globalFrob w))
        + (P w).coeff 0 • compressEnd W πW e 1 = 0 := by
      rw [← map_smul, ← map_sub, ← map_add, hcong, map_zero]
    rw [pow_two, compressEnd_mul W πW e hπ _ _ (hstab _),
      compressEnd_mul W πW e hπ _ _ (hstab _), hΛt,
      compressEnd_one W πW e hπ, smul_mul_assoc, one_mul, ← pow_two] at h₀
    exact h₀
  -- … and has determinant `(P w).coeff 0` by the Weil pairing
  have hdet : LinearMap.det (compressEnd W πW e (C.tauJ (globalFrob w))) =
      (P w).coeff 0 := by
    rw [compressEnd_eq_conj_restrict W πW e hπ (hstab _), LinearMap.det_conj]
    exact C.det_frob w hw (hstab _)
  -- 5. Cayley–Hamilton against the congruence pins the charpoly
  have hfr2 : Module.finrank L (Fin 2 → L) = 2 := by simp
  have hmon : (compressEnd W πW e (C.tauJ (globalFrob w))).charpoly.Monic :=
    LinearMap.charpoly_monic _
  have hdeg : (compressEnd W πW e (C.tauJ (globalFrob w))).charpoly.natDegree
      = 2 := by
    rw [LinearMap.charpoly_natDegree]
    exact hfr2
  have hP2 := eq_quadratic_of_monic_natDegree_two hmon hdeg
  have hc0 : (compressEnd W πW e (C.tauJ (globalFrob w))).charpoly.coeff 0
      = (P w).coeff 0 := by
    have hsign := LinearMap.det_eq_sign_charpoly_coeff
      (compressEnd W πW e (C.tauJ (globalFrob w)))
    rw [hfr2, hdet] at hsign
    have hpow : ((-1 : L)) ^ 2 *
        (compressEnd W πW e (C.tauJ (globalFrob w))).charpoly.coeff 0 =
        (compressEnd W πW e (C.tauJ (globalFrob w))).charpoly.coeff 0 := by
      ring
    rw [hpow] at hsign
    exact hsign.symm
  have hCH := LinearMap.aeval_self_charpoly
    (compressEnd W πW e (C.tauJ (globalFrob w)))
  rw [hP2] at hCH
  simp only [map_add, map_mul, map_pow, Polynomial.aeval_X,
    Polynomial.aeval_C, Algebra.algebraMap_eq_smul_one,
    smul_mul_assoc, one_mul] at hCH
  rw [hc0] at hCH
  have hsub : ((compressEnd W πW e (C.tauJ (globalFrob w))).charpoly.coeff 1
      + -(P w).coeff 1) • compressEnd W πW e (C.tauJ (globalFrob w)) = 0 := by
    have hmod : ((compressEnd W πW e (C.tauJ (globalFrob w))).charpoly.coeff 1
        + -(P w).coeff 1) • compressEnd W πW e (C.tauJ (globalFrob w)) =
        (compressEnd W πW e (C.tauJ (globalFrob w)) ^ 2
          + (compressEnd W πW e (C.tauJ (globalFrob w))).charpoly.coeff 1
            • compressEnd W πW e (C.tauJ (globalFrob w))
          + (P w).coeff 0 • 1)
        - (compressEnd W πW e (C.tauJ (globalFrob w)) ^ 2
          - (-(P w).coeff 1) • compressEnd W πW e (C.tauJ (globalFrob w))
          + (P w).coeff 0 • 1) := by
      rw [add_smul]
      abel
    rw [hmod, hCH, hQ, sub_zero]
  have hone : ((compressEnd W πW e (C.tauJ (globalFrob w))).charpoly.coeff 1
      + -(P w).coeff 1) • (1 : Module.End L (Fin 2 → L)) = 0 := by
    have h2 : ((compressEnd W πW e (C.tauJ (globalFrob w))).charpoly.coeff 1
        + -(P w).coeff 1) •
        (compressEnd W πW e (C.tauJ (globalFrob w)) *
          compressEnd W πW e (C.tauJ ((globalFrob w)⁻¹))) = 0 := by
      rw [← smul_mul_assoc, hsub, zero_mul]
    rwa [hinv] at h2
  have hker : ((compressEnd W πW e (C.tauJ (globalFrob w))).charpoly.coeff 1
      + -(P w).coeff 1) • (Pi.single (0 : Fin 2) (1 : L) : Fin 2 → L) = 0 := by
    have h3 := congrArg (fun ψ : Module.End L (Fin 2 → L) =>
      ψ (Pi.single (0 : Fin 2) (1 : L))) hone
    simpa using h3
  have hc1 : (compressEnd W πW e (C.tauJ (globalFrob w))).charpoly.coeff 1
      = -(-(P w).coeff 1) := by
    rcases smul_eq_zero.mp hker with h | h
    · exact add_eq_zero_iff_eq_neg.mp h
    · have h4 : (1 : L) = 0 := by simpa using congrFun h 0
      exact absurd h4 one_ne_zero
  -- 6. two monic quadratics agreeing in both coefficients are equal
  rw [hP2, hc1, hc0, neg_neg]
  exact (eq_quadratic_of_monic_natDegree_two (C.monic w hw)
    (C.natDegree_eq w hw)).symm

/-- **STEP 2a′ — INHABITATION of the quaternionic Shimura-curve package**
(sorry leaf, CUT 2026-07-27 out of
`exists_threeadicField_realization_of_totallyDefinite_heckeCharacter`, which
is now a PROVEN assembly over this leaf and
`exists_galoisRep_charFrob_of_carayolPackage`).

This is Carayol's Théorème (A) stated in the vocabulary of the object Carayol
actually constructs: the `3`-adic cohomology of the Shimura curve attached to
the quaternion algebra, with its Hecke action, its Eichler–Shimura congruence
relation, multiplicity one, and the Weil-pairing determinant. Everything from
those data to the STEP 2a statement is PROVEN above; what remains here is the
geometry.

HYPOTHESES ARE BYTE-IDENTICAL to STEP 2a's, `hJL` included; nothing on the
hypothesis side moved, so the round-2/3/4/5 hypothesis audits recorded in
`carayol_threeadic_realization_of_heckePackage`'s docstring apply here
unchanged. In particular `hbad2`/`hbad3`/`hbadℓ` still delete the places
where the `3`-adic member ramifies, and `hirrF` is still the non-Eisenstein
condition without which Théorème (A) is not a theorem about this eigensystem
— and, by the ROUND-5 INTERLOCK, is also what makes the three `hbad`
exclusions SUFFICIENT.

INTEGRALITY IS STILL ABSENT from the conclusion, and must stay absent: `σ_λ`
is `E_λ`-adic and `E_λ` is a FIELD, so `Module.Finite ℤ_3 B` was never
something the citation could supply. That obligation lives in the sibling
`exists_stableLattice_galoisRep_of_finiteDimensional_padic`, where it is
elementary (Serre, *Abelian ℓ-adic representations* I §1).

Literature: Carayol, *Sur les représentations `ℓ`-adiques associées aux
formes modulaires de Hilbert*, Ann. Sci. ÉNS (4) **19** (1986) 409–468,
Théorème (A) (§0.7), its even-degree quaternionic predecessor Théorème (B)
(§0.9), and the cohomological construction of §0.10–0.11; Taylor, *On Galois
representations associated to Hilbert modular forms*, Invent. Math. **98**
(1989), for the cases Carayol's Shimura-curve route does not reach: `[F:ℚ]`
even with `π` not discrete series at any finite place. **Taylor is a live part
of this citation, not a footnote**, and the reason is worth stating because it
is invisible from this signature alone: for even `[F:ℚ]` the quaternion
algebra Carayol needs — split at exactly ONE infinite place — must ramify at
some FINITE place too, which forces `π` to be discrete series there. In the
intended chain `[F:ℚ] IS` even: `hFeven` is the hypothesis STEP 1
(`exists_totallyDefinite_heckeCharacter_of_heckePackage`) consumes to build
the definite quaternion algebra. (This leaf does not itself carry `hFeven`,
and `hJL` does not force evenness either — a totally definite `D` over an
odd-degree `F` ramifies at an odd number of finite places — so an odd-degree
instance is formally admissible here and is the EASY case for the citation.)

ROUND-6 DECOMPOSITION AUDIT (2026-07-27) — why the cut went THIS way and not
another. Rounds 2–5 audited the HYPOTHESIS side and the conclusion-side
SHRINKS; round 6 asked the different question of how to DECOMPOSE what is
left. Axes searched, each with the check that would refute the verdict:

(a) COEFFICIENT-FIELD SELECTION — cutting out "produce `L`, `ψ₃`, `ι`" as an
  elementary leaf (a number field embeds in `ℚ̄_3`, and the `ℚ_3`-algebra it
  generates is finite). REJECTED, and this is the sharp point: the current
  conclusion `∃ L, …` is ALREADY maximally weak in `L`, so every way of
  moving the choice out makes the remainder STRONGER — `∀ L` receiving `E`
  additionally demands base change from `E_λ`; pinning `L = ℚ_3(ψ₃ E)` is
  Théorème (A) verbatim, which is route (2) of the ROUND-3 audit, already
  rejected there for asserting more. Refuting check: exhibit a factorisation
  of the coefficient-field choice under which the residue is WEAKER than the
  present statement. None was found.

(b) THE CARRIER — returning the representation on an abstract 2-dimensional
  `L`-module instead of `Fin 2 → L`, with a basis-transport leaf. It IS a
  strict weakening, and it is REJECTED by the ROUND-3 route-(3) test: it
  removes no INPUT, since the construction that proves the weak form is the
  same construction in full. (It is also exactly what
  `exists_galoisRep_charFrob_of_carayolPackage` now does internally, for
  free.)

(c) THE `ℚ̄_3` FORM — weakening the conclusion to a representation over
  `AlgebraicClosure ℚ_[3]`, with an elementary re-ascent leaf. The re-ascent
  is TRUE and its proof is worth recording since it is not obvious: `Γ_F` is
  compact, `GL₂(ℚ̄_3) = ⋃_L GL₂(L)` over the COUNTABLY many finite extensions
  `L/ℚ_3` (finitely many of each degree), each closed since `L` is complete;
  Baire on the compact image gives one `GL₂(L) ∩ image` with nonempty
  interior, hence an open — so finite-index — subgroup, and adjoining the
  entries of finitely many coset representatives gives the field. REJECTED
  anyway, on two independent grounds: it fails the same route-(3) test (the
  `E_λ`-adic construction is what produces both forms), and the re-ascent
  needs "finitely many extensions of `ℚ_3` of each degree", which is Krasner
  and is not at this pin.

(d) THE LITERATURE'S OWN CASE SPLIT — Carayol §0.9 (a finite place where `π`
  is discrete series) versus Taylor 1989 (the rest). NOT STATEABLE: the case
  distinction is a condition on the local components of an automorphic
  representation, and the pin has no automorphic representations of `GL₂/F`.

(e) THE GEOMETRIC ROUTE — taken, and it is this cut. Note what it does NOT
  do: see the FORMAL-CONTENT AUDIT on `CarayolPackage`, which records that
  the package is EQUIVALENT to the STEP 2a conclusion and therefore
  RELOCATES the citation into geometric vocabulary rather than shrinking it.
  The genuine shrink is the next cut, also recorded there.

AXES NOT SEARCHED, so that the next owner starts where this one stopped: the
CONSUMER side (whether `carayol_threeadic_realization_of_heckePackage` and
its own consumers could be restructured to need less than a full compatible
member at `3` — that is a cut-level change above this node and belongs to its
owner), and the `R = 𝕋` route (stating the package over the Hecke algebra
`TotallyDefiniteQuaternionAlgebra.HeckeAlgebra D 𝒮` and specialising along
`θ`, as `Modularity/Patching.lean` would want it — a STRONGER statement, so
rejected here, but possibly the right shape if a consumer ever needs the
family rather than one specialisation).

CIRCULARITY GUARD (inherited from pillar β, load-bearing): no discharge
through `Family.lean`, `Lift.lean`, or `Modularity/Interface.lean`. -/
theorem exists_carayolPackage_of_totallyDefinite_heckeCharacter
    {ℓ : ℕ} (hℓodd : Odd ℓ) [Fact ℓ.Prime] (hℓ5 : 5 ≤ ℓ)
    {O : Type u} [CommRing O] [IsDomain O] [TopologicalSpace O]
    [IsTopologicalRing O] [Algebra ℤ_[ℓ] O] [IsLocalRing O]
    [Module.Finite ℤ_[ℓ] O] [IsModuleTopology ℤ_[ℓ] O]
    (hZinj : Function.Injective (algebraMap ℤ_[ℓ] O))
    {ρ : GaloisRep ℚ O (Fin 2 → O)}
    (hrank : Module.rank O (Fin 2 → O) = 2)
    (hρ : IsHardlyRamified hℓodd hrank ρ)
    {k : Type u} [Field k] [Finite k] [Algebra ℤ_[ℓ] k]
    [TopologicalSpace k] [DiscreteTopology k]
    {W : Type v} [AddCommGroup W] [Module k W] [Module.Finite k W]
    [Module.Free k W]
    (hW : Module.rank k W = 2) {ρbar : GaloisRep ℚ k W}
    (hρbar : IsHardlyRamified hℓodd hW ρbar)
    (hirr : ρbar.IsIrreducible)
    (π : O →+* k) (hπsurj : Function.Surjective π)
    (hπ : ∀ (q : ℕ) (hq : q.Prime), q ≠ 2 → q ≠ ℓ →
      (ρ.charFrob hq.toHeightOneSpectrumRingOfIntegersRat).map π =
        ρbar.charFrob hq.toHeightOneSpectrumRingOfIntegersRat)
    (F : Type u) [Field F] [NumberField F]
    (hFtr : NumberField.IsTotallyReal F) (hFgal : IsGalois ℚ F)
    (hirrF : (ρbar.map (algebraMap ℚ F)).IsIrreducible)
    (E : Type u) [Field E] [NumberField E]
    (badF : Finset (HeightOneSpectrum (NumberField.RingOfIntegers F)))
    (heckeF : HeightOneSpectrum (NumberField.RingOfIntegers F) →
      Polynomial E)
    (ψℓ : E →+* AlgebraicClosure ℚ_[ℓ])
    (ιO : O →+* AlgebraicClosure ℚ_[ℓ]) (hιO : Function.Injective ιO)
    (hmod : ∀ w ∉ badF,
      ((ρ.map (algebraMap ℚ F)).charFrob w).map ιO =
        (heckeF w).map ψℓ)
    (hbad2 : ∀ w : HeightOneSpectrum (NumberField.RingOfIntegers F),
      (2 : NumberField.RingOfIntegers F) ∈ w.asIdeal → w ∈ badF)
    (hbad3 : ∀ w : HeightOneSpectrum (NumberField.RingOfIntegers F),
      (3 : NumberField.RingOfIntegers F) ∈ w.asIdeal → w ∈ badF)
    (hbadℓ : ∀ w : HeightOneSpectrum (NumberField.RingOfIntegers F),
      (ℓ : NumberField.RingOfIntegers F) ∈ w.asIdeal → w ∈ badF)
    (hJL : ∃ (D : Type u) (_ : DivisionRing D) (_ : Algebra F D)
      (_ : _root_.IsQuaternionAlgebra F D)
      (_ : _root_.IsQuaternionAlgebra.IsTotallyDefinite F D)
      (_ : _root_.IsQuaternionAlgebra.NumberField.WithRigidification F D)
      (p : ℕ) (𝒮 : _root_.TotallyDefiniteQuaternionAlgebra.U₁Data F E p)
      (θ : _root_.TotallyDefiniteQuaternionAlgebra.HeckeAlgebra D 𝒮 →ₐ[E] E),
      ∀ (w : HeightOneSpectrum (NumberField.RingOfIntegers F))
        (hwS : w ∉ 𝒮.S) (hwQ : w ∉ 𝒮.Q), w ∉ badF →
        (heckeF w).coeff 1 =
          -θ (_root_.TotallyDefiniteQuaternionAlgebra.HeckeAlgebra.T D 𝒮 w hwS hwQ)) :
    ∃ (L : Type u) (_ : Field L) (_ : Algebra ℚ_[3] L)
      (_ : Module.Finite ℚ_[3] L),
      letI : TopologicalSpace L := moduleTopology ℚ_[3] L
      letI : IsTopologicalRing L :=
        isTopologicalRing_moduleTopology_of_finite_padic 3 L
      ∃ (ψ₃ : E →+* AlgebraicClosure ℚ_[3])
        (ι : L →+* AlgebraicClosure ℚ_[3])
        (P : HeightOneSpectrum (NumberField.RingOfIntegers F) → Polynomial L),
        (∀ w ∉ badF, (P w).map ι = (heckeF w).map ψ₃) ∧
          Nonempty (CarayolPackage F L badF P) := by
  sorry

/-- **STEP 2a — CARAYOL's Théorème (A) in its FIELD form: the `3`-adic
realization over a finite extension of `ℚ_3`** (CUT 2026-07-27 out of
`carayol_threeadic_of_totallyDefinite_heckeCharacter`, which is now a proven
assembly of this leaf and the stable-lattice leaf below; and PROVEN ITSELF
since 2026-07-27, by the Eichler–Shimura cut, over
`exists_carayolPackage_of_totallyDefinite_heckeCharacter` — the geometric
inhabitation leaf — and the machine-checked extraction
`exists_galoisRep_charFrob_of_carayolPackage`).

ASSEMBLY. The citation now enters as the quaternionic Shimura-curve package
`CarayolPackage` (the `λ`-adic cohomology with its Hecke action, the
Eichler–Shimura congruence relation, multiplicity one and the Weil-pairing
determinant); the passage from those data to the statement below — the
`θ`-eigenspace is Galois-stable and 2-dimensional, the compressed
representation is a continuous 2-dimensional representation, and
Cayley–Hamilton against the congruence relation pins its Frobenius
characteristic polynomial — is PROVEN. All that is left here is composing the
comparison embeddings, through `Polynomial.map`. The frontier count is
UNCHANGED by this cut (one leaf in, one leaf out); what moved is where the
faith sits. Read the FORMAL-CONTENT AUDIT on `CarayolPackage` before treating
the cut as a reduction: it is a RELOCATION, and the genuine reduction — a
`ModularJacobianPackage`-style second level replacing multiplicity one by
freeness over the Hecke subalgebra — is recorded there as the next cut. The
ROUND-6 DECOMPOSITION AUDIT on
`exists_carayolPackage_of_totallyDefinite_heckeCharacter` records the four
other axes searched and why each was rejected.

The prose below is the statement's own audit trail and is UNCHANGED by the
Eichler–Shimura cut, since neither the hypotheses nor the conclusion moved.

This is verbatim STEP 2 with ONE component deleted from the conclusion:
INTEGRALITY. Where STEP 2 asks for a coefficient ring `B` module-finite over
`ℤ_3` — i.e. for a `Γ_F`-stable LATTICE — this asks only for the
representation over a finite extension `L/ℚ_3`, which is what Carayol's
Théorème (A) literally produces (`σ_λ` is `E_λ`-adic; `E_λ` is a field).

WHY THIS CUT IS A STRICT SHRINK, and why the standing ROUTE AUDIT no longer
blocks it. `carayol_threeadic_realization_of_heckePackage`'s ROUND-3 AUDIT,
route (1), analysed exactly this cut and reached the conclusion recorded there:
"Old ⟹ New using only material already in this file … So New is a CONSEQUENCE
of Old: strictly less to take on faith, and what it drops is exactly the
INTEGRALITY — the existence of a Galois-stable lattice — and nothing else. New
⟹ Old is precisely Serre I §1, and that is the entire price. **The moment the
lattice step is PROVEN rather than cited, the cut becomes a strict
improvement**; it is the only remaining route to removing `Module.Finite ℤ_3 B`."
The older ROUTE AUDIT (2026-07-24) had rejected the same cut on the ground that
"the stable-lattice step is itself a citation (compactness of `G_F` plus Serre
I §1), so the cut trades one citation for two". **Round 5 refuted that ground**
by producing a complete six-step in-tree work plan for the lattice step out of
material that is all present at this pin, and the ONE pin gap it named has
since closed — see the lattice leaf's docstring for both the plan and the
refuting checks. So the lattice half is an ELEMENTARY open leaf, not a
citation, and this is one citation plus one elementary leaf rather than two
citations.

Every hypothesis, and every other component of the conclusion, is byte-identical
to STEP 2's; in particular `hJL` is the STEP 1 package verbatim, `hbad2` /
`hbad3` / `hbadℓ` still delete the places where the `3`-adic member ramifies,
and `hirrF` is still the non-Eisenstein condition without which Théorème (A) is
not a theorem about this eigensystem. See
`carayol_threeadic_realization_of_heckePackage`'s docstring for the full
round-2/3/4/5 hypothesis audits; they apply here unchanged, because nothing on
the hypothesis side moved.

Literature: Carayol, *Sur les représentations `ℓ`-adiques associées aux formes
modulaires de Hilbert*, Ann. Sci. ÉNS (4) **19** (1986) 409–468, Théorème (A)
(§0.7) and its even-degree quaternionic predecessor Théorème (B) (§0.9);
Taylor, *On Galois representations associated to Hilbert modular forms*,
Invent. Math. **98** (1989). Carayol builds the compatible system by
decomposing the `ℓ`-adic cohomology `H¹(M_K ⊗_F F̄, ℱ_λ)` of the Shimura curves
attached to the quaternion algebra under the Hecke action (op. cit.
§0.10–0.11); no pin material reaches that, which is why this half stays a
citation.

CIRCULARITY GUARD (inherited from pillar β, load-bearing): no discharge
through `Family.lean`, `Lift.lean`, or `Modularity/Interface.lean`. -/
theorem exists_threeadicField_realization_of_totallyDefinite_heckeCharacter
    {ℓ : ℕ} (hℓodd : Odd ℓ) [Fact ℓ.Prime] (hℓ5 : 5 ≤ ℓ)
    {O : Type u} [CommRing O] [IsDomain O] [TopologicalSpace O]
    [IsTopologicalRing O] [Algebra ℤ_[ℓ] O] [IsLocalRing O]
    [Module.Finite ℤ_[ℓ] O] [IsModuleTopology ℤ_[ℓ] O]
    (hZinj : Function.Injective (algebraMap ℤ_[ℓ] O))
    {ρ : GaloisRep ℚ O (Fin 2 → O)}
    (hrank : Module.rank O (Fin 2 → O) = 2)
    (hρ : IsHardlyRamified hℓodd hrank ρ)
    {k : Type u} [Field k] [Finite k] [Algebra ℤ_[ℓ] k]
    [TopologicalSpace k] [DiscreteTopology k]
    {W : Type v} [AddCommGroup W] [Module k W] [Module.Finite k W]
    [Module.Free k W]
    (hW : Module.rank k W = 2) {ρbar : GaloisRep ℚ k W}
    (hρbar : IsHardlyRamified hℓodd hW ρbar)
    (hirr : ρbar.IsIrreducible)
    (π : O →+* k) (hπsurj : Function.Surjective π)
    (hπ : ∀ (q : ℕ) (hq : q.Prime), q ≠ 2 → q ≠ ℓ →
      (ρ.charFrob hq.toHeightOneSpectrumRingOfIntegersRat).map π =
        ρbar.charFrob hq.toHeightOneSpectrumRingOfIntegersRat)
    (F : Type u) [Field F] [NumberField F]
    (hFtr : NumberField.IsTotallyReal F) (hFgal : IsGalois ℚ F)
    (hirrF : (ρbar.map (algebraMap ℚ F)).IsIrreducible)
    (E : Type u) [Field E] [NumberField E]
    (badF : Finset (HeightOneSpectrum (NumberField.RingOfIntegers F)))
    (heckeF : HeightOneSpectrum (NumberField.RingOfIntegers F) →
      Polynomial E)
    (ψℓ : E →+* AlgebraicClosure ℚ_[ℓ])
    (ιO : O →+* AlgebraicClosure ℚ_[ℓ]) (hιO : Function.Injective ιO)
    (hmod : ∀ w ∉ badF,
      ((ρ.map (algebraMap ℚ F)).charFrob w).map ιO =
        (heckeF w).map ψℓ)
    (hbad2 : ∀ w : HeightOneSpectrum (NumberField.RingOfIntegers F),
      (2 : NumberField.RingOfIntegers F) ∈ w.asIdeal → w ∈ badF)
    (hbad3 : ∀ w : HeightOneSpectrum (NumberField.RingOfIntegers F),
      (3 : NumberField.RingOfIntegers F) ∈ w.asIdeal → w ∈ badF)
    (hbadℓ : ∀ w : HeightOneSpectrum (NumberField.RingOfIntegers F),
      (ℓ : NumberField.RingOfIntegers F) ∈ w.asIdeal → w ∈ badF)
    (hJL : ∃ (D : Type u) (_ : DivisionRing D) (_ : Algebra F D)
      (_ : _root_.IsQuaternionAlgebra F D)
      (_ : _root_.IsQuaternionAlgebra.IsTotallyDefinite F D)
      (_ : _root_.IsQuaternionAlgebra.NumberField.WithRigidification F D)
      (p : ℕ) (𝒮 : _root_.TotallyDefiniteQuaternionAlgebra.U₁Data F E p)
      (θ : _root_.TotallyDefiniteQuaternionAlgebra.HeckeAlgebra D 𝒮 →ₐ[E] E),
      ∀ (w : HeightOneSpectrum (NumberField.RingOfIntegers F))
        (hwS : w ∉ 𝒮.S) (hwQ : w ∉ 𝒮.Q), w ∉ badF →
        (heckeF w).coeff 1 =
          -θ (_root_.TotallyDefiniteQuaternionAlgebra.HeckeAlgebra.T D 𝒮 w hwS hwQ)) :
    ∃ (L : Type u) (_ : Field L) (_ : Algebra ℚ_[3] L)
      (_ : Module.Finite ℚ_[3] L),
      letI : TopologicalSpace L := moduleTopology ℚ_[3] L
      letI : IsTopologicalRing L :=
        isTopologicalRing_moduleTopology_of_finite_padic 3 L
      ∃ (τ : GaloisRep F L (Fin 2 → L))
        (ψ₃ : E →+* AlgebraicClosure ℚ_[3])
        (ι : L →+* AlgebraicClosure ℚ_[3]),
        ∀ w ∉ badF, (τ.charFrob w).map ι = (heckeF w).map ψ₃ := by
  -- STEP 2a′ — the GEOMETRIC half: the quaternionic Shimura curve, its
  -- `3`-adic cohomology, and the four classical facts about it.
  obtain ⟨L, hFieldL, hAlgL, hFinL, ψ₃, ι, P, hPmatch, ⟨C⟩⟩ :=
    exists_carayolPackage_of_totallyDefinite_heckeCharacter hℓodd hℓ5
      hZinj hrank hρ hW hρbar hirr π hπsurj hπ F hFtr hFgal hirrF E badF heckeF
      ψℓ ιO hιO hmod hbad2 hbad3 hbadℓ hJL
  refine ⟨L, hFieldL, hAlgL, hFinL, ?_⟩
  -- the topology on `L` is not a choice — `Module.Finite ℚ_3 L` pins it
  letI : TopologicalSpace L := moduleTopology ℚ_[3] L
  haveI : IsTopologicalRing L :=
    isTopologicalRing_moduleTopology_of_finite_padic 3 L
  -- the PROVEN half: eigenspace, compression, Cayley–Hamilton
  obtain ⟨τ, hτ⟩ := exists_galoisRep_charFrob_of_carayolPackage C
  exact ⟨τ, ψ₃, ι, fun w hw => by rw [hτ w hw, hPmatch w hw]⟩

/-! ### The Serre stable-lattice development (2026-07-27)

The five declarations below carry out STEPS 1–4 of the six-step plan
recorded on `exists_stableLattice_galoisRep_of_finiteDimensional_padic`
below, and cut the remaining STEPS 5–6 out as the single named leaf
`exists_framed_of_finiteIndex_stabilizer`.  Reading order:

* `isTorsionFree_padicInt_of_algebra` — the one instance that search does
  not produce (STEP 2's recorded friction);
* `isOpen_span_range_basis_padic` — the `ℤ_p`-span of a `ℚ_p`-basis of a
  finite-dimensional `ℚ_p`-space is OPEN.  This is the "first genuinely
  NEW lemma" the plan predicted, and it is the `L`-version that
  `TateModule.lean`'s `isOpen_span_natCast_pow` is the technique but not
  the statement of;
* `isOpen_integralClosure_padic` — hence `𝒪_L` is open in `L`, via
  `Module.Basis.localizationLocalization`, which is exactly the
  "`ℚ_p`-basis of `L` drawn from a `ℤ_p`-basis of `𝒪_L`" the plan asked
  for (it is also what mathlib's own `IsIntegralClosure.rank` uses);
* `exists_framed_of_finiteIndex_stabilizer` — THE REMAINING LEAF: STEPS
  5–6, the coset-sum lattice and the continuity of the framed
  representation;
* `exists_framed_stableLattice_of_finiteDimensional_padic` — PROVEN
  assembly of STEPS 1–4 over those, cutting `charFrob` out of the picture
  entirely (it produces a MATRIX identity instead, which is what makes the
  headline theorem below a three-line `charpoly` computation). -/

/-- **`ℤ_p`-torsion-freeness of a field which is a `ℚ_p`-algebra** (PROVEN
2026-07-27).  Instance search does NOT produce `Module.IsTorsionFree ℤ_[p] L`,
and it is the one hypothesis that `IsIntegralClosure.module_free` and
`IsIntegralClosure.rank` need beyond what is inferred; it is `comap` along
`ℤ_p ↪ ℚ_p` from the field instance. -/
theorem isTorsionFree_padicInt_of_algebra (p : ℕ) [Fact p.Prime]
    {L : Type*} [Field L] [Algebra ℚ_[p] L] [Algebra ℤ_[p] L]
    [IsScalarTower ℤ_[p] ℚ_[p] L] : Module.IsTorsionFree ℤ_[p] L :=
  Module.IsTorsionFree.comap (S := ℚ_[p]) (algebraMap ℤ_[p] ℚ_[p])
    (fun _ hr => isRegular_iff_ne_zero.mpr fun h => (isRegular_iff_ne_zero.mp hr)
      ((map_eq_zero_iff _ (IsFractionRing.injective ℤ_[p] ℚ_[p])).mp h))
    (fun r m => algebraMap_smul ℚ_[p] r m)

/-- **The `ℤ_p`-span of a `ℚ_p`-basis of a finite-dimensional `ℚ_p`-space
with its module topology is OPEN** (PROVEN 2026-07-27).

Read through the coordinate isomorphism `b.equivFun : V ≃ₗ[ℚ_p] (ι → ℚ_p)`
— a homeomorphism, because both sides carry the module topology and
`IsModuleTopology.continuous_of_linearMap` applies in each direction — the
span is exactly the set of vectors all of whose coordinates lie in
`ℤ_p ⊆ ℚ_p`, and `ℤ_p` is open in `ℚ_p` because the closed unit ball of an
ultrametric field is open (`PadicInt.isOpenEmbedding_coe`).  So it is a
finite product of opens, `isOpen_set_pi`.

This is the `V`-version of `Modularity/TateModule.lean`'s
`isOpen_span_natCast_pow`, which is about an ideal INSIDE a ring already
carrying the `ℤ_q`-module topology and therefore does not apply here. -/
theorem isOpen_span_range_basis_padic (p : ℕ) [Fact p.Prime]
    {V : Type*} [AddCommGroup V] [Module ℚ_[p] V] [Module ℤ_[p] V]
    [IsScalarTower ℤ_[p] ℚ_[p] V] [Module.Finite ℚ_[p] V]
    [TopologicalSpace V] [IsModuleTopology ℚ_[p] V]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℚ_[p] V) :
    IsOpen ((Submodule.span ℤ_[p] (Set.range b) : Submodule ℤ_[p] V) : Set V) := by
  classical
  have hmem : ∀ x : V, x ∈ Submodule.span ℤ_[p] (Set.range b) ↔
      ∀ j, b.repr x j ∈ Set.range (algebraMap ℤ_[p] ℚ_[p]) := by
    intro x
    constructor
    · intro hx
      induction hx using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨i, rfl⟩ := hy
        intro j
        rw [b.repr_self]
        rcases eq_or_ne j i with h | h
        · exact ⟨1, by simp [h]⟩
        · exact ⟨0, by simp [h]⟩
      | zero => intro j; exact ⟨0, by simp⟩
      | add y z _ _ hy hz =>
        intro j
        obtain ⟨cy, hcy⟩ := hy j
        obtain ⟨cz, hcz⟩ := hz j
        exact ⟨cy + cz, by simp [← hcy, ← hcz]⟩
      | smul c y _ hy =>
        intro j
        obtain ⟨cy, hcy⟩ := hy j
        refine ⟨c * cy, ?_⟩
        rw [show c • y = (algebraMap ℤ_[p] ℚ_[p] c) • y from
          (algebraMap_smul ℚ_[p] c y).symm]
        simp [← hcy]
    · intro h
      choose c hc using h
      have hx : x = ∑ j, c j • b j := by
        conv_lhs => rw [← b.sum_repr x]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [← hc j, algebraMap_smul]
      rw [hx]
      exact Submodule.sum_mem _ fun j _ =>
        Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  have hset : ((Submodule.span ℤ_[p] (Set.range b) : Submodule ℤ_[p] V) : Set V)
      = b.equivFun ⁻¹' (Set.univ.pi fun _ : ι =>
        Set.range (algebraMap ℤ_[p] ℚ_[p])) := by
    ext x
    simpa [b.equivFun_apply] using hmem x
  have hrange : IsOpen (Set.range (algebraMap ℤ_[p] ℚ_[p])) := by
    have hcoe : Set.range (algebraMap ℤ_[p] ℚ_[p]) = Set.range ((↑) : ℤ_[p] → ℚ_[p]) := rfl
    rw [hcoe]
    exact PadicInt.isOpenEmbedding_coe.isOpen_range
  rw [hset]
  exact IsOpen.preimage (IsModuleTopology.continuous_of_linearMap b.equivFun.toLinearMap)
    (isOpen_set_pi Set.finite_univ fun _ _ => hrange)

/-- **The ring of integers `𝒪_L = integralClosure ℤ_p L` is OPEN in a finite
extension `L/ℚ_p`** (PROVEN 2026-07-27) — STEP 2 of the plan on
`exists_stableLattice_galoisRep_of_finiteDimensional_padic`, and the one
half of it that the handover recorded as NOT confirmed.

`𝒪_L` is module-finite and free over `ℤ_p` (`IsIntegralClosure.finite`,
`IsIntegralClosure.module_free`, the latter over
`isTorsionFree_padicInt_of_algebra`), and `L` is the localization of `𝒪_L`
at `ℤ_p⁰` (`IsIntegralClosure.isLocalization`), so a `ℤ_p`-basis of `𝒪_L`
becomes a `ℚ_p`-basis of `L` by `Module.Basis.localizationLocalization`
whose `ℤ_p`-span is, by `localizationLocalization_span`, exactly the range
of `𝒪_L → L`.  Then `isOpen_span_range_basis_padic` applies. -/
theorem isOpen_integralClosure_padic (p : ℕ) [Fact p.Prime]
    {L : Type*} [Field L] [Algebra ℚ_[p] L] [Module.Finite ℚ_[p] L]
    [TopologicalSpace L] [IsModuleTopology ℚ_[p] L]
    [Algebra ℤ_[p] L] [IsScalarTower ℤ_[p] ℚ_[p] L] :
    IsOpen ((integralClosure ℤ_[p] L : Set L)) := by
  classical
  haveI : Module.IsTorsionFree ℤ_[p] L := isTorsionFree_padicInt_of_algebra p
  set C := integralClosure ℤ_[p] L with hCdef
  haveI hfin : Module.Finite ℤ_[p] C := IsIntegralClosure.finite ℤ_[p] ℚ_[p] L C
  haveI hfree : Module.Free ℤ_[p] C := IsIntegralClosure.module_free ℤ_[p] ℚ_[p] L C
  haveI hloc := IsIntegralClosure.isLocalization ℤ_[p] ℚ_[p] L C
  haveI : Fintype (Module.Free.ChooseBasisIndex ℤ_[p] C) :=
    Module.Free.ChooseBasisIndex.fintype ℤ_[p] C
  set bC := Module.Free.chooseBasis ℤ_[p] C with hbC
  set b := Module.Basis.localizationLocalization ℚ_[p] (nonZeroDivisors ℤ_[p]) L bC with hb
  have hspan : (Submodule.span ℤ_[p] (Set.range b) : Submodule ℤ_[p] L)
      = LinearMap.range (IsScalarTower.toAlgHom ℤ_[p] C L : C →ₗ[ℤ_[p]] L) :=
    Module.Basis.localizationLocalization_span ℚ_[p] (nonZeroDivisors ℤ_[p]) L bC
  have hset : ((integralClosure ℤ_[p] L : Subalgebra ℤ_[p] L) : Set L)
      = ((Submodule.span ℤ_[p] (Set.range b) : Submodule ℤ_[p] L) : Set L) := by
    rw [hspan]
    ext x
    simp only [SetLike.mem_coe, LinearMap.mem_range]
    constructor
    · intro hx; exact ⟨⟨x, hx⟩, rfl⟩
    · rintro ⟨y, rfl⟩; exact y.2
  rw [hset]
  exact isOpen_span_range_basis_padic p b

/-- **STEPS 5–6 of the Serre stable-lattice plan: the COSET-SUM LATTICE and
the CONTINUITY of its framing** (sorry leaf, CUT 2026-07-27).

Given a finite-index subgroup `U ≤ Γ_F` preserving the STANDARD lattice
`𝒪_L² ⊆ L²` — which `exists_framed_stableLattice_of_finiteDimensional_padic`
below constructs and proves open, hence of finite index, by compactness —
produce a `Γ_F`-stable lattice and a framing of it.

WHAT REMAINS, and it is exactly the two steps the handover plan called the
`Finset` bookkeeping and "the expensive half":

* STEP 5.  `Λ := ⨆ q : Γ_F ⧸ U, τ(q.out) '' 𝒪_L²` is `Γ_F`-stable: for `g`
  and a class `q`, `g * q.out` lies in the class `⟦g * q.out⟧`, so
  `g * q.out = ⟦g * q.out⟧.out * u` with `u ∈ U` and
  `τ(g * q.out) '' 𝒪_L² = τ(⟦g * q.out⟧.out) '' (τ(u) '' 𝒪_L²) ⊆ Λ`.  It is
  a finite sup of f.g. `𝒪_L`-modules, hence f.g.; it contains an
  automorphic image of `𝒪_L²`, hence spans `L²` over `L`.  Being f.g. and
  torsion-free over the DVR `𝒪_L` it is FREE, and spanning `L²` pins its
  rank at `2` — that is `b` together with `e : Λ ≃ₗ[𝒪_L] (Fin 2 → 𝒪_L)`.
* STEP 6.  CONTINUITY of `g ↦ e.conj (τ g |_Λ)` into
  `moduleTopology 𝒪_L (End_{𝒪_L}(Fin 2 → 𝒪_L))`.  Go through `ℤ_p` rather
  than `𝒪_L`: the two module topologies agree because `𝒪_L` is
  module-finite over `ℤ_p` (`IsModuleTopology.trans` /
  `moduleTopology.trans`, in this tree at
  `Fermat/FLT/Mathlib/Topology/Algebra/Module/ModuleTopology.lean:169,194`),
  `End_{𝒪_L}(𝒪_L²)` is then finite free over `ℤ_p`, and continuity into a
  finite free `ℤ_p`-module is continuity of coordinates, each of which
  factors through the already-continuous `τ` and the topological embedding
  `ℤ_p ↪ ℚ_p`.  Keep the intermediate lemmas stated over an ABSTRACT
  module.

The conclusion is a MATRIX identity rather than anything about `charFrob`:
`b` is an `L`-basis of `L²` and the matrix of `τ g` in it is the
`algebraMap 𝒪_L L`-image of the matrix of `ρ g` in the standard basis.
That is strictly more elementary than a characteristic-polynomial
statement, and `exists_stableLattice_galoisRep_of_finiteDimensional_padic`
below converts it in three rewrites (`LinearMap.charpoly_toMatrix`,
`Matrix.charpoly_map`). -/
theorem exists_framed_of_finiteIndex_stabilizer (p : ℕ) [Fact p.Prime]
    {F : Type u} [Field F] [NumberField F]
    {L : Type u} [Field L] [Algebra ℚ_[p] L] [Module.Finite ℚ_[p] L]
    [TopologicalSpace L] [IsTopologicalRing L] [IsModuleTopology ℚ_[p] L]
    [Algebra ℤ_[p] L] [IsScalarTower ℤ_[p] ℚ_[p] L]
    (τ : GaloisRep F L (Fin 2 → L))
    (U : Subgroup (Field.absoluteGaloisGroup F)) (hUfi : U.FiniteIndex)
    (hU : ∀ g ∈ U, ∀ x : Fin 2 → L,
        (∀ k, x k ∈ integralClosure ℤ_[p] L) →
        ∀ k, τ g x k ∈ integralClosure ℤ_[p] L) :
    letI : TopologicalSpace ↥(integralClosure ℤ_[p] L) :=
      moduleTopology ℤ_[p] ↥(integralClosure ℤ_[p] L)
    ∃ (ρ : GaloisRep F ↥(integralClosure ℤ_[p] L)
          (Fin 2 → ↥(integralClosure ℤ_[p] L)))
      (b : Module.Basis (Fin 2) L (Fin 2 → L)),
      ∀ (g : Field.absoluteGaloisGroup F) (i : Fin 2),
        τ g (b i) = ∑ k, algebraMap ↥(integralClosure ℤ_[p] L) L
          (ρ g (Pi.single i 1) k) • b k := by
  sorry

/-- **STEPS 1–4 of the Serre stable-lattice plan, in MATRIX form** (PROVEN
2026-07-27 over `isOpen_integralClosure_padic` and the single leaf
`exists_framed_of_finiteIndex_stabilizer`).

STEP 1 `CompactSpace (Γ F)` by `inferInstanceAs`; STEP 2 `𝒪_L` open in `L`;
then the set `S ⊆ End_L(L²)` of endomorphisms preserving the standard
lattice `𝒪_L²` is OPEN — it is cut out by the finitely many `L`-linear
coordinate functionals `f ↦ (f eᵢ)_k`, each continuous out of the module
topology, and `𝒪_L` is open — so the TWO-SIDED stabilizer
`U := {g | τ g ∈ S ∧ τ g⁻¹ ∈ S}` is an open SUBGROUP (the two-sided form is
what makes it one; the naive preimage of the integral matrices is only a
submonoid), and STEP 3 gives it finite index.

`S` is described two ways and the proof needs both: as
`{f | ∀ x ∈ 𝒪_L², f x ∈ 𝒪_L²}` for the subgroup axioms, and as
`{f | ∀ i k, (f eᵢ)_k ∈ 𝒪_L}` for openness.  They agree because
`x = ∑ᵢ xᵢ • eᵢ` and `𝒪_L` is a subring. -/
theorem exists_framed_stableLattice_of_finiteDimensional_padic
    (p : ℕ) [Fact p.Prime]
    {F : Type u} [Field F] [NumberField F]
    {L : Type u} [Field L] [Algebra ℚ_[p] L] [Module.Finite ℚ_[p] L]
    [TopologicalSpace L] [IsTopologicalRing L] [IsModuleTopology ℚ_[p] L]
    (τ : GaloisRep F L (Fin 2 → L)) :
    ∃ (B : Type u) (_ : CommRing B) (_ : Algebra ℤ_[p] B)
      (_ : Module.Finite ℤ_[p] B),
      letI : TopologicalSpace B := moduleTopology ℤ_[p] B
      letI : IsTopologicalRing B := isTopologicalRing_moduleTopology_of_finite p B
      ∃ (ρ : GaloisRep F B (Fin 2 → B)) (j : B →+* L)
        (b : Module.Basis (Fin 2) L (Fin 2 → L)),
        ∀ (g : Field.absoluteGaloisGroup F) (i : Fin 2),
          τ g (b i) = ∑ k, j (ρ g (Pi.single i 1) k) • b k := by
  classical
  letI : Algebra ℤ_[p] L :=
    ((algebraMap ℚ_[p] L).comp (algebraMap ℤ_[p] ℚ_[p])).toAlgebra
  haveI : IsScalarTower ℤ_[p] ℚ_[p] L := IsScalarTower.of_algebraMap_eq fun _ => rfl
  set C := integralClosure ℤ_[p] L with hCdef
  -- the endomorphism algebra carries the `L`-module topology
  letI : TopologicalSpace (Module.End L (Fin 2 → L)) :=
    moduleTopology L (Module.End L (Fin 2 → L))
  haveI : IsModuleTopology L (Module.End L (Fin 2 → L)) := ⟨rfl⟩
  -- STEP 2: `𝒪_L` is open in `L`
  have hOopen : IsOpen ((C : Set L)) := isOpen_integralClosure_padic p
  -- the set of endomorphisms preserving the standard lattice `𝒪_L²`
  set S : Set (Module.End L (Fin 2 → L)) :=
    {f | ∀ x : Fin 2 → L, (∀ k, x k ∈ C) → ∀ k, f x k ∈ C} with hSdef
  have hSbasis : S = {f : Module.End L (Fin 2 → L) | ∀ i k, f (Pi.single i 1) k ∈ C} := by
    ext f
    simp only [hSdef, Set.mem_setOf_eq]
    constructor
    · intro hf i k
      refine hf _ (fun k' => ?_) k
      by_cases h : k' = i
      · simp [h, Pi.single_eq_same]
      · simp [Pi.single_eq_of_ne h]
    · intro hf x hx k
      have hxsum : x = ∑ i, x i • Pi.single (M := fun _ : Fin 2 => L) i 1 := by
        funext k'
        simp [Finset.sum_apply, Pi.single_apply, Finset.sum_ite_eq]
      rw [hxsum]
      simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      exact Subalgebra.sum_mem _ fun i _ => Subalgebra.mul_mem _ (hx i) (hf i k)
  -- the lattice-preserving set is OPEN
  have hSopen : IsOpen S := by
    rw [hSbasis]
    have hrw : {f : Module.End L (Fin 2 → L) | ∀ i k, f (Pi.single i 1) k ∈ C}
        = ⋂ i : Fin 2, ⋂ k : Fin 2,
          (fun f : Module.End L (Fin 2 → L) => f (Pi.single i 1) k) ⁻¹' (C : Set L) := by
      ext f; simp [Set.mem_iInter]
    rw [hrw]
    refine isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun k => ?_
    exact IsOpen.preimage (IsModuleTopology.continuous_of_linearMap
      ({ toFun := fun f : Module.End L (Fin 2 → L) => f (Pi.single i 1) k
         map_add' := fun _ _ => rfl
         map_smul' := fun _ _ => rfl } : Module.End L (Fin 2 → L) →ₗ[L] L)) hOopen
  -- `S` contains the identity and is closed under composition
  have hSone : (1 : Module.End L (Fin 2 → L)) ∈ S := fun x hx k => hx k
  have hSmul : ∀ f g, f ∈ S → g ∈ S → f * g ∈ S := by
    intro f g hf hg x hx k
    exact hf (g x) (hg x hx) k
  -- the TWO-SIDED stabilizer is an OPEN subgroup, hence of finite index
  set U : Subgroup (Field.absoluteGaloisGroup F) :=
    { carrier := {g | τ g ∈ S ∧ τ g⁻¹ ∈ S}
      mul_mem' := by
        rintro a b ⟨ha1, ha2⟩ ⟨hb1, hb2⟩
        refine ⟨?_, ?_⟩
        · rw [map_mul]; exact hSmul _ _ ha1 hb1
        · rw [mul_inv_rev, map_mul]; exact hSmul _ _ hb2 ha2
      one_mem' := by
        refine ⟨?_, ?_⟩
        · rw [map_one]; exact hSone
        · rw [inv_one, map_one]; exact hSone
      inv_mem' := by
        rintro a ⟨ha1, ha2⟩
        exact ⟨ha2, by rw [inv_inv]; exact ha1⟩ } with hUdef
  have hUopen : IsOpen (U : Set (Field.absoluteGaloisGroup F)) := by
    have hτcont : Continuous fun g : Field.absoluteGaloisGroup F => τ g :=
      ContinuousMonoidHom.continuous_toFun τ
    have hrw : (U : Set (Field.absoluteGaloisGroup F))
        = ((fun g : Field.absoluteGaloisGroup F => τ g) ⁻¹' S)
          ∩ ((fun g : Field.absoluteGaloisGroup F => τ g⁻¹) ⁻¹' S) := rfl
    rw [hrw]
    exact (hSopen.preimage hτcont).inter (hSopen.preimage (hτcont.comp continuous_inv))
  haveI hcompact : CompactSpace (Field.absoluteGaloisGroup F) :=
    inferInstanceAs (CompactSpace (AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F))
  have hUfi : U.FiniteIndex :=
    haveI : Finite (Field.absoluteGaloisGroup F ⧸ U) :=
      Subgroup.quotient_finite_of_isOpen U hUopen
    Subgroup.finiteIndex_of_finite_quotient
  have hUstab : ∀ g ∈ U, ∀ x : Fin 2 → L,
      (∀ k, x k ∈ integralClosure ℤ_[p] L) →
      ∀ k, τ g x k ∈ integralClosure ℤ_[p] L := fun g hg => hg.1
  letI : TopologicalSpace ↥C := moduleTopology ℤ_[p] ↥C
  obtain ⟨ρ, b, hb⟩ := exists_framed_of_finiteIndex_stabilizer p τ U hUfi hUstab
  exact ⟨↥C, inferInstance, inferInstance,
    IsIntegralClosure.finite ℤ_[p] ℚ_[p] L ↥C, ρ, algebraMap ↥C L, b, hb⟩

/-- **STEP 2b — THE GALOIS-STABLE LATTICE (Serre, *Abelian `ℓ`-adic
representations*, I §1)** (sorry leaf, CUT 2026-07-27): a continuous
`2`-dimensional representation of `Γ_F` over a finite extension `L/ℚ_p`
preserves a lattice, so it is conjugate to a representation over a
coefficient ring `B` module-finite over `ℤ_p`, with the same Frobenius
characteristic polynomials.

**THIS IS AN ELEMENTARY LEAF, NOT A CITATION**, and saying so is the whole
point of the cut: it is what makes
`exists_threeadicField_realization_of_totallyDefinite_heckeCharacter` a strict
shrink of the Carayol citation rather than a swap of one citation for two. The
2026-07-24 ROUTE AUDIT in `carayol_threeadic_realization_of_heckePackage`
rejected this cut on precisely the ground that "the stable-lattice step is
itself a citation"; the ROUND-3/ROUND-5 audits in the same docstring refuted
that by producing the complete work plan reproduced below out of material that
is entirely in-tree at this pin.

WHY IT IS TRUE. `Γ_F` is compact, `τ` is continuous, and `𝒪_L` is open in `L`;
so the two-sided stabiliser `U` of the standard lattice `Λ₀ = 𝒪_L²` is an OPEN
subgroup of a compact group, hence of finite index, and
`Λ := ∑_i τ(gᵢ) Λ₀` over coset representatives is a `Γ_F`-stable lattice. `𝒪_L`
is a DVR, so `Λ` is free of rank `2`, and conjugating by a basis gives the
representation over `B = 𝒪_L`. Conjugation does not move a characteristic
polynomial, which is why the matching clause is an equality on the nose rather
than up to an isomorphism.

WORK PLAN (inherited verbatim from the ROUND-5 audit of
`carayol_threeadic_realization_of_heckePackage`, where it was written for a
leaf that did not yet exist; it is reproduced HERE, on the declaration it is
actually about, so the next owner starts at step 4 rather than at a blank
page). Steps 1–3 are lookups, step 5 is standard, and essentially all of the
cost is in step 6.

1. `CompactSpace (Γ F)`. AVAILABLE but NOT by `inferInstance`: the tree's own
   `instance [Algebra.IsAlgebraic K L] : CompactSpace (L ≃ₐ[K] L)`
   (`Fermat/FLT/Mathlib/FieldTheory/Galois/Infinite.lean:93`) is stronger than
   mathlib's `IsGalois`-based one, but `Field.absoluteGaloisGroup` is a `def`,
   so it must be summoned as
   `inferInstanceAs (CompactSpace (AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F))`
   — the idiom already used at `ModThree.lean:37174`.
2. `𝒪_L := integralClosure ℤ_p L` is module-finite over `ℤ_p`
   (`IsIntegralClosure.finite`) and free (`IsIntegralClosure.module_free`); the
   set-up is `exists_padicIntegers_dvr_hull_of_injective`
   (`Fermat/FLT/Mathlib/RingTheory/PadicIntegralClosure.lean:192`) verbatim,
   which also gives it the `ℤ_p`-module topology by fiat. `U := {g | τ g '' Λ₀ ⊆
   Λ₀ ∧ τ g⁻¹ '' Λ₀ ⊆ Λ₀}` is a SUBGROUP (the two-sided form is what makes it
   one; the naive preimage of the integral matrices is only a submonoid) and is
   OPEN, because `Mat₂(𝒪_L)` is open in `Mat₂(L) ≅ End_L(L²)`. That reduces to
   `𝒪_L` open in `L`, i.e. a full `ℤ_p`-lattice in a finite-dimensional
   `ℚ_p`-space is open — the `isOpen_span_natCast_pow` /
   `isOpen_pow_of_natCast_mem` technique of
   `Fermat/FLT/Modularity/TateModule.lean:2752`, `:2793` verbatim
   (`Module.Free.chooseBasis`'s `equivFun` +
   `IsModuleTopology.continuous_of_linearMap` + `isOpen_set_pi` +
   `IsLocalRing.isOpen_maximalIdeal_pow`).
3. `U` has finite index: `Subgroup.quotient_finite_of_isOpen`
   (`Mathlib/Topology/Algebra/OpenSubgroup.lean:287`) composed with
   `Subgroup.finiteIndex_of_finite_quotient` (`Mathlib/GroupTheory/Index.lean:719`)
   — mathlib has no single bundled name, which is why an earlier grep missed
   it, and the tree already open-codes the composition at `ModThree.lean:37176`.
4. `Λ := ⨆ i, τ (gᵢ) '' Λ₀` over coset representatives is `Γ F`-stable: for `g`
   and each `i`, `g * gᵢ = gⱼ * u` with `u ∈ U`, so `τ(g * gᵢ) '' Λ₀ = τ(gⱼ) ''
   Λ₀`. The Lean cost here is the `Finset` bookkeeping over
   `Quotient (QuotientGroup.leftRel U)`, not the mathematics.
5. `Λ` is f.g. and torsion-free over the DVR `𝒪_L`, hence free, and it spans
   `L²`, hence of rank `2` — giving `e : Λ ≃ₗ[𝒪_L] (Fin 2 → 𝒪_L)`.
6. CONTINUITY of `g ↦ e.conj (τ g |_Λ)` into
   `moduleTopology 𝒪_L (End_{𝒪_L} (Fin 2 → 𝒪_L))`. Go through `ℤ_p` rather than
   `𝒪_L` — the module topology over `𝒪_L` agrees with the one over `ℤ_p`
   because `𝒪_L` is module-finite over `ℤ_p`, `End_{𝒪_L}(𝒪_L²)` is then finite
   free over `ℤ_p`, and continuity into a finite free `ℤ_p`-module is continuity
   of coordinates, each of which factors through the already-continuous `τ` and
   the topological embedding `ℤ_p ↪ ℚ_p`. This is the expensive half; the
   doctrine's warning about concrete modules inside topology-carrying steps
   applies in full, so keep the intermediate lemmas stated over an ABSTRACT
   module.

**STATUS 2026-07-27 — THIS LEAF IS NOW PROVEN, AND STEPS 1–4 WITH IT.** The
six-step plan below is history except for STEPS 5–6, which are cut out as the
single named leaf `exists_framed_of_finiteIndex_stabilizer` above. What was
built, in dependency order:

* `isTorsionFree_padicInt_of_algebra` — the recorded friction of step 2;
* `isOpen_span_range_basis_padic` — the "first genuinely NEW lemma" predicted
  below. It is NOT the `isOpen_span_natCast_pow` statement; what carries it is
  `PadicInt.isOpenEmbedding_coe` (`ℤ_p` is open in `ℚ_p` because the closed
  unit ball of an ultrametric field is open) plus `isOpen_set_pi` through
  `b.equivFun`;
* `isOpen_integralClosure_padic` — step 2's openness half, over
  `Module.Basis.localizationLocalization` and its `..._span` lemma, which
  supplies exactly the "`ℚ_p`-basis of `L` drawn from a `ℤ_p`-basis of `𝒪_L`"
  the paragraph below asks for. That is also what mathlib's own
  `IsIntegralClosure.rank` uses, so the construction was already in the pin;
* `exists_framed_stableLattice_of_finiteDimensional_padic` — steps 1–4, in
  MATRIX form (no `charFrob`);
* this theorem — three rewrites converting that matrix identity into the
  `charFrob` statement (`LinearMap.charpoly_toMatrix`, `Matrix.charpoly_map`,
  `Module.Basis.repr_sum_self`). Note `charFrob` never had to be pushed through
  the lattice step: it is `charpoly` of `τ` at ONE group element, and a matrix
  identity at every element implies it at that one.

STEPS 1–3 ARE CONFIRMED LOOKUPS — the incantations, each COMPILED in a scratch
module against this file's own import surface on 2026-07-27, so the next owner
can paste them rather than rediscover them. Nothing below is a guess.

```
-- step 1
example {F : Type u} [Field F] [NumberField F] : CompactSpace (Field.absoluteGaloisGroup F) :=
  inferInstanceAs (CompactSpace (AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F))

-- step 2, set-up: `L` carries no `Algebra ℤ_p` instance, it must be built
noncomputable local instance : Algebra ℤ_[p] L :=
  ((algebraMap ℚ_[p] L).comp (algebraMap ℤ_[p] ℚ_[p])).toAlgebra
local instance : IsScalarTower ℤ_[p] ℚ_[p] L := IsScalarTower.of_algebraMap_eq fun _ => rfl

-- step 2, `𝒪_L`: finite, free, and of the expected rank
example : Module.Finite ℤ_[p] ↥(integralClosure ℤ_[p] L) :=
  IsIntegralClosure.finite ℤ_[p] ℚ_[p] L ↥(integralClosure ℤ_[p] L)
example : Module.Free ℤ_[p] ↥(integralClosure ℤ_[p] L) :=
  IsIntegralClosure.module_free ℤ_[p] ℚ_[p] L ↥(integralClosure ℤ_[p] L)
example : Module.finrank ℤ_[p] ↥(integralClosure ℤ_[p] L) = Module.finrank ℚ_[p] L :=
  IsIntegralClosure.rank ℤ_[p] ℚ_[p] L ↥(integralClosure ℤ_[p] L)

-- step 3
example {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    (U : Subgroup G) (hU : IsOpen (U : Set G)) : U.FiniteIndex :=
  haveI : Finite (G ⧸ U) := Subgroup.quotient_finite_of_isOpen U hU
  Subgroup.finiteIndex_of_finite_quotient
```

THE ONE HYPOTHESIS THAT IS NOT INFERRED, and the only friction found in that
pass: `IsIntegralClosure.module_free` and `IsIntegralClosure.rank` want
`Module.IsTorsionFree ℤ_[p] L`, which instance search does NOT produce. It is
three lines, and it is `comap` along `ℤ_p ↪ ℚ_p` from the field instance:

```
local instance : Module.IsTorsionFree ℤ_[p] L :=
  Module.IsTorsionFree.comap (S := ℚ_[p]) (algebraMap ℤ_[p] ℚ_[p])
    (fun _ hr => isRegular_iff_ne_zero.mpr fun h => (isRegular_iff_ne_zero.mp hr)
      ((map_eq_zero_iff _ (IsFractionRing.injective ℤ_[p] ℚ_[p])).mp h))
    (fun r m => algebraMap_smul ℚ_[p] r m)
```

(DONE 2026-07-27, see the STATUS block above: the openness half of step 2 is
`isOpen_integralClosure_padic`. The prediction in the paragraph below was right
on both counts — it was the first genuinely new lemma, and it did need a
`ℚ_p`-basis of `L` drawn from a `ℤ_p`-basis of `𝒪_L`; what it did NOT need was
`IsLocalRing.isOpen_maximalIdeal_pow`, since `ℤ_p` open in `ℚ_p` is
`PadicInt.isOpenEmbedding_coe` outright.)

What was NOT yet confirmed at handover was the openness half of step 2 — `𝒪_L`
open in `L`.
`TateModule.lean`'s `isOpen_span_natCast_pow` is about an ideal INSIDE a ring
carrying the `ℤ_q`-module topology, so it is the right technique
(`chooseBasis`'s `equivFun` + `isOpen_set_pi`) but not the right statement; the
`L`-version additionally needs `ℤ_p` open in `ℚ_p` (the closed unit ball is
open by ultrametricity) and a `ℚ_p`-basis of `L` drawn from a `ℤ_p`-basis of
`𝒪_L`, which `IsIntegralClosure.rank` above is exactly what makes possible.
Treat that as the first genuinely NEW lemma of this development.

**THE ONE PIN GAP THAT ROUND 5 NAMED HAS CLOSED — this is a correction to that
audit, checked mechanically on 2026-07-27.** Round 5 recorded that the
transitivity lemma step 6 opens with (`IsModuleTopology R M ↔ IsModuleTopology
S M` for `S` module-finite over `R` with the `R`-module topology) is "NOT in our
mathlib pin", is present only in the reference project, and that "vendoring the
three is the recommended first commit of the development" — with a warning that
they would be FREE-FLOATING until step 6 consumes them, so the development
could not be landed incrementally. **All of that is now moot: the vendoring
already happened**, as part of the 109-module automorphic vendoring, and the
lemmas arrived WITH consumers, so there is no free-floating problem and no
first commit to pay for. Refuting check, one line:
`grep -rn 'moduleTopology.trans\|of_continuous_isOpenMap_algebraMap' Fermat/`
— `moduleTopology.trans` at
`Fermat/FLT/Mathlib/Topology/Algebra/Module/ModuleTopology.lean:169`,
`IsModuleTopology.trans` at `:194`, `of_continuous_isOpenMap_algebraMap` at
`:212`, already consumed at `DivisionAlgebra/Finiteness.lean:144,512`,
`NumberField/AdeleRing.lean:341` and inside `ModuleTopology.lean` itself. So
this leaf can be attacked as one whole task with nothing owed up front.

FAITHFULNESS NOTE. `j` is NOT asserted injective and `B` is NOT asserted to be
a domain, local, or to carry `ℤ_p` injectively: none of those is needed by the
consumer (`carayol_threeadic_of_totallyDefinite_heckeCharacter`), all of them
are already theorems downstream from the mere existence of a
characteristic-zero comparison embedding
(`injective_of_finite_padicInt_charZero`,
`injective_algebraMap_of_ringHom_charZero`,
`isLocalRing_of_finite_padicInt_domain`,
`exists_domain_coefficientRing_of_ringHom`), and a weaker conclusion is a
weaker obligation on whoever proves this. -/
theorem exists_stableLattice_galoisRep_of_finiteDimensional_padic
    (p : ℕ) [Fact p.Prime]
    {F : Type u} [Field F] [NumberField F]
    {L : Type u} [Field L] [Algebra ℚ_[p] L] [Module.Finite ℚ_[p] L]
    [TopologicalSpace L] [IsTopologicalRing L] [IsModuleTopology ℚ_[p] L]
    (τ : GaloisRep F L (Fin 2 → L)) :
    ∃ (B : Type u) (_ : CommRing B) (_ : Algebra ℤ_[p] B)
      (_ : Module.Finite ℤ_[p] B),
      letI : TopologicalSpace B := moduleTopology ℤ_[p] B
      letI : IsTopologicalRing B := isTopologicalRing_moduleTopology_of_finite p B
      ∃ (τB : GaloisRep F B (Fin 2 → B)) (j : B →+* L),
        ∀ w : HeightOneSpectrum (NumberField.RingOfIntegers F),
          (τB.charFrob w).map j = τ.charFrob w := by
  classical
  obtain ⟨B, hCR, hAlg, hFin, ρ, j, b, hb⟩ :=
    exists_framed_stableLattice_of_finiteDimensional_padic p τ
  letI : TopologicalSpace B := moduleTopology ℤ_[p] B
  letI : IsTopologicalRing B := isTopologicalRing_moduleTopology_of_finite p B
  refine ⟨B, hCR, hAlg, hFin, ρ, j, fun w => ?_⟩
  set g : Field.absoluteGaloisGroup F :=
    Field.absoluteGaloisGroup.map (algebraMap F (w.adicCompletion F))
      (Field.AbsoluteGaloisGroup.adicArithFrob w) with hg
  have hρ : ρ.toLocal w (Field.AbsoluteGaloisGroup.adicArithFrob w) = ρ g := rfl
  have hτ : τ.toLocal w (Field.AbsoluteGaloisGroup.adicArithFrob w) = τ g := rfl
  show ((ρ.toLocal w (Field.AbsoluteGaloisGroup.adicArithFrob w)).charpoly).map j =
    (τ.toLocal w (Field.AbsoluteGaloisGroup.adicArithFrob w)).charpoly
  rw [hρ, hτ, ← LinearMap.charpoly_toMatrix (ρ g) (Pi.basisFun B (Fin 2)),
    ← LinearMap.charpoly_toMatrix (τ g) b, ← Matrix.charpoly_map]
  congr 1
  ext k i
  rw [Matrix.map_apply, LinearMap.toMatrix_apply, LinearMap.toMatrix_apply,
    Pi.basisFun_apply, Pi.basisFun_repr, hb g i]
  rw [Module.Basis.repr_sum_self]

/-- **STEP 2 of the Carayol node — CARAYOL's Théorème (A): the `3`-adic
Galois realization of the quaternionic Hecke character** (PROVEN ASSEMBLY
since 2026-07-27 over the two leaves declared immediately above; HOISTED
2026-07-27 out of the body of
`carayol_threeadic_realization_of_heckePackage`, where it lived as the
internal `have hcar`).

ASSEMBLY (2026-07-27) — the INTEGRALITY CUT, i.e. route (1) of the ROUND-3
AUDIT in `carayol_threeadic_realization_of_heckePackage`, taken. This node
splits at the only joint that audit left open:

* `exists_threeadicField_realization_of_totallyDefinite_heckeCharacter` — the
  CITATION half, Carayol's Théorème (A) over the FIELD `E_λ`, which is what the
  theorem literally produces. It no longer asserts that the representation
  preserves a lattice;
* `exists_stableLattice_galoisRep_of_finiteDimensional_padic` — the ELEMENTARY
  half, Serre I §1: a continuous representation of the compact `Γ_F` over a
  finite extension of `ℚ_3` preserves a lattice. Its docstring carries the
  complete six-step in-tree work plan and the refuting checks.

What the assembly itself does is only the composition of comparison embeddings:
`ι ∘ j` where `j : B →+* L` and `ι : L →+* ℚ̄_3`, through `Polynomial.map_map`.
That the Frobenius characteristic polynomials survive the lattice step is
asserted by the lattice leaf, not re-derived here.

Given the Jacquet–Langlands package produced by
`exists_totallyDefinite_heckeCharacter_of_heckePackage` — a totally definite
rigidified quaternion algebra `D/F`, a level datum `𝒮` and an `E`-algebra
character `θ` of `TotallyDefiniteQuaternionAlgebra.HeckeAlgebra D 𝒮` seeing
the traces of `heckeF` — attach to it the `3`-adic member of its compatible
system, with the local–global compatibility that identifies Frobenius
characteristic polynomials with Hecke polynomials at the places outside
`badF`. This is the genuine literature joint of the whole node: Carayol,
*Sur les représentations `ℓ`-adiques associées aux formes modulaires de
Hilbert*, Ann. Sci. ÉNS (4) **19** (1986) 409–468, Théorème (A) (§0.7) and
its even-degree quaternionic predecessor Théorème (B) (§0.9); Taylor,
*On Galois representations associated to Hilbert modular forms*, Invent.
Math. **98** (1989), for the remaining cases. Carayol builds the compatible
system by decomposing the `ℓ`-adic cohomology `H¹(M_K ⊗_F F̄, ℱ_λ)` of the
Shimura curves attached to the quaternion algebra under the Hecke action
(op. cit. §0.10–0.11), using his earlier analysis of their bad reduction;
no pin material reaches that.

The hypothesis is the EXISTENTIAL package verbatim, not `D`/`𝒮`/`θ` as
binders. That is deliberate: the conclusion does not mention `D`, so the
two forms are equivalent, and the existential form keeps the interface
byte-identical to the internal `have` this replaces, which is what makes
the consumer a one-line `exact`.

`hbad2`, `hbad3`, `hbadℓ` are what entitle the conclusion to a matching
clause exactly outside `badF` — the `3`-adic member ramifies at the places
over `2`, `3` and `ℓ`, and at a ramified place `charFrob` is not even
choice-independent. `hirrF` is the cuspidality/non-Eisenstein condition
without which Théorème (A) is not a theorem about this eigensystem at all.
See the consumer's docstring for the full round-2/3/4/5 hypothesis audits.

`hFeven` is deliberately ABSENT from this statement: the parity bit is
consumed entirely by STEP 1, where the quaternion algebra is produced. See
that leaf's docstring.

CIRCULARITY GUARD (inherited from pillar β, load-bearing): no discharge
through `Family.lean`, `Lift.lean`, or `Modularity/Interface.lean`. -/
theorem carayol_threeadic_of_totallyDefinite_heckeCharacter
    {ℓ : ℕ} (hℓodd : Odd ℓ) [Fact ℓ.Prime] (hℓ5 : 5 ≤ ℓ)
    {O : Type u} [CommRing O] [IsDomain O] [TopologicalSpace O]
    [IsTopologicalRing O] [Algebra ℤ_[ℓ] O] [IsLocalRing O]
    [Module.Finite ℤ_[ℓ] O] [IsModuleTopology ℤ_[ℓ] O]
    (hZinj : Function.Injective (algebraMap ℤ_[ℓ] O))
    {ρ : GaloisRep ℚ O (Fin 2 → O)}
    (hrank : Module.rank O (Fin 2 → O) = 2)
    (hρ : IsHardlyRamified hℓodd hrank ρ)
    {k : Type u} [Field k] [Finite k] [Algebra ℤ_[ℓ] k]
    [TopologicalSpace k] [DiscreteTopology k]
    {W : Type v} [AddCommGroup W] [Module k W] [Module.Finite k W]
    [Module.Free k W]
    (hW : Module.rank k W = 2) {ρbar : GaloisRep ℚ k W}
    (hρbar : IsHardlyRamified hℓodd hW ρbar)
    (hirr : ρbar.IsIrreducible)
    (π : O →+* k) (hπsurj : Function.Surjective π)
    (hπ : ∀ (q : ℕ) (hq : q.Prime), q ≠ 2 → q ≠ ℓ →
      (ρ.charFrob hq.toHeightOneSpectrumRingOfIntegersRat).map π =
        ρbar.charFrob hq.toHeightOneSpectrumRingOfIntegersRat)
    (F : Type u) [Field F] [NumberField F]
    (hFtr : NumberField.IsTotallyReal F) (hFgal : IsGalois ℚ F)
    (hirrF : (ρbar.map (algebraMap ℚ F)).IsIrreducible)
    (E : Type u) [Field E] [NumberField E]
    (badF : Finset (HeightOneSpectrum (NumberField.RingOfIntegers F)))
    (heckeF : HeightOneSpectrum (NumberField.RingOfIntegers F) →
      Polynomial E)
    (ψℓ : E →+* AlgebraicClosure ℚ_[ℓ])
    (ιO : O →+* AlgebraicClosure ℚ_[ℓ]) (hιO : Function.Injective ιO)
    (hmod : ∀ w ∉ badF,
      ((ρ.map (algebraMap ℚ F)).charFrob w).map ιO =
        (heckeF w).map ψℓ)
    (hbad2 : ∀ w : HeightOneSpectrum (NumberField.RingOfIntegers F),
      (2 : NumberField.RingOfIntegers F) ∈ w.asIdeal → w ∈ badF)
    (hbad3 : ∀ w : HeightOneSpectrum (NumberField.RingOfIntegers F),
      (3 : NumberField.RingOfIntegers F) ∈ w.asIdeal → w ∈ badF)
    (hbadℓ : ∀ w : HeightOneSpectrum (NumberField.RingOfIntegers F),
      (ℓ : NumberField.RingOfIntegers F) ∈ w.asIdeal → w ∈ badF)
    (hJL : ∃ (D : Type u) (_ : DivisionRing D) (_ : Algebra F D)
      (_ : _root_.IsQuaternionAlgebra F D)
      (_ : _root_.IsQuaternionAlgebra.IsTotallyDefinite F D)
      (_ : _root_.IsQuaternionAlgebra.NumberField.WithRigidification F D)
      (p : ℕ) (𝒮 : _root_.TotallyDefiniteQuaternionAlgebra.U₁Data F E p)
      (θ : _root_.TotallyDefiniteQuaternionAlgebra.HeckeAlgebra D 𝒮 →ₐ[E] E),
      ∀ (w : HeightOneSpectrum (NumberField.RingOfIntegers F))
        (hwS : w ∉ 𝒮.S) (hwQ : w ∉ 𝒮.Q), w ∉ badF →
        (heckeF w).coeff 1 =
          -θ (_root_.TotallyDefiniteQuaternionAlgebra.HeckeAlgebra.T D 𝒮 w hwS hwQ)) :
    ∃ (B : Type u) (_ : CommRing B)
      (_ : Algebra ℤ_[3] B) (_ : Module.Finite ℤ_[3] B),
      letI : TopologicalSpace B := moduleTopology ℤ_[3] B
      letI : IsTopologicalRing B :=
        isTopologicalRing_moduleTopology_of_finite 3 B
      ∃ (τF : GaloisRep F B (Fin 2 → B))
        (ψ₃ : E →+* AlgebraicClosure ℚ_[3])
        (ιB : B →+* AlgebraicClosure ℚ_[3]),
        ∀ w ∉ badF, (τF.charFrob w).map ιB = (heckeF w).map ψ₃ := by
  -- STEP 2a — the CITATION half, over the field `E_λ`: Carayol's Théorème (A)
  -- literally produces an `E_λ`-adic representation, and this is that statement
  -- with nothing added.
  obtain ⟨L, hFieldL, hAlgL, hFinL, τ, ψ₃, ι, hmatch⟩ :=
    exists_threeadicField_realization_of_totallyDefinite_heckeCharacter hℓodd hℓ5
      hZinj hrank hρ hW hρbar hirr π hπsurj hπ F hFtr hFgal hirrF E badF heckeF
      ψℓ ιO hιO hmod hbad2 hbad3 hbadℓ hJL
  -- the topology on `L` must be FIXED before anything whose type mentions it is
  -- elaborated; it is not a choice, `Module.Finite ℚ_3 L` pins it
  letI : TopologicalSpace L := moduleTopology ℚ_[3] L
  haveI : IsModuleTopology ℚ_[3] L := ⟨rfl⟩
  haveI : IsTopologicalRing L := isTopologicalRing_moduleTopology_of_finite_padic 3 L
  -- STEP 2b — the ELEMENTARY half, Serre I §1: `Γ_F` is compact, so `τ`
  -- preserves a lattice and descends to a coefficient ring module-finite over
  -- `ℤ_3`, with the Frobenius characteristic polynomials unmoved (conjugation
  -- does not move a characteristic polynomial).
  obtain ⟨B, hCR, hAlg, hFin, τF, j, hj⟩ :=
    exists_stableLattice_galoisRep_of_finiteDimensional_padic 3 (F := F) τ
  letI : TopologicalSpace B := moduleTopology ℤ_[3] B
  -- the assembly is the composition of the two comparison embeddings
  exact ⟨B, hCR, hAlg, hFin, τF, ψ₃, ι.comp j, fun w hw => by
    rw [← Polynomial.map_map, hj w, hmatch w hw]⟩

/-- **The Hilbert-modular `3`-adic realization, geometric core**
(PROVEN assembly since 2026-07-27, over the two hoisted citation leaves
`exists_totallyDefinite_heckeCharacter_of_heckePackage` (Jacquet–Langlands)
and `carayol_threeadic_of_totallyDefinite_heckeCharacter` (Carayol 1986,
Théorème (A)/(B) / Taylor 1989); until then a sorry node whose two `have`s
carried the same two statements without names): a Hilbert-modular Hecke
eigensystem `(E, heckeF)` over the
totally real field `F` — witnessed as modular by the `ℓ`-adic matching
clause `hmod` for the lift `ρ` — has a `3`-adic Galois realization: a
representation `τF` of `G_F` on a rank-`2` lattice over a local DOMAIN
`B` module-finite over `ℤ_3` (classically the integers of the
completion `E_λ`, `λ | 3`), matching the Hecke polynomials through a
place `ψ₃` of `E` over `3` and a comparison embedding `ιB`.

CITATION-SHRINKING CUT (2026-07-25, extended the same day). This leaf
replaces the earlier `exists_threeadic_realization_domain_of_heckePackage`
citation, which is now a PROVEN assembly over it. Six of that
statement's components were pulled out of the citation and proven
in-tree as the five bricks above; the citation now asserts strictly
less:

* `TopologicalSpace B`, `IsTopologicalRing B`, `IsModuleTopology ℤ_3 B`
  — GONE. The coefficient ring's topology is not a choice: the three
  components together pin it to be the `ℤ_3`-module topology, so the
  statement below simply USES that topology, and
  `isTopologicalRing_moduleTopology_of_finite` supplies the ring-topology
  and module-topology facts. The citation no longer has to know that its
  coefficient ring is a topological ring at all;
* `Function.Injective ιB` — GONE, by
  `injective_of_finite_padicInt_charZero`: a domain module-finite over
  `ℤ_p` has NO nonzero prime lying over `(0)`, so any ring map of it into
  a characteristic-zero field is injective;
* `Function.Injective (algebraMap ℤ_3 B)` — GONE, by
  `injective_algebraMap_of_ringHom_charZero`: the mere EXISTENCE of the
  comparison embedding `ιB` into `ℚ̄_3` forces it, since
  `ιB ∘ algebraMap` is a map of `ℤ_3` into a characteristic-zero field.
  This is the hypothesis that feeds the downstream free-lattice
  normalization `free_of_finite_of_algebraMap_padicInt_injective`, so
  `ℤ_3`-freeness of `B` is now TWO formal steps away from the citation
  rather than one assumption plus one step;
* `IsLocalRing B` — GONE (2026-07-25, second pass), by
  `isLocalRing_of_finite_padicInt_domain`: a DOMAIN module-finite over
  `ℤ_3` is `3`-adically complete, hence Henselian, hence has no
  nontrivial idempotents in `B ⧸ 3B` — and a finite ring with only
  trivial idempotents is local. The 2026-07-25 audit below predicted
  this needed the unbundled `spectralNorm` layer to be bundled first;
  it does not — completeness enters ONLY through the idempotent lift,
  and the missing pin half (precompleteness of a finite free module)
  is four short lemmas, proven above.

* `IsDomain B` — GONE (2026-07-26), by
  `exists_domain_coefficientRing_of_ringHom`: the kernel of the
  comparison embedding `ιB` is prime because `ℚ̄_3` is a domain, so the
  whole package descends to `B ⧸ ker ιB` — still module-finite over
  `ℤ_3`, still carrying the representation (by the coefficient base
  change `exists_charFrob_map_algebraMap`), still receiving the induced
  embedding — and no `ιB`-image of a Frobenius characteristic polynomial
  moves. Note this is a QUOTIENT, not a lift: unlike the locality brick
  it uses no completeness at all.

NARROWED AGAIN 2026-07-26 — the matching clause no longer claims
local–global compatibility at the places over `3`, via the new
hypothesis `hbad3`. This one is a FAITHFULNESS repair as well as a
shrink, and the gap it closes is sharp:

* the exceptional set `badF` is supplied from the `ℓ`-adic side, and
  `hmod` constrains it only through the `ℓ`-adic `ρ`. Since `ρ` is
  hardly ramified it is ramified only at `2` and `ℓ`, so `hmod` gives
  `badF` no reason whatever to contain the places of `F` over `3` —
  and for the intended instantiation it does not have to;
* but the representation this leaf PRODUCES is the `3`-adic member of
  the compatible system, and that member RAMIFIES at every place over
  `3`. At a ramified place `charFrob` is not even independent of the
  choices: `GaloisRepTransport`'s module docstring records that two
  arithmetic Frobenii at one prime differ by an inertia element, so no
  choice-free comparison holds there. Carayol's Théorème (A) asserts
  local–global compatibility at `w`, and the identification of the
  Frobenius characteristic polynomial with the Hecke polynomial only
  at the places where the `λ`-adic member is unramified.
* So the OLD statement asserted, at every `w | 3`, an equality that the
  literature does not give and that would hold only by accident. The
  hypothesis `hbad3 : ∀ w, (3 : 𝓞 F) ∈ w.asIdeal → w ∈ badF` deletes
  exactly those instances and nothing else.

It costs the consumers NOTHING, which is why this is a shrink rather
than a relocation: `badF` is chosen existentially upstream
(`exists_heckePackage_of_seed`) and the matching clause only WEAKENS
when it grows, so `exists_potentialModularityWitness_of_five_le`
discharges `hbad3` by replacing `badF` with
`badF ∪ {w : w ∋ 3}` — a `Finset` by
`finite_heightOneSpectrum_mem_of_ne_zero` above — and carries the
enlarged set into the witness. No other citation assumes more; the
`PotentialModularityWitness` docstring already said `badF` contains
the places over `2`, `3` and `ℓ`, so this makes the formal statement
say what the interface always claimed. The twin Brauer node
`blggt_threeadicBrauerSum_of_witness` never had this gap — it excludes
`q = 3` explicitly and chooses its own exceptional set `S₁`.

NARROWED A THIRD TIME 2026-07-26 (round 3) — the same repair, COMPLETED,
by the two further hypotheses `hbad2` and `hbadℓ`. Round 2 excluded the
places over `3` and stopped there; the exclusion set is only honest once
it is closed under "wherever the `3`-adic member can ramify", and that
set is the places over `2`, `3` AND `ℓ`:

* over `2`: `ρ` is hardly ramified, so it IS allowed to ramify at `2`,
  and for the intended instantiation it does. The Hilbert newform
  attached to `ρ|_{G_F}` then has level divisible by the places over
  `2`, so the `3`-adic member of its compatible system ramifies there
  too, and Carayol's local–global compatibility gives no Frobenius
  characteristic polynomial at such a place. Round 2 reasoned that
  `hmod` "constrains `badF` only through `ρ`, which ramifies only at `2`
  and `ℓ`" and concluded the `3`-places were the gap; that is right
  about where the gap is WIDEST, but it is not an argument that
  `badF` contains the `2`-places — `badF` is a free parameter of this
  statement and nothing here forces it to;
* over `ℓ`: the `3`-adic member is unramified at `w | ℓ` only because
  `ρ` is FLAT at `ℓ`, i.e. because the newform's level is prime to `ℓ`.
  That is an extra literature input (Fontaine–Laffaille / the
  weight-`2` level–flatness dictionary) on top of Carayol, and it was
  nowhere cited by this leaf. Excluding the places over `ℓ` removes the
  dependence on it outright, so the citation is now Carayol's
  Théorème (A) and nothing else.

Both are discharged exactly as `hbad3` was, and at the same call site:
`exists_potentialModularityWitness_of_five_le` now enlarges `badF`
three times by `exists_finset_superset_of_places_mem`, at `2`, `3` and
`ℓ`. Cost to consumers: zero. What this removes from the citation is
the claim of a Frobenius-characteristic-polynomial identity at places
where the representation it produces is ramified, where `charFrob` is
not even choice-independent.

What remains is the genuinely geometric core: the automorphic
construction of a `2`-dimensional `3`-adic representation of `G_F` with
prescribed Frobenius characteristic polynomials, over the ring of
integers of the coefficient field's completion. Carayol builds the
compatible system by decomposing the `ℓ`-adic cohomology
`H¹(M_K ⊗_F F̄, ℱ_λ)` of the Shimura curves attached to a quaternion
algebra over `F` under the Hecke action (op. cit. §0.10–0.11), using
his earlier analysis of their bad reduction; that is what no pin
material can reach.

Literature (verified against the source, 2026-07-25): Carayol, *Sur
les représentations ℓ-adiques associées aux formes modulaires de
Hilbert*, Ann. Sci. ÉNS (4) **19** (1986) 409–468 —
Théorème (A) (§0.7, p. 410): for `π` a cuspidal automorphic
representation of `GL₂` over the totally real `F` of the relevant
weight, there is a finite extension `E` of the field of definition
`ℚ(π)` and a STRICTLY COMPATIBLE system `{σ_λ}` of continuous
`2`-dimensional `E_λ`-adic representations of `Gal(F̄/F)` whose
restriction to every local Weil group `W_𝔭` is the local Langlands
image `σ_λ(π_𝔭)` — in particular the Frobenius characteristic
polynomial at each good place is the Hecke polynomial;
Théorème (B) (§0.9) is the weaker version proven first, over a
quaternion algebra ramified at a chosen finite place when `[F : ℚ]` is
even, with (A) deduced from (B) by cyclic base change for `GL(2)`;
Taylor, *On Galois representations associated to Hilbert modular
forms*, Invent. Math. **98** (1989) (the remaining cases, by
congruences). The passage from Carayol's `E_λ`-adic representation to
the lattice model over the local ring `B = O_{E_λ}` used here is the
standard compactness argument (Serre, *Abelian ℓ-adic
representations*, I §1); by the ROUTE AUDIT below it is deliberately
NOT split off as a separate leaf.

PIN AUDIT (2026-07-24, re-checked 2026-07-25): the mathlib pin has no
Hilbert modular forms, no Shimura curves and no automorphic Galois
representations of any kind (`grep Hilbert.*modular`, `grep Shimura`
over `Mathlib/`: nothing in this direction), so the construction
itself is irreducibly a citation. What the pin DOES have is the
coefficient-ring commutative algebra and the module-topology layer,
which is why those have been split off and proven (five bricks above,
plus `free_of_finite_of_algebraMap_padicInt_injective` and the four
precompleteness lemmas that feed the locality brick).

RESIDUAL BOOKKEEPING — NOW DISCHARGED (audited 2026-07-25 morning,
CLOSED 2026-07-25 evening). The audit read: "`IsLocalRing B` stays in
the citation; its formal proof from 'domain, module-finite over `ℤ_3`'
needs a Henselian/completeness input, and the pin has `HenselianRing`
and `IsAdicComplete.henselianRing` but no instance connecting them to
module-finite algebras, no `IsNonarchimedeanLocalField` instance for
finite extensions of `ℚ_p`, and only the unbundled `spectralNorm`
layer — so the bridge would have to be built (idempotent lifting along
`3`-adic completeness of a finite free `ℤ_3`-module, then 'connected
finite ring is local')."

That bridge IS the route, and it has been built: see
`isLocalRing_of_finite_padicInt_domain` above. Two corrections to the
audit for the record: (i) the valuation-uniqueness reading is a detour
— idempotent lifting alone suffices, and never mentions a valuation;
(ii) the only genuinely missing pin ingredient was PRECOMPLETENESS of a
finite free module (the pin has the `IsHausdorff` half only), which is
`isPrecomplete_of_free_finite` and its three supporting lemmas above.

TERMINALITY AUDIT, component by component (2026-07-26 — the whole
conclusion was re-audited for further shrinks. Result: the one
component that was a formal consequence of the others, `IsDomain B`,
has been removed; every component that remains is terminal, and the
argument for each is below. Do not re-litigate without new evidence).

* `B : Type u`, `CommRing B`, `Algebra ℤ_3 B` — the carrier and the
  structures without which `Module.Finite ℤ_3 B` cannot be stated.
  Nothing to remove.
* `Module.Finite ℤ_3 B` — TERMINAL. Not a consequence of the other
  components: a ring receiving `ℤ_3` and mapping to `ℚ̄_3` need not be
  module-finite over `ℤ_3`. Classically it is the INTEGRALITY of the
  realization — Carayol's `E_λ`-adic representation plus the
  stable-lattice step (Serre I §1) — and the route audit below records
  why splitting that step off trades one citation for two. It is also
  what feeds `free_of_finite_of_algebraMap_padicInt_injective`
  downstream, so it cannot simply be dropped.
* `IsDomain B` — REMOVED, see the shrink bullet above. It was the only
  component of the old conclusion that was a formal consequence of the
  others, and it is worth recording exactly why it took work rather
  than a line: the descent to `B ⧸ ker ιB` moves a GALOIS
  REPRESENTATION, so it needs a coefficient base change with a
  `charFrob` compatibility. That bridge existed in-tree only in
  `Modularity/Patching.lean`, only over the base field `ℚ`, and that
  module is not in this one's import cone; the three declarations
  `charFrob_baseChange_of_numberField`, `charFrob_conj_of_numberField`
  and `exists_charFrob_map_algebraMap` above are the general-base
  replacement.
* `τF`, `ψ₃`, `ιB` and the matching clause — TERMINAL, and they are
  terminal TOGETHER rather than one at a time. Taken in isolation each
  of the three data is cheap (`ψ₃` exists because a number field embeds
  into the algebraically closed characteristic-zero `ℚ̄_3`; `ιB` exists
  because `Frac B` is then a finite extension of `ℚ_3`), but none of
  them may be quantified away, because it is precisely their COUPLING
  by the matching clause that is Carayol's Théorème (A). Two rewrites
  of this block were audited and rejected as going the WRONG WAY, i.e.
  as making the citation assert MORE: replacing `ψ₃`/`ιB` by a single
  `E →+* Frac B` (that additionally asserts the Hecke field embeds in
  the coefficient field, which the present pair does not), and moving
  `ψ₃` from the existential into a hypothesis (that asserts the whole
  compatible system rather than one member). The trace/determinant
  restatement was audited separately below and is equivalent, not
  weaker.

Also audited and deliberately NOT done: restating the matching clause
as the pair `ιB (tr τF(Frob_w)) = ψ₃ a_w`, `ιB (det τF(Frob_w)) =
ψ₃ d_w` (the "eigenvalue-to-trace dictionary"). Both sides of the
present clause are monic of degree `2` (`hmod` forces `heckeF w` to be
one), so the trace/determinant form is EQUIVALENT, not weaker: it
would relocate polynomial bookkeeping into this file without removing
anything from the citation.

ROUND-3 AUDIT (2026-07-26). The conclusion was audited a second time
against the round-2 verdict and NO component came out: the verdict
above stands unchanged, and the shrink round 3 found is on the
HYPOTHESIS side (`hbad2`, `hbadℓ`). Three routes were examined; the
first is the only one that can ever remove `Module.Finite ℤ_3 B`, and
its price is now known exactly.

(1) THE FIELD FORM IS A STRICT WEAKENING — so the ROUTE AUDIT's "the
cut trades one citation for two" is CONDITIONAL, not absolute. Write

* (Old) `∃ B, CommRing B, Algebra ℤ_3 B, Module.Finite ℤ_3 B`, `τF`
  over `Fin 2 → B`, `ψ₃`, `ιB`, matching — the present statement;
* (New) `∃ L, Field L, Algebra ℚ_3 L, FiniteDimensional ℚ_3 L`, `τ`
  over `Fin 2 → L`, `ψ₃`, `ι : L →+* ℚ̄_3`, matching.

Then **Old ⟹ New using only material already in this file**: descend
to `B' := B ⧸ ker ιB`, a domain (the `IsDomain` shrink above),
module-finite over `ℤ_3`, receiving `ℤ_3` injectively
(`injective_algebraMap_of_ringHom_charZero`) hence `ℤ_3`-FREE
(`free_of_finite_of_algebraMap_padicInt_injective`); take
`L := Frac B'`, of the same finite rank over `ℚ_3`, and base-change the
representation along `B' → L` (`charFrob_baseChange_of_numberField`,
`exists_charFrob_map_algebraMap`). So New is a CONSEQUENCE of Old:
strictly less to take on faith, and what it drops is exactly the
INTEGRALITY — the existence of a Galois-stable lattice — and nothing
else. New ⟹ Old is precisely Serre I §1, and that is the entire price.
The moment the lattice step is PROVEN rather than cited, the cut
becomes a strict improvement; it is the only remaining route to
removing `Module.Finite ℤ_3 B`, and it is new mathematics, not
restructuring.

**ROUTE (1) HAS BEEN TAKEN (2026-07-27), one level down — at STEP 2.**
It is not this node that was cut but its Carayol half,
`carayol_threeadic_of_totallyDefinite_heckeCharacter`, which is now a
PROVEN assembly of
`exists_threeadicField_realization_of_totallyDefinite_heckeCharacter`
(the citation, in the FIELD form written as "New" above) and
`exists_stableLattice_galoisRep_of_finiteDimensional_padic` (Serre
I §1). That is the right level: this node's conclusion is unchanged,
its consumers are unchanged, and the integrality claim has moved OUT of
the citation and INTO an elementary open leaf. The lattice leaf carries
the six-step work plan below, verbatim, on the declaration it is
actually about. NOTE the frontier count RISES by one at this cut, which
is disclosure and not regression: a component that was previously
invisible inside a citation is now a named, ownable obligation.

PIN RECON for that step (done 2026-07-26 so the next owner need not
repeat it). Statement: `Γ F` compact, `τ : Γ F → GL_2(L)` continuous,
`L/ℚ_3` finite ⟹ a `Γ F`-stable `O_L`-lattice exists (take the
`O_L`-span of `τ(g_i)·O_L²` over coset representatives of the open
subgroup stabilizing one lattice). Where each ingredient stands:
* compactness of the absolute Galois group — AVAILABLE, but NOT by
  `inferInstance`: the tree's own
  `instance [Algebra.IsAlgebraic K L] : CompactSpace (L ≃ₐ[K] L)`
  (`Fermat/FLT/Mathlib/FieldTheory/Galois/Infinite.lean:93`) is
  strictly better than mathlib's `IsGalois`-based one (algebraicity
  only, no separability), but `Field.absoluteGaloisGroup` is a `def`,
  so it must be summoned as
  `inferInstanceAs (CompactSpace (AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F))`
  — the idiom already used at `ModThree.lean:37174`;
* `O_L` module-finite over `ℤ_3` — `IsIntegralClosure.finite`
  (`Mathlib/RingTheory/DedekindDomain/IntegralClosure.lean:174`): `ℤ_3`
  is a Noetherian integrally closed domain (both free from
  `IsDiscreteValuationRing ℤ_[p]`, `PadicIntegers.lean:521`) and
  `L/ℚ_3` is finite separable;
* the lattice is FREE of rank `2` — `O_L` is Dedekind and local
  (`isLocalRing_of_finite_padicInt`, in this file), hence a DVR, hence
  a PID; alternatively `IsIntegralClosure.module_free`
  (`IntegralClosure.lean:182`) gives `Module.Free ℤ_3 O_L` outright;
* `O_L` OPEN in `L` — **CORRECTED 2026-07-26 (round 5): the "no direct
  pin support, this is where the work starts" verdict was WRONG.** The
  technique is in-tree and worked out:
  `isOpen_span_natCast_pow` and `isOpen_pow_of_natCast_mem`
  (`Fermat/FLT/Modularity/TateModule.lean:2752`, `:2793`) prove exactly
  "a lattice is open" for a ring carrying the `ℤ_q`-module topology, by
  transporting through `Module.Free.chooseBasis`'s `equivFun` +
  `IsModuleTopology.continuous_of_linearMap` + `isOpen_set_pi` +
  `IsLocalRing.isOpen_maximalIdeal_pow ℤ_[q] n`. The same file supplies
  `compactSpace_of_isModuleTopology_padicInt` (`:2725`),
  `t2Space_of_isModuleTopology_padicInt` (`:2736`) and
  `exists_pow_subset_of_mem_nhds` (`:2812`);
* an open subgroup of a compact group has finite index — **CORRECTED
  2026-07-26 (round 5): no covering argument is owed.** It is
  `Subgroup.quotient_finite_of_isOpen`
  (`Mathlib/Topology/Algebra/OpenSubgroup.lean:287`) composed with
  `Subgroup.finiteIndex_of_finite_quotient`
  (`Mathlib/GroupTheory/Index.lean:719`); mathlib has no single bundled
  name, which is why the earlier grep missed it, and the tree already
  open-codes the composition at `ModThree.lean:37176`;
* transporting `τ` to a `GaloisRep F O_L (Fin 2 → O_L)` is the
  EXPENSIVE half, not the lattice: it needs `moduleTopology ℤ_3 O_L` to
  agree with the subspace topology from `L`, and the doctrine warning
  about concrete modules inside topology-carrying steps applies in
  full. Round 5 confirms this is where ALL the remaining work is, and
  that it is a genuine hole rather than a lookup: a repo-wide sweep of
  BOTH trees found **no** `GaloisRep` descent to a subring of any kind
  — no `GaloisRep.restrictScalars`, no Galois-stable-lattice
  development, and `GaloisRep.baseChange`
  (`GaloisRep.lean:161`) goes only UP, along an `Algebra A B`. The
  `p`-adic ring-of-integers hull
  (`exists_padicIntegers_dvr_hull_of_continuousSMul`,
  `PadicIntegralClosure.lean:320`) does NOT close it either: it starts
  from an `R` that is already `Module.Finite ℤ_[p]`, so it presupposes
  the integrality this step is trying to produce. (The reverse half is
  in-tree and cheap — `finiteDimensional_padic_fractionRing`,
  `PadicIntegralClosure.lean:136` — which is the Old ⟹ New direction.)
  This is a self-contained development, not a lemma — and it may
  not be sorried in passing, since a sorried lattice step IS the "one
  citation for two" the ROUTE AUDIT rejects.

WORK PLAN for that development (round 5, so the next owner starts at
step 4 rather than at a blank page). Steps 1–3 are now lookups, step 5
is standard, and essentially all of the cost is in step 6:

1. `CompactSpace (Γ F)` — the `inferInstanceAs` idiom above.
2. `U := {g | τ g '' Λ₀ ⊆ Λ₀ ∧ τ g⁻¹ '' Λ₀ ⊆ Λ₀}` is a SUBGROUP (the
   two-sided form is what makes it one; the naive preimage of the
   integral matrices is only a submonoid) and is OPEN, because
   `Mat₂(O_L)` is open in `Mat₂(L) ≅ End_L(L²)`. That reduces to
   `O_L` open in `L`, i.e. a full `ℤ_3`-lattice in a finite-dimensional
   `ℚ_3`-space is open — the `TateModule.lean:2752` technique verbatim,
   with `chooseBasis` + `isOpen_set_pi` and `ℤ_3` open in `ℚ_3`.
3. `U` has finite index — the two-lemma composition above.
4. `Λ := ⨆ i, τ (gᵢ) '' Λ₀` over coset representatives is `Γ F`-stable:
   for `g` and each `i`, `g * gᵢ = gⱼ * u` with `u ∈ U`, so
   `τ(g * gᵢ) '' Λ₀ = τ(gⱼ) '' Λ₀`. The Lean cost here is the `Finset`
   bookkeeping over `Quotient (QuotientGroup.leftRel U)`, not the
   mathematics.
5. `Λ` is f.g. and torsion-free over the DVR `O_L`, hence free, and it
   spans `L²`, hence of rank `2` — giving `e : Λ ≃ₗ[O_L] (Fin 2 → O_L)`.
6. CONTINUITY of `g ↦ e.conj (τ g |_Λ)` into
   `moduleTopology O_L (End_{O_L} (Fin 2 → O_L))`. The route that
   avoids the concrete-module blowup the doctrine warns about is to
   go through `ℤ_3` rather than `O_L`: the module topology over `O_L`
   agrees with the one over `ℤ_3` because `O_L` is module-finite over
   `ℤ_3`, `End_{O_L}(O_L²)` is then finite free over `ℤ_3`, and
   continuity into a finite free `ℤ_3`-module is continuity of
   coordinates, each of which factors through the already-continuous
   `τ` and the topological embedding `ℤ_3 ↪ ℚ_3`.

   **The one pin gap this exposes**: the transitivity lemma that step 6
   opens with — for `S` an `R`-algebra with `[Module.Finite R S]` and
   `[IsModuleTopology R S]`, the `S`-module topology on an `S`-module
   `M` COINCIDES with the `R`-module topology (an equality of
   topologies, and correspondingly `IsModuleTopology R M ↔
   IsModuleTopology S M`) — is NOT in our mathlib pin. It IS in the
   reference project as `moduleTopology.trans` / `IsModuleTopology.trans`
   (`~/cs/FLT/FLT/Mathlib/Topology/Algebra/Module/ModuleTopology.lean`,
   `:169` and `:194` respectively, alongside
   `of_continuous_isOpenMap_algebraMap` at `:212`, which is the natural
   tool for "`O_L` carries the `ℤ_3`-module topology"). That project's
   pin has drifted, so these need a signature audit rather than a
   verbatim copy. Vendoring the three is the recommended first commit
   of the development.

   **PIN GAP RE-VERIFIED (2026-07-26, a later owner.)** Both halves of
   that claim were re-checked mechanically rather than taken on trust,
   and both hold: `IsModuleTopology.trans` / `moduleTopology.trans` are
   absent from OUR pin (no match anywhere in `Mathlib/`), and present in
   the reference project — `lemma trans` at
   `~/cs/FLT/FLT/Mathlib/Topology/Algebra/Module/ModuleTopology.lean:194`
   with `of_continuous_isOpenMap_algebraMap` at `:212`, as recorded. So
   the vendoring step is real work and not a lookup.

   **BOTH PARAGRAPHS ABOVE ARE RETIRED (2026-07-27) — THE VENDORING HAS
   LANDED, AND IT LANDED WITH CONSUMERS.** The re-verification was
   correct when it was run and is now false: `moduleTopology.trans`,
   `IsModuleTopology.trans` and `of_continuous_isOpenMap_algebraMap` are
   in THIS tree, at
   `Fermat/FLT/Mathlib/Topology/Algebra/Module/ModuleTopology.lean:169`,
   `:194` and `:212`, brought in by the 109-module automorphic vendoring.
   Refuting check, one line:
   `grep -rn 'moduleTopology.trans' Fermat/`. They are already consumed
   at `DivisionAlgebra/Finiteness.lean:144,512`,
   `NumberField/AdeleRing.lean:341` and inside `ModuleTopology.lean`
   itself, so the free-floating warning that used to end this item — "the
   three vendored lemmas would be FREE-FLOATING until step 6 consumes
   them, so steps 1–6 have to arrive together" — no longer applies
   either: there is no first commit to pay for, and step 6 can open
   directly with `IsModuleTopology.trans`. Budgeting it as one whole task
   is still the right call, but for its own size and not for this reason.

(2) FIXING THE CARRIER — returning the representation over the
integers of `ℚ_3(ψ₃ E)`, i.e. over `O_{E_λ}` — REJECTED. It does make
`Module.Finite ℤ_3 B` provable (`ψ₃ E` is generated over `ℚ_3` by one
algebraic element, so `ℚ_3(ψ₃ E)/ℚ_3` is finite), but it is Carayol's
Théorème (A) VERBATIM where the present statement is only a
consequence of it: it asserts MORE, which is the same objection that
already sank `E →+* Frac B`. The weaker-looking variant — keep `B`
abstract, replace `Module.Finite ℤ_3 B` by `Algebra.IsIntegral ℤ_3 B`
and add `ιB '' B ⊆ ℚ_3(ψ₃ E)` — falls to the same objection, since the
added inclusion is again the coefficient-field claim.

(3) LETTING THE CITATION CHOOSE ITS OWN EXCEPTIONAL SET `bad₃ ⊇ badF`
(as the twin `blggt_threeadicBrauerSum_of_witness` does with `S₁`) —
REJECTED. It does formally weaken the conclusion and the call site
could absorb it for nothing, but it removes no INPUT: the construction
that proves the weak form is the same construction in full. That is
the test which separates it from `hbad2`/`hbad3`/`hbadℓ` — those
delete instances the literature does not cover; this one only blurs
instances that it does.

NARROWED A FOURTH TIME 2026-07-26 (round 4) — CUSPIDALITY, via the new
hypothesis `hirrF : (ρbar.map (algebraMap ℚ F)).IsIrreducible`. Rounds
2 and 3 closed the RAMIFICATION gap (`hbad2`/`hbad3`/`hbadℓ`); this one
closes the other half of the same faithfulness question — *which
eigensystems the cited theorem is a theorem about at all*.

* Carayol's Théorème (A) is a statement about a CUSPIDAL automorphic
  representation `π` of `GL₂/F`. It says nothing whatever about an
  Eisenstein eigensystem: the "compatible system" attached to one is a
  direct sum of one-dimensional characters, and its construction is
  class field theory, not the `ℓ`-adic cohomology of a Shimura curve.
* The only automorphy input this leaf has is `hmod`, and `hmod` does
  not distinguish the two: it says the Hecke polynomials interpolate
  the Frobenius characteristic polynomials of `ρ|_{G_F}` away from
  `badF`, which is equally true of an Eisenstein system when
  `ρbar|_{G_F}` is reducible. So the OLD statement claimed a Carayol
  realization on instances Théorème (A) does not reach.
* `hirrF` deletes exactly those instances. In the intended chain it is
  precisely the non-Eisenstein condition: the maximal ideal of the
  Hecke algebra cut out by `ρbar|_{G_F}` is non-Eisenstein iff
  `ρbar|_{G_F}` is irreducible, and that is the hypothesis under which
  `exists_heckeEigensystem_of_congruentSeed` produces `heckeF` in the
  first place (it is also the hypothesis of the Carayol 1994 descent
  quoted in `MoretBaillySeed`'s `O₀` field).
* NOT implied by `hirr`. Irreducibility of `ρbar` over `ℚ` does NOT
  give irreducibility over the large totally real Galois `F`;
  restriction to `G_F` can break it. That is exactly why the
  Moret–Bailly leaf has to assert image preservation separately, and
  why `hirrF` is a genuine restriction rather than a derived fact.
* Cost to consumers: ZERO, like the three `hbad` hypotheses.
  `exists_potentialModularityWitness_of_five_le` already OBTAINS
  `hirrF` from `exists_moretBailly_seed_of_five_le` (where it is proven
  in-tree from image preservation by
  `isIrreducible_map_of_range_surjective`) and already passes it to
  `exists_heckePackage_of_seed`; it now passes it here too, through the
  two assemblies.

ROUND-4 AUDIT — three further candidates examined and REJECTED. All
three are recorded so the next owner does not spend a round on them.

(4) THREADING THE `MoretBaillySeed` IN AS A HYPOTHESIS — REJECTED as a
FAKE narrowing, and this is the sharpest instance yet of the test. It
looks like exactly the automorphy certificate this leaf is missing
("`heckeF` comes from a Hilbert newform"), and it would be free at the
call site. But `MoretBaillySeed`'s own VACUITY AUDIT (see that
structure's docstring) records that the type is JUNK-SATISFIABLE: its
`modular₀` field degenerates to the Hilbert–Blumenthal point's own
`matchℓ` with `hecke₀` renamed, and repo-wide the structure is never
consumed. A hypothesis that every instance can satisfy with junk
deletes NO instance, so adding it would weaken the statement on paper
and narrow nothing in fact. **The test a candidate hypothesis must
pass: does it FAIL somewhere the literature also fails?** `hbad2`,
`hbad3`, `hbadℓ` and `hirrF` pass it; the seed does not.

(5) PINNING THE WEIGHT — adding `∀ w ∉ badF, (heckeF w).coeff 0 =
(Ideal.absNorm w.asIdeal : E)` (parallel weight `2`, trivial
nebentypus) — REJECTED as REDUNDANT, not merely as blurring.
`IsHardlyRamified.det` already pins `det ρ` to the `ℓ`-adic cyclotomic
character (see `HardlyRamified/Defs.lean`), so the constant coefficient
of `(ρ.map (algebraMap ℚ F)).charFrob w` is the cyclotomic value at
`Frob_w`, i.e. `Nw`; `hmod` then transports that to `heckeF w`. The
clause is therefore a formal CONSEQUENCE of hypotheses already present
and deletes no instance. Monicity and `natDegree = 2` are consequences
of `hmod` for the same reason. (Independently it would also have been
route-(3) blurring: Théorème (A) covers cuspidal `π` of every
admissible weight, so restricting the determinant would delete
instances the literature DOES cover.)

(6) TOTAL ODDNESS of `ρ|_{G_F}` — REJECTED as REDUNDANT, same source:
`IsHardlyRamified.det` fixes the determinant outright, so oddness is
already a consequence of `hρ` and no instance is deleted.

ROUND-5 AUDIT (2026-07-26). Round 5 asked the one question rounds 2–4
left open: is the exclusion set `{w | w ∣ 2} ∪ {w ∣ 3} ∪ {w ∣ ℓ}`
COMPLETE — i.e. can the `3`-adic member still ramify at some
`w ∉ badF`, so that a FIFTH `hbad` is owed? Answer: NO, the set is
complete, and the proof is recorded here because the missing fifth
hypothesis is otherwise an entirely reasonable thing for the next
auditor to propose (it does delete instances, so the sharp test does
not by itself dispose of it).

(7) EXCLUDING THE LEVEL — adding `hbadlevel`, i.e. demanding that
`badF` also contain the places where the Hilbert newform underlying
`heckeF` is ramified — REJECTED as REDUNDANT. The hypotheses already
force that level to be supported over `2` and `ℓ`:

* `hirrF` gives `ρbar|_{G_F}` irreducible, hence `ρ|_{G_F}`
  irreducible (a reducible representation has reducible reduction);
* let `{σ_λ}` be the compatible system of the cuspidal `π` underlying
  `heckeF`. Both `σ_ℓ` and `ρ|_{G_F}` are unramified outside a finite
  set, so both factor through `Γ_{F,S}` for one finite `S`, and `hmod`
  says their Frobenius characteristic polynomials agree at every
  `w ∉ badF` — a set of density `1`. Chebotarev plus Brauer–Nesbitt
  therefore give `σ_ℓ^{ss} ≅ (ρ|_{G_F})^{ss}`;
* by irreducibility that is an isomorphism `σ_ℓ ≅ ρ|_{G_F}` on the
  nose, and `ρ` is hardly ramified, so `σ_ℓ` is unramified outside the
  places over `2` and `ℓ`. Local–global compatibility at `w ∤ ℓ` then
  says `π_w` is unramified there, so the level of `π` is supported
  over `2` and `ℓ`, and `σ_3` is unramified outside the places over
  `2`, `3` and `ℓ` — exactly the set already excluded by `hbad2`,
  `hbad3`, `hbadℓ`. No instance is deleted.

THE INTERLOCK, which is the load-bearing part and was not visible
before round 4: **rounds 3 and 4 are NOT independent narrowings —
`hirrF` is what makes `hbad2`/`hbad3`/`hbadℓ` SUFFICIENT.** Drop
`hirrF` from the argument above and it stops at
`σ_ℓ^{ss} ≅ (ρ|_{G_F})^{ss}`, which does not bound the ramification of
`σ_ℓ` itself: a `σ_ℓ` that is STEINBERG at some `w₀ ∤ 2·3·ℓ` — a
nonsplit extension of characters, with unipotent nontrivial inertia at
`w₀` — has unramified semisimplification, satisfies `hmod` at `w₀`,
and yet its `3`-adic partner `σ_3` is ramified at `w₀`, where
`charFrob` is not choice-independent. So without `hirrF` a genuine
fifth exclusion IS owed. Do not remove or weaken `hirrF` on the
grounds that it "only" handles Eisenstein systems; it is also the
reason the ramification exclusion is closed.

Recorded for the same reason, as a correction to the round-4 note's
"NOT implied by `hirr`": the CONVERSE does hold. `Γ F → Γ ℚ` is
injective with image the subgroup fixing `F`, so `ρbar.map` is a
restriction, and an invariant subspace for `Γ ℚ` is one for `Γ F` —
hence `hirrF ⟹ hirr`, and `hirr` is now a formally redundant
hypothesis of this statement. It is deliberately LEFT IN PLACE:
removing it deletes no instance, changes the signature of two proven
assemblies and their call site, and would cost the integrator a
conflict for nothing.

RESIDUAL FAITHFULNESS GAP, NAMED (2026-07-26, round 4; flagged, NOT
repaired here — it is a cut-level change). Even with `hirrF`, the true
hypothesis of Théorème (A) — that `heckeF` IS the Hecke eigensystem of
a cuspidal Hilbert newform over `F` — is NOT stateable at this pin,
because the pin has no Hilbert modular forms (PIN AUDIT above).
`hirrF` is the sharpest in-tree PROXY for it, not the thing itself:
for an abstract `heckeF` satisfying `hmod` and `hirrF`, what this leaf
asserts is still "`ρ|_{G_F}` sits in a compatible system", of which
automorphy is the smuggled ingredient. Closing that gap properly means
DEFINING Hilbert modular forms and their eigensystems, and rewiring the
three interfaces that currently record "modular" as bare Frobenius data
(`MoretBaillySeed`, `exists_heckePackage_of_seed`,
`PotentialModularityWitness`). That is a decomposition decision, not a
repair available inside this declaration; it is recorded here so the
next audit does not mistake `hirrF` for a complete fix.

HALF OF THAT GAP IS NOW CLOSED — HILBERT MODULAR FORMS ARE IN THE TREE
(2026-07-27). The clause "the pin has no Hilbert modular forms", and the
PIN AUDIT it rests on, are RETIRED. They were true of `Mathlib/` and they
were FALSE of `~/cs/FLT`, which nobody had costed. What replaces them is a
smaller and much sharper obstruction, stated below so the next owner
attacks that instead of re-running the sweep.

*What is now available.* The reference project carries a complete
development of weight-`2` automorphic forms on a TOTALLY DEFINITE
QUATERNION ALGEBRA over a totally real field, with their Hecke algebras —
`TotallyDefiniteQuaternionAlgebra`, `WeightTwoAutomorphicForm.LevelStruct`,
`HeckeAlgebra`, `HeckeAlgebra.T` — over adele rings, restricted products
and Haar characters. By Jacquet–Langlands this is the Hilbert-modular
eigensystem data Théorème (A) is about. Its import closure was measured
(109 modules, 20,688 lines) and VENDORED into this tree under
`Fermat/FLT/{AutomorphicForm,QuaternionAlgebra,DivisionAlgebra,HaarMeasure,
NumberField,DedekindDomain,Hacks,Mathlib}/…`, where it BUILDS GREEN against
our pin. The refuting check, for whoever doubts this paragraph next:
`grep -rn 'HeckeAlgebra\.T' Fermat/FLT/AutomorphicForm/` and
`lake build Fermat.FLT.AutomorphicForm.QuaternionAlgebra.HeckeOperators.Concrete`.

*Cost of the vendoring, measured rather than estimated.* Exactly ONE
statement in those 20,688 lines is unproven, and it is not a pin problem:
the reference discharges `isFiniteRelIndex_Δ` (finiteness of `Δ_g/Fˣ`,
Voight Lemma 17.7.13) with its tactic `knownin1980s`, which is
`axiom knownin1980s {P : Prop} : P` — a proof of an ARBITRARY proposition.
That axiom is inadmissible here, so it is not vendored and its one use
became a sorried leaf. Pin drift cost exactly TWO repairs, both recorded
at their sites: an auto-generated instance name whose suffix encoded the
root module (`RestrictedProduct.instModuleCoe_fLT`, now named explicitly),
and one `Algebra.smul_def` rewrite in `DivisionAlgebra/Finiteness.lean`
that stopped firing because `InfinitePlace K` now unfolds to a subtype.

*THE OBSTRUCTION THAT REMAINS, and why this leaf still cannot consume any
of it.* The formalization is QUATERNIONIC, and a totally definite
quaternion algebra over `F` unramified at every finite place exists only
when `[F : ℚ]` is EVEN (the ramification set must have even cardinality,
and here it is exactly the set of infinite places). This leaf quantifies
over an abstract totally real Galois `F` with no parity constraint, so:

- as the CONCLUSION of a sub-leaf — "`heckeF` is the eigensystem of a
  quaternionic form over `F`" — it is **FALSE for odd-degree `F`**, and
  cutting this leaf that way would manufacture a false leaf, which is
  worse than leaving it open;
- as a HYPOTHESIS on this leaf — adding `Even (Module.finrank ℚ F)` — it
  fails this docstring's own sharp test (round-4 block): Carayol's
  Théorème (A) covers Hilbert newforms over totally real `F` of EVERY
  degree, so the hypothesis would delete instances the literature DOES
  cover. That is route-(3) blurring, already rejected here twice.

So the honest next step is a Jacquet–Langlands layer, or the parity datum
recorded upstream where `F` is CHOSEN (Taylor's construction is free to
take `[F : ℚ]` even, exactly as it is free to take `F` linearly disjoint
from `ℚ(ζ_ℓ)`) — i.e. a new field on `MoretBaillySeed` threaded through
`exists_potentialModularityWitness_of_five_le`, which is the same
cut-level change the paragraph above already names, now with a much
smaller residue: no longer "define Hilbert modular forms", but "record one
parity bit and cite Jacquet–Langlands".

**JACQUET–LANGLANDS CONSUMER — THAT LANDED (2026-07-27). The paragraph
above is now HISTORY, and the "FREE-FLOATING" warning it used to end with
is RETIRED.** The parity route was taken, in the form the paragraph names.
Three things changed and they are worth stating precisely, because the
next auditor will otherwise re-derive them:

*(1) Where the parity bit is recorded.* NOT on `MoretBaillySeed` — one
level deeper, and cheaper. `exists_evenDegree_totallyReal_of_sup_eq_top`
(a new sorry leaf, elementary field theory: adjoin a real quadratic
`ℚ(√p)` ramified at a prime unramified in `L·F`) enlarges the field that
`exists_totallyReal_point_of_geometricallyIrreducible` returns, carrying
the `F`-rational point up along `HasRationalPoint.of_ringHom` and the
disjointness join along with it. `Even (Module.finrank ℚ F)` is then a
plain existential conjunct threaded through
`exists_hilbertBlumenthalPoint_of_five_le` and
`exists_moretBailly_seed_of_five_le`, obtained in
`exists_potentialModularityWitness_of_five_le`, and handed down through
the two `*_threeadic_realization_*` assemblies to `hFeven` here. No
structure field was added and no carrier changed shape.

*(2) Why this is NOT the route-(3) blurring rejected just above.* The
sharp test asks whether a hypothesis DELETES INSTANCES the literature
covers. It does not, because this leaf is not universally quantified in
practice: it has exactly ONE call site, and that call site now PRODUCES
an even-degree `F` rather than receiving an arbitrary one. The bit is
recorded where `F` is chosen, which is precisely the disposition the
rejected reading lacked. An auditor who wants to re-open this should
attack `exists_evenDegree_totallyReal_of_sup_eq_top` (is the enlargement
really free?), not `hFeven`.

*(3) What the skeleton below actually consumes, and what it does NOT
claim.* STEP 1 asserts the EXISTENCE of a division ring `D/F` with
`IsQuaternionAlgebra F D` and a
`IsQuaternionAlgebra.NumberField.WithRigidification F D` — the latter is
the vendored development's own encoding of "split at every finite place",
and by Albert–Brauer–Hasse–Noether a totally definite such `D` exists
exactly when `[F : ℚ]` is even, which is the sole use of `hFeven` in the
whole node. It then asserts an `E`-algebra character `θ` of
`TotallyDefiniteQuaternionAlgebra.HeckeAlgebra D 𝒮` matching the traces
of `heckeF`. **`D`, `𝒮` and `θ` are all existentially quantified**, which
is what keeps the statement true: asserting anything about an ARBITRARY
rigidified `D` would be false, whereas asserting the existence of a good
one is exactly Jacquet–Langlands.

**RETRACTED 2026-07-27 — the rest of this item, as originally written, was
WRONG, and it is worth stating loudly because it recorded a successor task
that did not exist.** It read: "the vendored development has NO
`IsTotallyDefinite` predicate — definiteness is a source COMMENT there
('if `D` isn't totally definite all the definitions below are garbage
mathematically but they typecheck'), not a hypothesis", and concluded that
"nothing in the formal statement PINS the witnessing `D` to be totally
definite, so a future owner discharging STEP 1 must supply definiteness
from outside the formalism (or add the predicate)". That is true of the
REFERENCE project's `AutomorphicForm/` sources and FALSE of this tree:
`Fermat/FLT/Mathlib/Algebra/IsQuaternionAlgebra.lean` defines the class
`IsQuaternionAlgebra.IsTotallyDefinite F D`, and
`AutomorphicForm/QuaternionAlgebra/Basic.lean` and
`.../HeckeOperators/Concrete.lean` already consume it. STEP 1's existential
now CARRIES `IsTotallyDefinite F D`, so the witnessing `D` is pinned and
the "supply definiteness from outside the formalism" task is discharged
rather than deferred. Refuting check, one line:
`grep -rn 'class IsTotallyDefinite' Fermat/`.

STEP 2 is Carayol's Théorème (A) proper, stated as an IMPLICATION from
STEP 1's package to this node's conclusion, so that `hJL` is consumed and
`D`/`𝒮`/`θ` genuinely appear in the proof term — which is what puts the
109-module vendored subtree into the used-constant cone of
`fermat_last_theorem`. Before this, that subtree was free-floating.

*(4) BOTH STEPS ARE NOW TOP-LEVEL LEAVES (2026-07-27).* They were internal
sorried `have`s, which no frontier scan can name and no dispatcher can own
— the node reported as a single leaf carrying two unrelated citations. They
are now `exists_totallyDefinite_heckeCharacter_of_heckePackage` (STEP 1)
and `carayol_threeadic_of_totallyDefinite_heckeCharacter` (STEP 2),
declared immediately above this docstring, and THIS node is a proven
assembly: one `exact`, no tactic block. Nothing about the mathematics
moved; the audits in this docstring apply verbatim, and each step's own
docstring records what is left to prove in it. `hFeven` is threaded to
STEP 1 only, so the parity bit's single use is now mechanically visible
rather than asserted in a comment.

ROUTE AUDIT (dichotomy, 2026-07-24; unchanged — do not re-litigate
without new evidence). Two routes to the `3`-adic member of the
compatible system were weighed at this joint:

* the **Carayol/Taylor automorphic route** taken here — attach the
  `3`-adic representation directly to the Hilbert eigensystem
  `(E, heckeF)` recorded by the potential-modularity carrier. Its
  input is exactly the data the carrier already carries, and its
  output is exactly the carrier's `3`-adic block; the only depth is
  the automorphic construction itself, which no pin material can
  reach;
* the **motivic/Tate-module route** — realize the eigensystem inside
  the `3`-adic Tate module of the Moret–Bailly Hilbert–Blumenthal
  abelian variety, avoiding automorphic forms. Rejected: it needs
  `A/F` itself (not just its eigensystem) threaded through
  `exists_heckePackage_of_seed`, which would widen the `MoretBailly`
  interface with a full abelian-scheme package, and it still needs
  Carayol's local-global compatibility to identify Frobenius
  characteristic polynomials with the Hecke polynomials at good
  places — i.e. the same citation plus an abelian-variety development
  the pin also lacks. Strictly deeper at every node.

A third cut — this leaf returning the representation over the local
FIELD `E_λ`, with a Galois-stable lattice chosen afterwards — was
rejected earlier for the same reason: the stable-lattice step is
itself a citation (compactness of `G_F` plus Serre I §1), so the cut
trades one citation for two.

SOUNDNESS AUDIT (both ways, 2026-07-24, inherited): (i) direct — for
the intended instantiation (`(E, heckeF)` the eigensystem of the
Hilbert newform attached to `ρ|_{G_F}` by
`exists_heckePackage_of_seed`) this is Carayol/Taylor verbatim; for an
abstract eigensystem merely satisfying `hmod` the
abstract-quantification caveat applies (the hypothesis that `heckeF`
IS a newform eigensystem lives in this citation), and (ii) collapse —
the hypothesis set (an irreducible hardly ramified mod-`ℓ`
representation, `ℓ ≥ 5`) is classically unsatisfiable (headline
below), so the statement is classically true for every package.

CIRCULARITY GUARD (inherited from pillar β, load-bearing): no
discharge through `Family.lean`, `Lift.lean`, or
`Modularity/Interface.lean`. -/
theorem carayol_threeadic_realization_of_heckePackage
    {ℓ : ℕ} (hℓodd : Odd ℓ) [Fact ℓ.Prime] (hℓ5 : 5 ≤ ℓ)
    {O : Type u} [CommRing O] [IsDomain O] [TopologicalSpace O]
    [IsTopologicalRing O] [Algebra ℤ_[ℓ] O] [IsLocalRing O]
    [Module.Finite ℤ_[ℓ] O] [IsModuleTopology ℤ_[ℓ] O]
    (hZinj : Function.Injective (algebraMap ℤ_[ℓ] O))
    {ρ : GaloisRep ℚ O (Fin 2 → O)}
    (hrank : Module.rank O (Fin 2 → O) = 2)
    (hρ : IsHardlyRamified hℓodd hrank ρ)
    {k : Type u} [Field k] [Finite k] [Algebra ℤ_[ℓ] k]
    [TopologicalSpace k] [DiscreteTopology k]
    {W : Type v} [AddCommGroup W] [Module k W] [Module.Finite k W]
    [Module.Free k W]
    (hW : Module.rank k W = 2) {ρbar : GaloisRep ℚ k W}
    (hρbar : IsHardlyRamified hℓodd hW ρbar)
    (hirr : ρbar.IsIrreducible)
    (π : O →+* k) (hπsurj : Function.Surjective π)
    (hπ : ∀ (q : ℕ) (hq : q.Prime), q ≠ 2 → q ≠ ℓ →
      (ρ.charFrob hq.toHeightOneSpectrumRingOfIntegersRat).map π =
        ρbar.charFrob hq.toHeightOneSpectrumRingOfIntegersRat)
    (F : Type u) [Field F] [NumberField F]
    (hFtr : NumberField.IsTotallyReal F) (hFgal : IsGalois ℚ F)
    -- PARITY (2026-07-27): `[F : ℚ]` EVEN. This is NOT a narrowing of the
    -- literature statement smuggled in here — it is a bit RECORDED UPSTREAM,
    -- where `F` is CHOSEN by the Moret–Bailly construction
    -- (`exists_evenDegree_totallyReal_of_sup_eq_top`, threaded through
    -- `exists_hilbertBlumenthalPoint_of_five_le` and
    -- `exists_moretBailly_seed_of_five_le`), exactly as `F` is already chosen
    -- linearly disjoint from the fixed field of `ker ρbar`. The sole call site
    -- supplies it, so no instance the literature covers is lost. See the
    -- "JACQUET–LANGLANDS CONSUMER" block in the docstring.
    (hFeven : Even (Module.finrank ℚ F))
    -- CUSPIDALITY (round-4 narrowing, 2026-07-26): Carayol's Théorème (A)
    -- is a theorem about CUSPIDAL `π`, and `hmod` alone does not exclude an
    -- Eisenstein eigensystem. See the docstring's round-4 block.
    (hirrF : (ρbar.map (algebraMap ℚ F)).IsIrreducible)
    (E : Type u) [Field E] [NumberField E]
    (badF : Finset (HeightOneSpectrum (NumberField.RingOfIntegers F)))
    (heckeF : HeightOneSpectrum (NumberField.RingOfIntegers F) →
      Polynomial E)
    (ψℓ : E →+* AlgebraicClosure ℚ_[ℓ])
    (ιO : O →+* AlgebraicClosure ℚ_[ℓ]) (hιO : Function.Injective ιO)
    (hmod : ∀ w ∉ badF,
      ((ρ.map (algebraMap ℚ F)).charFrob w).map ιO =
        (heckeF w).map ψℓ)
    (hbad2 : ∀ w : HeightOneSpectrum (NumberField.RingOfIntegers F),
      (2 : NumberField.RingOfIntegers F) ∈ w.asIdeal → w ∈ badF)
    (hbad3 : ∀ w : HeightOneSpectrum (NumberField.RingOfIntegers F),
      (3 : NumberField.RingOfIntegers F) ∈ w.asIdeal → w ∈ badF)
    (hbadℓ : ∀ w : HeightOneSpectrum (NumberField.RingOfIntegers F),
      (ℓ : NumberField.RingOfIntegers F) ∈ w.asIdeal → w ∈ badF) :
    ∃ (B : Type u) (_ : CommRing B)
      (_ : Algebra ℤ_[3] B) (_ : Module.Finite ℤ_[3] B),
      letI : TopologicalSpace B := moduleTopology ℤ_[3] B
      letI : IsTopologicalRing B :=
        isTopologicalRing_moduleTopology_of_finite 3 B
      ∃ (τF : GaloisRep F B (Fin 2 → B))
        (ψ₃ : E →+* AlgebraicClosure ℚ_[3])
        (ιB : B →+* AlgebraicClosure ℚ_[3]),
        ∀ w ∉ badF, (τF.charFrob w).map ιB = (heckeF w).map ψ₃ :=
  -- STEP 1 — JACQUET–LANGLANDS (`exists_totallyDefinite_heckeCharacter_of_heckePackage`),
  -- the ONLY step that consumes `hFeven`: `[F : ℚ]` even ⟹ a totally definite
  -- quaternion algebra `D/F` split at every finite place exists, and the Hilbert
  -- eigensystem `(E, heckeF)` transfers to an `E`-algebra character `θ` of its
  -- Hecke algebra.  STEP 2 — CARAYOL's Théorème (A)
  -- (`carayol_threeadic_of_totallyDefinite_heckeCharacter`): attach to `θ` its
  -- `3`-adic Galois realization with local–global compatibility outside `badF`.
  -- Both were internal `have`s until 2026-07-27; hoisting them gave each an
  -- ownable name and made this node a proven assembly.  See their docstrings —
  -- in particular STEP 1's, which RETRACTS the "no `IsTotallyDefinite`
  -- predicate" claim in the JACQUET–LANGLANDS CONSUMER block above and pins the
  -- witnessing `D` totally definite.
  carayol_threeadic_of_totallyDefinite_heckeCharacter hℓodd hℓ5 hZinj hrank hρ hW
      hρbar hirr π hπsurj hπ F hFtr hFgal hirrF E badF heckeF ψℓ ιO hιO hmod hbad2
      hbad3 hbadℓ
    (exists_totallyDefinite_heckeCharacter_of_heckePackage hℓodd hℓ5 hZinj hrank hρ hW
      hρbar hirr π hπsurj hπ F hFtr hFgal hFeven hirrF E badF heckeF ψℓ ιO hιO hmod
      hbad2 hbad3 hbadℓ)

/-- **The Hilbert-modular `3`-adic realization, integral-domain form**
(PROVEN assembly, 2026-07-25 — Carayol 1986 / Taylor 1989 at one
remove): a Hilbert-modular Hecke eigensystem `(E, heckeF)` over the
totally real field `F` — witnessed as modular by the `ℓ`-adic matching
clause `hmod` for the lift `ρ` — has a `3`-adic Galois realization
over a local DOMAIN `B` which is module-finite over `ℤ_3`, carries the
`ℤ_3`-module topology, receives `ℤ_3` injectively, and embeds into
`ℚ̄_3`.

ASSEMBLY (2026-07-25): this used to BE the citation; it is now a
proven assembly over the strictly narrower geometric core
`carayol_threeadic_realization_of_heckePackage` plus the five
coefficient-ring bricks proven above — the module topology is a ring
topology and is the module topology
(`isTopologicalRing_moduleTopology_of_finite`), locality of the
coefficient ring is the Henselian property of `ℤ_3`
(`isLocalRing_of_finite_padicInt_domain`), and both injectivity
components follow from the existence of the comparison embedding into
the characteristic-zero field `ℚ̄_3`
(`injective_of_finite_padicInt_charZero`,
`injective_algebraMap_of_ringHom_charZero`). Nothing else changes: the
coefficient ring, the representation, the place `ψ₃`, the embedding
`ιB` and the Hecke-polynomial matching clause are carried verbatim
from the citation, so there is no lattice change and no charpoly to
re-compute.

NARROWED AGAIN 2026-07-26, twice. (i) The core no longer asserts
`IsDomain` of its coefficient ring; step (a') of the proof below
recovers it by quotienting by `ker ιB`, which is prime because `ℚ̄_3`
is a domain, and carries the representation across by the coefficient
base change `exists_domain_coefficientRing_of_ringHom`. (ii) The
hypotheses `hbad2`, `hbad3`, `hbadℓ` (the places of `F` over `2`, `3`
and `ℓ` lie in `badF`) are threaded straight through to the core. They
are a faithfulness repair — the `3`-adic member can ramify at exactly
those places, so the matching clause had no business reaching there — and
it costs nothing, because `badF` is chosen existentially upstream and
the clause only weakens as it grows. See the core's docstring for the
argument and `exists_potentialModularityWitness_of_five_le` for the
discharge.

NARROWED A FOURTH TIME 2026-07-26 (round 4): the CUSPIDALITY hypothesis
`hirrF : (ρbar.map (algebraMap ℚ F)).IsIrreducible` is likewise threaded
straight through to the core. Carayol's Théorème (A) is a theorem about
cuspidal `π`, and `hmod` alone does not exclude an Eisenstein
eigensystem; `hirrF` is the non-Eisenstein condition. It too costs
nothing: `exists_potentialModularityWitness_of_five_le` already holds it
(from `exists_moretBailly_seed_of_five_le`) and already passes it to
`exists_heckePackage_of_seed`.

See `carayol_threeadic_realization_of_heckePackage` for the full
literature, pin, route and soundness audits (including the
component-by-component TERMINALITY AUDIT of what is left, and what was
deliberately NOT pulled out of the citation, and why).

CIRCULARITY GUARD (inherited from pillar β, load-bearing): no
discharge through `Family.lean`, `Lift.lean`, or
`Modularity/Interface.lean`; discharged here through the Carayol
geometric core alone, which inherits the same guard. -/
theorem exists_threeadic_realization_domain_of_heckePackage
    {ℓ : ℕ} (hℓodd : Odd ℓ) [Fact ℓ.Prime] (hℓ5 : 5 ≤ ℓ)
    {O : Type u} [CommRing O] [IsDomain O] [TopologicalSpace O]
    [IsTopologicalRing O] [Algebra ℤ_[ℓ] O] [IsLocalRing O]
    [Module.Finite ℤ_[ℓ] O] [IsModuleTopology ℤ_[ℓ] O]
    (hZinj : Function.Injective (algebraMap ℤ_[ℓ] O))
    {ρ : GaloisRep ℚ O (Fin 2 → O)}
    (hrank : Module.rank O (Fin 2 → O) = 2)
    (hρ : IsHardlyRamified hℓodd hrank ρ)
    {k : Type u} [Field k] [Finite k] [Algebra ℤ_[ℓ] k]
    [TopologicalSpace k] [DiscreteTopology k]
    {W : Type v} [AddCommGroup W] [Module k W] [Module.Finite k W]
    [Module.Free k W]
    (hW : Module.rank k W = 2) {ρbar : GaloisRep ℚ k W}
    (hρbar : IsHardlyRamified hℓodd hW ρbar)
    (hirr : ρbar.IsIrreducible)
    (π : O →+* k) (hπsurj : Function.Surjective π)
    (hπ : ∀ (q : ℕ) (hq : q.Prime), q ≠ 2 → q ≠ ℓ →
      (ρ.charFrob hq.toHeightOneSpectrumRingOfIntegersRat).map π =
        ρbar.charFrob hq.toHeightOneSpectrumRingOfIntegersRat)
    (F : Type u) [Field F] [NumberField F]
    (hFtr : NumberField.IsTotallyReal F) (hFgal : IsGalois ℚ F)
    -- PARITY (2026-07-27): carried through untouched to the Carayol core, which
    -- is the only node that consumes it. See
    -- `carayol_threeadic_realization_of_heckePackage`.
    (hFeven : Even (Module.finrank ℚ F))
    (hirrF : (ρbar.map (algebraMap ℚ F)).IsIrreducible)
    (E : Type u) [Field E] [NumberField E]
    (badF : Finset (HeightOneSpectrum (NumberField.RingOfIntegers F)))
    (heckeF : HeightOneSpectrum (NumberField.RingOfIntegers F) →
      Polynomial E)
    (ψℓ : E →+* AlgebraicClosure ℚ_[ℓ])
    (ιO : O →+* AlgebraicClosure ℚ_[ℓ]) (hιO : Function.Injective ιO)
    (hmod : ∀ w ∉ badF,
      ((ρ.map (algebraMap ℚ F)).charFrob w).map ιO =
        (heckeF w).map ψℓ)
    (hbad2 : ∀ w : HeightOneSpectrum (NumberField.RingOfIntegers F),
      (2 : NumberField.RingOfIntegers F) ∈ w.asIdeal → w ∈ badF)
    (hbad3 : ∀ w : HeightOneSpectrum (NumberField.RingOfIntegers F),
      (3 : NumberField.RingOfIntegers F) ∈ w.asIdeal → w ∈ badF)
    (hbadℓ : ∀ w : HeightOneSpectrum (NumberField.RingOfIntegers F),
      (ℓ : NumberField.RingOfIntegers F) ∈ w.asIdeal → w ∈ badF) :
    ∃ (B : Type u) (_ : CommRing B) (_ : IsDomain B)
      (_ : TopologicalSpace B)
      (_ : IsTopologicalRing B) (_ : Algebra ℤ_[3] B) (_ : IsLocalRing B)
      (_ : Module.Finite ℤ_[3] B) (_ : IsModuleTopology ℤ_[3] B)
      (_ : Function.Injective (algebraMap ℤ_[3] B))
      (τF : GaloisRep F B (Fin 2 → B))
      (ψ₃ : E →+* AlgebraicClosure ℚ_[3])
      (ιB : B →+* AlgebraicClosure ℚ_[3]) (_ : Function.Injective ιB),
      ∀ w ∉ badF, (τF.charFrob w).map ιB = (heckeF w).map ψ₃ := by
  classical
  -- (a) the NARROWED Carayol/Taylor citation: the coefficient ring comes
  -- back as a BARE commutative ring, module-finite over `ℤ_3`, with no
  -- topology, no domain hypothesis, no `ℤ_3`-injectivity and no
  -- injectivity of the comparison embedding asserted
  obtain ⟨B₀, hCR₀, hAlg₀, hFin₀, τ₀, ψ₃, ι₀, hmatch₀⟩ :=
    carayol_threeadic_realization_of_heckePackage hℓodd hℓ5 hZinj hrank hρ hW
      hρbar hirr π hπsurj hπ F hFtr hFgal hFeven hirrF E badF heckeF ψℓ ιO hιO
      hmod hbad2 hbad3 hbadℓ
  -- (a') DOMAIN NORMALIZATION: `ker ι₀` is prime, so the whole package
  -- descends to `B₀ ⧸ ker ι₀` without moving any `ι₀`-image of a Frobenius
  -- characteristic polynomial. This is why the citation no longer has to
  -- assert `IsDomain`.
  letI : TopologicalSpace B₀ := moduleTopology ℤ_[3] B₀
  haveI : IsModuleTopology ℤ_[3] B₀ := ⟨rfl⟩
  haveI : IsTopologicalRing B₀ := isTopologicalRing_moduleTopology_of_finite 3 B₀
  obtain ⟨B, hCR, hDom, hAlg, hFin, τF, ιB, hdesc⟩ :=
    exists_domain_coefficientRing_of_ringHom (p := 3) (K := F) ι₀ τ₀
  -- locality of the coefficient ring is now a THEOREM of the Henselian
  -- property of `ℤ_3`, not a component of the citation
  have hLR : IsLocalRing B :=
    isLocalRing_of_finite_padicInt_domain (p := 3)
      (injective_algebraMap_of_ringHom_charZero ιB)
  -- (b) the coefficient-ring bookkeeping, all four components PROVEN
  -- above: the canonical module topology is a ring topology and is of
  -- course the module topology, and both injectivity statements follow
  -- from the mere existence of the characteristic-zero comparison
  -- embedding `ιB`
  -- the topology must be FIXED by `letI` before the components whose types
  -- mention it are elaborated
  letI : TopologicalSpace B := moduleTopology ℤ_[3] B
  exact ⟨B, hCR, hDom, moduleTopology ℤ_[3] B,
    isTopologicalRing_moduleTopology_of_finite 3 B, hAlg, hLR, hFin, ⟨rfl⟩,
    injective_algebraMap_of_ringHom_charZero ιB, τF, ψ₃, ιB,
    injective_of_finite_padicInt_charZero (p := 3) ιB,
    fun w hw => (hdesc w).trans (hmatch₀ w hw)⟩

/-- **The Hilbert-modular `3`-adic realization** (PROVEN assembly,
2026-07-24 — Carayol 1986 / Taylor 1989 at one remove): a
Hilbert-modular Hecke eigensystem `(E, heckeF)` over the totally real
field `F` — witnessed as modular by the `ℓ`-adic matching clause
`hmod` for the lift `ρ` — has a `3`-adic Galois realization: a
representation `τF` of `G_F` on a stable lattice over a local ring `B`
finite FREE over `ℤ_3` (classically the integers of the completion
`E_λ`, `λ | 3`), with the same Hecke polynomials through a place `ψ₃`
of `E` over `3`.

ASSEMBLY (2026-07-24, PROVEN — the literature-joint cut of this node).
The node splits at its one genuine literature joint into

* (a) the CITATION half, `exists_threeadic_realization_domain_of_heckePackage`
  — the automorphic construction of the `3`-adic representation with the
  right Frobenius characteristic polynomials, over the coefficient
  ring the construction literally produces: a local DOMAIN,
  module-finite over `ℤ_3`, containing `ℤ_3`. Since 2026-07-25 that
  half is itself PROVEN, over the strictly narrower geometric core
  `carayol_threeadic_realization_of_heckePackage` (which no longer
  asserts the topology on the coefficient ring, nor its LOCALITY, nor
  that it is a DOMAIN, nor either injectivity component, and since
  2026-07-26 no longer claims the Hecke matching at the places over
  `3`, where its own `3`-adic representation ramifies) — the sole
  residual sorry of the node is now that core;
* (b) the FORMAL half, `free_of_finite_of_algebraMap_padicInt_injective`
  — the free-lattice normalization, PROVEN in-tree: `ℤ_3` is a DVR
  hence a PID, injectivity of `algebraMap ℤ_3 B` between domains is
  torsion-freeness, and a finitely generated torsion-free module over
  a PID is free;
* (c) the eigensystem-match TRANSPORT, discharged by this assembly.
  It is an identity transport, and deliberately so: the free-lattice
  normalization of (b) does not move the coefficient ring, it only
  supplies the missing `Module.Free ℤ_3 B` instance on the ring (a)
  already produced. The Hecke-polynomial matching clause, the
  embedding `ιB` and the place `ψ₃` therefore carry over verbatim —
  there is no lattice change, hence no charpoly to re-compute. (The
  alternative cut, in which (a) returns the representation over the
  local FIELD `E_λ` and (b) chooses a Galois-stable lattice inside
  it, was rejected: the stable-lattice step is then itself a citation
  — compactness of `G_F` plus a Bruhat–Tits/`Serre I §1` argument that
  the pin cannot reach — so that cut would trade one citation for
  two, and (c) would become a genuine but unprovable transport.)

Literature (see the citation leaf's docstring for the full audit):
Carayol, *Sur les représentations ℓ-adiques associées aux formes
modulaires de Hilbert*, Ann. Sci. ÉNS 19 (1986); Taylor, *On Galois
representations associated to Hilbert modular forms*, Invent. Math. 98
(1989); Serre, *Abelian ℓ-adic representations*, I §1 for the stable
lattice.

HYPOTHESES ADDED 2026-07-26 AND THREADED THROUGH UNCHANGED: `hbad2`,
`hbad3`, `hbadℓ` (rounds 2–3, the RAMIFICATION gap — the citation may
not claim a Frobenius characteristic polynomial where the `3`-adic
member ramifies) and `hirrF` (round 4, the CUSPIDALITY gap — Carayol's
Théorème (A) is a theorem about cuspidal `π`, and `hmod` alone does not
exclude an Eisenstein eigensystem). All four are free at the single
call site `exists_potentialModularityWitness_of_five_le`; see the core's
docstring for the arguments.

SOUNDNESS AUDIT (both ways, 2026-07-24): unchanged from the citation
leaf, since this theorem is a strict consequence of it — (i) direct,
for the intended instantiation this is Carayol/Taylor verbatim plus
the freeness of the integers of a `3`-adic field; (ii) collapse, the
hypothesis set (an irreducible hardly ramified mod-`ℓ` representation,
`ℓ ≥ 5`) is classically unsatisfiable (headline below), so the
statement is classically true for every package.

CIRCULARITY GUARD (inherited from pillar β, load-bearing): no
discharge through `Family.lean`, `Lift.lean`, or
`Modularity/Interface.lean`. Discharged here through the
Carayol/Taylor citation leaf alone, which inherits the same guard. -/
theorem exists_threeadic_realization_of_heckePackage
    {ℓ : ℕ} (hℓodd : Odd ℓ) [Fact ℓ.Prime] (hℓ5 : 5 ≤ ℓ)
    {O : Type u} [CommRing O] [IsDomain O] [TopologicalSpace O]
    [IsTopologicalRing O] [Algebra ℤ_[ℓ] O] [IsLocalRing O]
    [Module.Finite ℤ_[ℓ] O] [IsModuleTopology ℤ_[ℓ] O]
    (hZinj : Function.Injective (algebraMap ℤ_[ℓ] O))
    {ρ : GaloisRep ℚ O (Fin 2 → O)}
    (hrank : Module.rank O (Fin 2 → O) = 2)
    (hρ : IsHardlyRamified hℓodd hrank ρ)
    {k : Type u} [Field k] [Finite k] [Algebra ℤ_[ℓ] k]
    [TopologicalSpace k] [DiscreteTopology k]
    {W : Type v} [AddCommGroup W] [Module k W] [Module.Finite k W]
    [Module.Free k W]
    (hW : Module.rank k W = 2) {ρbar : GaloisRep ℚ k W}
    (hρbar : IsHardlyRamified hℓodd hW ρbar)
    (hirr : ρbar.IsIrreducible)
    (π : O →+* k) (hπsurj : Function.Surjective π)
    (hπ : ∀ (q : ℕ) (hq : q.Prime), q ≠ 2 → q ≠ ℓ →
      (ρ.charFrob hq.toHeightOneSpectrumRingOfIntegersRat).map π =
        ρbar.charFrob hq.toHeightOneSpectrumRingOfIntegersRat)
    (F : Type u) [Field F] [NumberField F]
    (hFtr : NumberField.IsTotallyReal F) (hFgal : IsGalois ℚ F)
    -- PARITY (2026-07-27): carried through untouched to the Carayol core, which
    -- is the only node that consumes it. See
    -- `carayol_threeadic_realization_of_heckePackage`.
    (hFeven : Even (Module.finrank ℚ F))
    (hirrF : (ρbar.map (algebraMap ℚ F)).IsIrreducible)
    (E : Type u) [Field E] [NumberField E]
    (badF : Finset (HeightOneSpectrum (NumberField.RingOfIntegers F)))
    (heckeF : HeightOneSpectrum (NumberField.RingOfIntegers F) →
      Polynomial E)
    (ψℓ : E →+* AlgebraicClosure ℚ_[ℓ])
    (ιO : O →+* AlgebraicClosure ℚ_[ℓ]) (hιO : Function.Injective ιO)
    (hmod : ∀ w ∉ badF,
      ((ρ.map (algebraMap ℚ F)).charFrob w).map ιO =
        (heckeF w).map ψℓ)
    (hbad2 : ∀ w : HeightOneSpectrum (NumberField.RingOfIntegers F),
      (2 : NumberField.RingOfIntegers F) ∈ w.asIdeal → w ∈ badF)
    (hbad3 : ∀ w : HeightOneSpectrum (NumberField.RingOfIntegers F),
      (3 : NumberField.RingOfIntegers F) ∈ w.asIdeal → w ∈ badF)
    (hbadℓ : ∀ w : HeightOneSpectrum (NumberField.RingOfIntegers F),
      (ℓ : NumberField.RingOfIntegers F) ∈ w.asIdeal → w ∈ badF) :
    ∃ (B : Type u) (_ : CommRing B) (_ : TopologicalSpace B)
      (_ : IsTopologicalRing B) (_ : Algebra ℤ_[3] B) (_ : IsLocalRing B)
      (_ : Module.Finite ℤ_[3] B) (_ : Module.Free ℤ_[3] B)
      (_ : IsModuleTopology ℤ_[3] B)
      (τF : GaloisRep F B (Fin 2 → B))
      (ψ₃ : E →+* AlgebraicClosure ℚ_[3])
      (ιB : B →+* AlgebraicClosure ℚ_[3]) (_ : Function.Injective ιB),
      ∀ w ∉ badF, (τF.charFrob w).map ιB = (heckeF w).map ψ₃ := by
  classical
  -- (a) the Carayol/Taylor citation half: the `3`-adic realization over
  -- the coefficient DOMAIN the construction literally produces
  obtain ⟨B, hCR, hDom, hTS, hTR, hAlg, hLR, hFin, hMT, hBinj, τF, ψ₃,
    ιB, hιB, hmatch⟩ :=
    exists_threeadic_realization_domain_of_heckePackage hℓodd hℓ5 hZinj
      hrank hρ hW hρbar hirr π hπsurj hπ F hFtr hFgal hFeven hirrF E badF
      heckeF ψℓ ιO hιO hmod hbad2 hbad3 hbadℓ
  -- (c) the eigensystem-match transport: the normalization below does
  -- not move the coefficient ring, so `hmatch` is carried verbatim and
  -- only the `Module.Free` component remains to be supplied
  refine ⟨B, hCR, hTS, hTR, hAlg, hLR, hFin, ?_, hMT, τF, ψ₃, ιB, hιB,
    hmatch⟩
  -- (b) the free-lattice normalization over `ℤ_3`
  exact @free_of_finite_of_algebraMap_padicInt_injective 3 _ B hCR hDom
    hAlg hFin hBinj

/-- **Descent-closed enlargement of the Hecke block** (SORRIED citation;
the discharge of `PotentialModularityWitness.descentClosed`, added
2026-07-27 when that field was introduced).

STATEMENT.  Given the `ℓ`-adic Hecke block over `F` produced by
`exists_heckePackage_of_seed` — a number field `E`, Hecke polynomials
`heckeF`, a place `ψℓ : E ↪ ℚ̄_ℓ`, the coefficient embedding
`ιO : O ↪ ℚ̄_ℓ` and the modularity clause `hmod` — the coefficient field
may be ENLARGED to a number field `E₂` which still carries the
eigensystem over `F` (`hmod₂`, with the SAME bad set and the same `ιO`)
and which is in addition DESCENT-CLOSED: for every subgroup
`H ≤ Gal(F/ℚ)` and every realization of the eigensystem of `ρ|_{G_{F^H}}`
over a number field `E'` receiving `E₂` compatibly with the embeddings
into `ℚ̄_ℓ`, the eigenvalue function already takes values in `ι '' E₂`
away from a further finite set.

CLASSICAL CONTENT (BLGGT §5.3; Langlands, *Base Change for GL(2)*,
Thm 4.2; Shimura's rationality theorem).  The Brauer decomposition of the
trivial character of `Gal(F/ℚ)` involves FINITELY many solvable subgroups
`Hᵢ`, and the tower of cyclic steps below each `Hᵢ` is finite; solvable
base change descends the Hilbert newform `f` over `F` to a form over each
intermediate field, and by Shimura's rationality theorem each descended
form has a NUMBER FIELD as its Hecke field.  Take `E₂` to be the
compositum, inside `ℚ̄_ℓ`, of `ψℓ(E)` with the images of all those Hecke
fields: a compositum of finitely many number fields is a number field.
By construction every descended eigenvalue lies in `E₂`, which is the
descent-closure clause; and `heckeF` is transported along `E ↪ E₂` with
`hmod₂` following from `hmod` by functoriality of `Polynomial.map`, since
no clause pins `E` as GENERATED by `heckeF`.  This is precisely the
"enlarging `E` costs nothing" argument of the
`PotentialModularityWitness` docstring, and this leaf is where it is
CARRIED OUT rather than merely understood.

SOUNDNESS AUDIT.  (i) Direct: the compositum construction above, which is
a genuine classical theorem and not a vacuity.  (ii) Collapse: the
arithmetic hypothesis package is carried in full — `hℓ5`, `hρ`, `hρbar`,
`hirr` — and is classically unsatisfiable (the module headline), so the
statement is classically true for every package as well.  Note that BOTH
routes are available here, which is exactly what was NOT true of the leaf
this replaces (`heckeField_descentClosed_of_witness` quantified over an
arbitrary carrier with no arithmetic package at all, so only route (i)
applied to it and route (i) is a statement about the carrier that is
CHOSEN — the reason the obligation had to move onto the structure).

WHY THE ENLARGEMENT SHAPE RATHER THAN A BARE ASSERTION ABOUT `E`.  For
the `E` that `exists_heckePackage_of_seed` happens to return, descent
closure is NOT classically true — the Hecke field genuinely grows down
the tower.  Only the enlarged `E₂` satisfies it, so the statement must
quantify existentially over the new field.  Asserting descent-closure of
the given `E` would be a false leaf.

CIRCULARITY GUARD (inherited from pillar β, load-bearing): no discharge
through `Family.lean`, `Lift.lean`, or `Modularity/Interface.lean`. -/
theorem exists_descentClosed_heckePackage
    {ℓ : ℕ} (hℓodd : Odd ℓ) [Fact ℓ.Prime] (hℓ5 : 5 ≤ ℓ)
    {O : Type u} [CommRing O] [IsDomain O] [TopologicalSpace O]
    [IsTopologicalRing O] [Algebra ℤ_[ℓ] O] [IsLocalRing O]
    [Module.Finite ℤ_[ℓ] O] [IsModuleTopology ℤ_[ℓ] O]
    (hZinj : Function.Injective (algebraMap ℤ_[ℓ] O))
    {ρ : GaloisRep ℚ O (Fin 2 → O)}
    (hrank : Module.rank O (Fin 2 → O) = 2)
    (hρ : IsHardlyRamified hℓodd hrank ρ)
    {k : Type u} [Field k] [Finite k] [Algebra ℤ_[ℓ] k]
    [TopologicalSpace k] [DiscreteTopology k]
    {W : Type v} [AddCommGroup W] [Module k W] [Module.Finite k W]
    [Module.Free k W]
    (hW : Module.rank k W = 2) {ρbar : GaloisRep ℚ k W}
    (hρbar : IsHardlyRamified hℓodd hW ρbar)
    (hirr : ρbar.IsIrreducible)
    (π : O →+* k) (hπsurj : Function.Surjective π)
    (hπ : ∀ (q : ℕ) (hq : q.Prime), q ≠ 2 → q ≠ ℓ →
      (ρ.charFrob hq.toHeightOneSpectrumRingOfIntegersRat).map π =
        ρbar.charFrob hq.toHeightOneSpectrumRingOfIntegersRat)
    (F : Type u) [Field F] [NumberField F]
    (hFtr : NumberField.IsTotallyReal F) (hFgal : IsGalois ℚ F)
    (E : Type u) [Field E] [NumberField E]
    (badF : Finset (HeightOneSpectrum (NumberField.RingOfIntegers F)))
    (heckeF : HeightOneSpectrum (NumberField.RingOfIntegers F) →
      Polynomial E)
    (ψℓ : E →+* AlgebraicClosure ℚ_[ℓ])
    (ιO : O →+* AlgebraicClosure ℚ_[ℓ]) (hιO : Function.Injective ιO)
    (hmod : ∀ w ∉ badF,
      ((ρ.map (algebraMap ℚ F)).charFrob w).map ιO = (heckeF w).map ψℓ) :
    ∃ (E₂ : Type u) (_ : Field E₂) (_ : NumberField E₂)
      (heckeF₂ : HeightOneSpectrum (NumberField.RingOfIntegers F) →
        Polynomial E₂)
      (ψ₂ : E₂ →+* AlgebraicClosure ℚ_[ℓ]),
      (∀ w ∉ badF,
        ((ρ.map (algebraMap ℚ F)).charFrob w).map ιO = (heckeF₂ w).map ψ₂) ∧
      (∀ (H : Subgroup (F ≃ₐ[ℚ] F)) (E' : Type u) [Field E']
        [NumberField E'] (ψ : E' →+* AlgebraicClosure ℚ_[ℓ])
        (ι : E₂ →+* E'),
        (∀ x : E₂, ψ (ι x) = ψ₂ x) →
        ∀ (S : Finset (HeightOneSpectrum (NumberField.RingOfIntegers
            (IntermediateField.fixedField H))))
          (a : HeightOneSpectrum (NumberField.RingOfIntegers
            (IntermediateField.fixedField H)) → E'),
        (∀ w ∉ S,
          ((ρ.map (algebraMap ℚ
              (IntermediateField.fixedField H))).charFrob w).map ιO =
            (Polynomial.X ^ 2 - Polynomial.C (a w) * Polynomial.X +
              Polynomial.C ((Ideal.absNorm w.asIdeal : ℕ) : E')).map ψ) →
        ∃ (S' : Finset (HeightOneSpectrum (NumberField.RingOfIntegers
            (IntermediateField.fixedField H))))
          (b : HeightOneSpectrum (NumberField.RingOfIntegers
            (IntermediateField.fixedField H)) → E₂),
          ∀ w, w ∉ S → w ∉ S' → ι (b w) = a w) :=
  sorry

/-- **Carrier inhabitation — potential modularity of the KW lift**
(PROVEN — Taylor's theorem, the analytic core of pillar β): the
Khare–Wintenberger lift `ρ` of an irreducible hardly ramified mod-`ℓ`
representation, `ℓ ≥ 5`, admits a potential-modularity carrier: a
totally real Galois number field `F` over which `ρ` is modular,
attached to a Hilbert newform of parallel weight `2` whose Hecke
eigensystem the carrier records, together with the newform's `3`-adic
realization over `F`.

Literature: Taylor, *Remarks on a conjecture of Fontaine and Mazur*,
J. Inst. Math. Jussieu 1 (2002), Theorem B (potential modularity:
Moret–Bailly produces `F` totally real — and Galois over `ℚ`,
avoiding the finitely many local obstructions — together with an
auxiliary Hilbert–Blumenthal abelian variety realizing
`ρbar|_{G_F}` whose companion mod-`p` representation is dihedral,
hence modular by converse theorems and Jacquet–Langlands); the
modularity lifting theorem over totally real fields (Kisin, *Moduli
of finite flat group schemes, and modularity*, Ann. of Math. 170
(2009); Taylor's 2018 Stanford course) then promotes the modularity
of `ρbar|_{G_F}` to `ρ|_{G_F}` (`ρ` is flat at `ℓ` with cyclotomic
determinant, and `ρbar|_{G_F(ζ_ℓ)}` is kept absolutely irreducible by
the Moret–Bailly avoidance); Carayol's local-global compatibility
identifies the Frobenius characteristic polynomials away from the bad
set; Carayol (1986) / Taylor (1989) attach the `3`-adic realization
on a stable lattice. FLT blueprint ch. 4: the potential-modularity
stage verbatim.

SOUNDNESS AUDIT (both ways, 2026-07-24): (i) direct — for the
intended instantiation (`ρ` the KW minimal lift of pillar α) this is
the literature chain above; for an abstract package the
abstract-quantification caveat of pillar β applies, and (ii) collapse
— the hypothesis set (an irreducible hardly ramified mod-`ℓ`
representation, `ℓ ≥ 5`) is classically unsatisfiable (headline
below), so the statement is classically true for every package.

CIRCULARITY GUARD (inherited from pillar β, load-bearing): must be
proven by the independent potential-modularity construction — never
through `Family.lean`, `Lift.lean`, or `Modularity/Interface.lean`.

ASSEMBLY (2026-07-24, PROVEN): Moret–Bailly base production
(`exists_moretBailly_seed_of_five_le` — Taylor 2002 Theorem B: the
totally real Galois `F`, irreducibility preservation, and the modular
congruent seed `MoretBaillySeed`) + modularity lifting over `F`
(`exists_heckePackage_of_seed` — Kisin/Taylor MLT + Carayol
local-global, producing the ℓ-adic Hecke block `E`/`badF`/`heckeF`/
`ψℓ`/`ιO`/`modularF`) + the Hilbert-modular `3`-adic realization
(`exists_threeadic_realization_of_heckePackage` — Carayol 1986 /
Taylor 1989, producing the `3`-adic block `B`/`τF`/`ψ₃`/`ιB`/
`matchF₃`), glued by instantiating the carrier fieldwise. Since
2026-07-27 there is a FOURTH: `exists_descentClosed_heckePackage`
(step (ii''), which enlarges the Hecke block's coefficient field to a
descent-closed one and thereby discharges the carrier's new
`descentClosed` field). Those four leaves are the residual sorries of
the inhabitation node; the circularity guard above binds each of them.

BAD-SET ENLARGEMENT (2026-07-26, step (ii') of the proof; extended the
same day from `{3}` to `{2, 3, ℓ}`): the carrier is built with
`badF ∪ {w : w ∋ 2} ∪ {w : w ∋ 3} ∪ {w : w ∋ ℓ}` rather than with the
`badF` that `exists_heckePackage_of_seed` returns. This is free —
`modularF` only weakens as its exceptional set grows — and it is what
discharges the narrowed Carayol citation's `hbad2`, `hbad3` and
`hbadℓ`, i.e. what stops that citation claiming Hecke matching at the
places where the `3`-adic member of the compatible system can ramify:
over `3` as its own residue characteristic, and over `2` and `ℓ`
because the Hilbert newform's level is supported exactly where `ρ`
ramifies. The `PotentialModularityWitness` docstring already specified
`badF` to contain the places over `2`, `3` and `ℓ`; this makes it
formally so, for all three.

DESCENT-CLOSURE OF `E` — AN OBLIGATION ON THIS NODE'S HECKE BLOCK
(2026-07-26; the corresponding obligation was reported upward by the
owner of `exists_baseChangeDescentData_of_prime_cyclic_step_of_inert` and is now
recorded on the carrier). The coefficient field `E` this node hands to
the carrier must be closed under the SOLVABLE DESCENT, not merely the
Hecke field of the newform over `F`: the descent leaves conclude that
the eigenvalues of the descended forms lie in `E` too, and classically
the Hecke field grows on the way down. See the DESCENT-CLOSURE note in
the `PotentialModularityWitness` docstring for why this costs nothing
formally — no field of the structure asserts that `heckeF` generates
`E`, and `E` may be replaced by any finite extension — and for the
canonical choice (the compositum of the Hecke fields of the forms in
the Brauer decomposition, a number field). Whoever discharges
`exists_heckePackage_of_seed` should make that enlargement there, or
enlarge here in the same style as the bad-set enlargement above.

**DONE 2026-07-27, the second way (step (ii'') of the proof), and it is
now a FORMAL obligation rather than an understanding.** The prose above
said "this costs nothing formally" — true of the OTHER fields of the
carrier, and false of the descent leaves that consume `E`, which is why
`PotentialModularityWitness` gained the field `descentClosed` and why
this node must now supply it. It does so through the new sorried
citation `exists_descentClosed_heckePackage`: the block returned by
step (ii) is replaced by an enlarged block `(E₂, heckeF₂, ψ₂)` over the
same `badF'` and the same `ιO`, carrying the descent-closure clause. The
enlargement is free for exactly the reason recorded above, and the
`3`-adic block of step (iii) is built over `E₂` rather than `E`. -/
theorem exists_potentialModularityWitness_of_five_le
    {ℓ : ℕ} (hℓodd : Odd ℓ) [Fact ℓ.Prime] (hℓ5 : 5 ≤ ℓ)
    {O : Type u} [CommRing O] [IsDomain O] [TopologicalSpace O]
    [IsTopologicalRing O] [Algebra ℤ_[ℓ] O] [IsLocalRing O]
    [Module.Finite ℤ_[ℓ] O] [IsModuleTopology ℤ_[ℓ] O]
    (hZinj : Function.Injective (algebraMap ℤ_[ℓ] O))
    {ρ : GaloisRep ℚ O (Fin 2 → O)}
    (hrank : Module.rank O (Fin 2 → O) = 2)
    (hρ : IsHardlyRamified hℓodd hrank ρ)
    {k : Type u} [Field k] [Finite k] [Algebra ℤ_[ℓ] k]
    [TopologicalSpace k] [DiscreteTopology k]
    {W : Type v} [AddCommGroup W] [Module k W] [Module.Finite k W]
    [Module.Free k W]
    (hW : Module.rank k W = 2) {ρbar : GaloisRep ℚ k W}
    (hρbar : IsHardlyRamified hℓodd hW ρbar)
    (hirr : ρbar.IsIrreducible)
    (π : O →+* k) (hπsurj : Function.Surjective π)
    (hπ : ∀ (q : ℕ) (hq : q.Prime), q ≠ 2 → q ≠ ℓ →
      (ρ.charFrob hq.toHeightOneSpectrumRingOfIntegersRat).map π =
        ρbar.charFrob hq.toHeightOneSpectrumRingOfIntegersRat) :
    Nonempty (PotentialModularityWitness ℓ O ρ) := by
  classical
  -- (i) the Moret–Bailly base: totally real Galois `F`, irreducibility
  -- preservation, and the modular congruent seed (Taylor 2002 Thm B)
  obtain ⟨F, hF, hNF, hFtr, hFgal, hev, hirrF, ⟨seed⟩⟩ :=
    exists_moretBailly_seed_of_five_le hℓodd hℓ5 hZinj hrank hρ hW hρbar
      hirr π hπsurj hπ
  -- (ii) modularity lifting over `F`: the ℓ-adic Hecke block
  obtain ⟨E, hE, hNE, badF, heckeF, ψℓ, ιO, hιO, hmod⟩ :=
    exists_heckePackage_of_seed hℓodd hℓ5 hZinj hrank hρ hW hρbar hirr
      π hπsurj hπ F hFtr hFgal hirrF seed
  -- (ii') ENLARGE the exceptional set by the places of `F` over `2`, `3`
  -- and `ℓ` (2026-07-26; the `3` step was step (ii') of the round-2 cut,
  -- the `2` and `ℓ` steps complete it). The `ℓ`-adic clause `hmod` only
  -- WEAKENS when its exceptional set grows, so all three enlargements are
  -- free; together they discharge the narrowed Carayol citation's `hbad2`,
  -- `hbad3` and `hbadℓ`, which exist because those are exactly the places
  -- at which the `3`-adic member of the compatible system can RAMIFY — over
  -- `3` because it is the residue characteristic of that member, over `2`
  -- and `ℓ` because the level of the Hilbert newform is supported there,
  -- `ρ` being ramified precisely at `2` and `ℓ`. At a ramified place
  -- `charFrob` is not even independent of the choice of arithmetic
  -- Frobenius, so the citation has no right to a matching clause there.
  -- The `PotentialModularityWitness` docstring already specified `badF` to
  -- contain the places over `2`, `3` and `ℓ`; the witness is now built with
  -- a `badF` that formally does.
  have h2ne : (2 : NumberField.RingOfIntegers F) ≠ 0 := by norm_num
  have h3ne : (3 : NumberField.RingOfIntegers F) ≠ 0 := by norm_num
  have hℓne : (ℓ : NumberField.RingOfIntegers F) ≠ 0 := by
    have hℓ0 : ℓ ≠ 0 := by omega
    exact_mod_cast hℓ0
  obtain ⟨badF₂, hsub₂, hbad2₀⟩ :=
    exists_finset_superset_of_places_mem badF (2 : NumberField.RingOfIntegers F) h2ne
  obtain ⟨badF₃, hsub₃, hbad3₀⟩ :=
    exists_finset_superset_of_places_mem badF₂ (3 : NumberField.RingOfIntegers F) h3ne
  obtain ⟨badF', hsubℓ, hbadℓ⟩ :=
    exists_finset_superset_of_places_mem badF₃ (ℓ : NumberField.RingOfIntegers F) hℓne
  have hbad2 : ∀ w : HeightOneSpectrum (NumberField.RingOfIntegers F),
      (2 : NumberField.RingOfIntegers F) ∈ w.asIdeal → w ∈ badF' :=
    fun w hw => hsubℓ (hsub₃ (hbad2₀ w hw))
  have hbad3 : ∀ w : HeightOneSpectrum (NumberField.RingOfIntegers F),
      (3 : NumberField.RingOfIntegers F) ∈ w.asIdeal → w ∈ badF' :=
    fun w hw => hsubℓ (hbad3₀ w hw)
  have hsub : badF ⊆ badF' := (hsub₂.trans hsub₃).trans hsubℓ
  have hmod' : ∀ w ∉ badF',
      ((ρ.map (algebraMap ℚ F)).charFrob w).map ιO = (heckeF w).map ψℓ :=
    fun w hw => hmod w fun h => hw (hsub h)
  -- (ii'') ENLARGE the coefficient field to a DESCENT-CLOSED one
  -- (2026-07-27, when `PotentialModularityWitness.descentClosed` was
  -- added). The `E` that step (ii) returns is the Hecke field of the
  -- newform over `F` and is NOT closed under the solvable descent — the
  -- Hecke field grows down the Brauer tower. `E₂` is the compositum of
  -- `E` with the Hecke fields of all the descended forms, a finite
  -- compositum and hence still a number field; the enlargement is free
  -- exactly as the bad-set enlargement above is free, since no field of
  -- the carrier asserts that `heckeF` GENERATES `E`. This is what
  -- discharges the carrier's `descentClosed` field, and the enlarged
  -- block is what steps (iii) and the gluing below are handed.
  obtain ⟨E₂, hE₂, hNE₂, heckeF₂, ψ₂, hmod₂, hdc⟩ :=
    exists_descentClosed_heckePackage hℓodd hℓ5 hZinj hrank hρ hW hρbar
      hirr π hπsurj hπ F hFtr hFgal E badF' heckeF ψℓ ιO hιO hmod'
  -- (iii) the Hilbert-modular `3`-adic realization: the 3-adic block.
  -- `hirrF` — already in hand from step (i) and already consumed by step
  -- (ii) — is now also handed to the Carayol citation (round-4 narrowing,
  -- 2026-07-26): it is the non-Eisenstein/cuspidality condition without
  -- which Théorème (A) is not a theorem about the eigensystem at all.
  obtain ⟨B, hB₁, hB₂, hB₃, hB₄, hB₅, hB₆, hB₇, hB₈, τF, ψ₃, ιB, hιB,
    hmatch⟩ :=
    exists_threeadic_realization_of_heckePackage hℓodd hℓ5 hZinj hrank hρ
      hW hρbar hirr π hπsurj hπ F hFtr hFgal hev hirrF E₂ badF' heckeF₂ ψ₂ ιO hιO
      hmod₂ hbad2 hbad3 hbadℓ
  -- glue: instantiate the carrier fieldwise
  exact ⟨{ F := F, totallyReal := hFtr, galoisF := hFgal, E := E₂,
           badF := badF', heckeF := heckeF₂, ψℓ := ψ₂, ιO := ιO,
           ιO_injective := hιO, modularF := hmod₂, descentClosed := hdc,
           B := B, τF := τF,
           ψ₃ := ψ₃, ιB := ιB, ιB_injective := hιB, matchF₃ := hmatch }⟩

section ArtinInduction

open scoped Classical

/-- The `ℚ`-valued indicator function of the cyclic subgroup `⟨y⟩` —
i.e. the trivial character of `⟨y⟩` extended by zero to all of `G`,
the extension-by-zero shape in which the Brauer/Artin leaf carries its
one-dimensional characters. -/
noncomputable def cyclicIndicator {G : Type*} [Group G] (y : G) :
    G → ℚ :=
  fun h => if h ∈ Subgroup.zpowers y then 1 else 0

/-- The character of `G` induced from the trivial character of the
cyclic subgroup `⟨y⟩`, written by the Frobenius formula
`(Ind_{⟨y⟩}^G 1)(g) = |⟨y⟩|⁻¹ · Σ_{x ∈ G} 1_{⟨y⟩}(x⁻¹ g x)`. Its
values are the nonnegative integers `#{ x⟨y⟩ : x⁻¹ g x ∈ ⟨y⟩ }`, but
nothing below needs that. -/
noncomputable def indTrivCyclic {G : Type*} [Group G] [Fintype G]
    (y : G) : G → ℚ := fun g =>
  (Nat.card (Subgroup.zpowers y) : ℚ)⁻¹ *
    ∑ x : G, cyclicIndicator y (x⁻¹ * g * x)

/-- Frobenius reciprocity in elementary form: pairing the induced
trivial character of `⟨y⟩` against an arbitrary function `f : G → ℚ`
gives the sum over `⟨y⟩` of the conjugation average of `f` (up to the
normalizing factor `|⟨y⟩|⁻¹`). Proof: unfold the induced character,
exchange the two sums and reindex `g = x h x⁻¹` for each fixed `x`. -/
theorem sum_indTrivCyclic_mul {G : Type*} [Group G] [Fintype G]
    (y : G) (f : G → ℚ) :
    ∑ g : G, indTrivCyclic y g * f g =
      (Nat.card (Subgroup.zpowers y) : ℚ)⁻¹ *
        ∑ h ∈ Finset.univ.filter (fun h => h ∈ Subgroup.zpowers y),
          ∑ x : G, f (x * h * x⁻¹) := by
  have h1 : ∀ x : G, ∑ g : G, cyclicIndicator y (x⁻¹ * g * x) * f g
      = ∑ h : G, cyclicIndicator y h * f (x * h * x⁻¹) := by
    intro x
    refine (Fintype.sum_equiv
      ((Equiv.mulLeft x).trans (Equiv.mulRight x⁻¹)) _ _ ?_).symm
    intro h
    have hx : x⁻¹ * (x * h * x⁻¹) * x = h := by group
    simp only [Equiv.coe_trans, Function.comp_apply, Equiv.coe_mulLeft,
      Equiv.coe_mulRight]
    rw [hx]
  have step : ∑ g : G, (∑ x : G, cyclicIndicator y (x⁻¹ * g * x)) * f g
      = ∑ h ∈ Finset.univ.filter (fun h => h ∈ Subgroup.zpowers y),
          ∑ x : G, f (x * h * x⁻¹) := by
    simp only [Finset.sum_mul]
    rw [Finset.sum_comm, Finset.sum_congr rfl (fun x _ => h1 x),
      Finset.sum_comm, Finset.sum_filter]
    refine Finset.sum_congr rfl fun h _ => ?_
    by_cases hh : h ∈ Subgroup.zpowers y <;> simp [cyclicIndicator, hh]
  calc ∑ g : G, indTrivCyclic y g * f g
      = ∑ g : G, (Nat.card (Subgroup.zpowers y) : ℚ)⁻¹ *
          ((∑ x : G, cyclicIndicator y (x⁻¹ * g * x)) * f g) := by
        refine Finset.sum_congr rfl fun g _ => ?_
        show ((Nat.card (Subgroup.zpowers y) : ℚ)⁻¹ *
          ∑ x : G, cyclicIndicator y (x⁻¹ * g * x)) * f g = _
        rw [mul_assoc]
    _ = (Nat.card (Subgroup.zpowers y) : ℚ)⁻¹ *
          ∑ g : G, (∑ x : G, cyclicIndicator y (x⁻¹ * g * x)) * f g := by
        rw [Finset.mul_sum]
    _ = _ := by rw [step]

/-- Möbius inversion over the lattice of cyclic subgroups, in the only
form needed here: if every "cyclic partial sum" `Σ_{h ∈ ⟨y⟩} F h` of a
function `F : G → ℚ` vanishes, then `F` sums to zero over all of `G`.

Proof: partition `G` (and each `⟨y⟩`) into the fibres of `h ↦ ⟨h⟩`;
a strong induction on `|⟨y⟩|` shows each fibre sum
`Σ_{⟨h⟩ = ⟨y⟩} F h` vanishes (the fibres of the PROPER cyclic
subgroups of `⟨y⟩` are handled by the induction hypothesis, since a
proper subgroup has strictly smaller cardinality), and summing the
fibre sums over all cyclic subgroups gives `Σ_{g ∈ G} F g = 0`. -/
theorem sum_eq_zero_of_cyclic_sums {G : Type*} [Group G] [Fintype G]
    (F : G → ℚ)
    (hF : ∀ y : G,
      ∑ h ∈ Finset.univ.filter (fun h => h ∈ Subgroup.zpowers y),
        F h = 0) :
    ∑ g : G, F g = 0 := by
  have key : ∀ (n : ℕ) (y : G), Nat.card (Subgroup.zpowers y) = n →
      ∑ h ∈ Finset.univ.filter
        (fun h => Subgroup.zpowers h = Subgroup.zpowers y), F h = 0 := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro y hy
      have hfib : ∀ z : G, z ∈ Subgroup.zpowers y →
          (Finset.univ.filter (fun h => h ∈ Subgroup.zpowers y)).filter
              (fun h => Subgroup.zpowers h = Subgroup.zpowers z)
            = Finset.univ.filter
              (fun h => Subgroup.zpowers h = Subgroup.zpowers z) := by
        intro z hz
        ext h
        simp only [Finset.mem_filter, Finset.mem_univ, true_and,
          and_iff_right_iff_imp]
        intro hh
        have hmem : h ∈ Subgroup.zpowers h := Subgroup.mem_zpowers h
        rw [hh] at hmem
        exact (Subgroup.zpowers_le.2 hz) hmem
      have hmaps : ∀ h ∈ Finset.univ.filter
          (fun h => h ∈ Subgroup.zpowers y),
          Subgroup.zpowers h ∈ (Finset.univ.filter
            (fun h => h ∈ Subgroup.zpowers y)).image
            (fun h => Subgroup.zpowers h) :=
        fun h hh => Finset.mem_image_of_mem _ hh
      have hsplit := Finset.sum_fiberwise_of_maps_to hmaps F
      rw [hF y] at hsplit
      have hymem : y ∈ Finset.univ.filter
          (fun h => h ∈ Subgroup.zpowers y) := by
        simp [Subgroup.mem_zpowers]
      have hone := Finset.sum_eq_single_of_mem
        (s := (Finset.univ.filter (fun h => h ∈ Subgroup.zpowers y)).image
          (fun h : G => Subgroup.zpowers h))
        (f := fun D => ∑ h ∈ (Finset.univ.filter
          (fun h => h ∈ Subgroup.zpowers y)).filter
          (fun h => Subgroup.zpowers h = D), F h)
        (Subgroup.zpowers y) (Finset.mem_image_of_mem _ hymem) ?_
      · rw [hone, hfib y (Subgroup.mem_zpowers y)] at hsplit
        exact hsplit
      · intro D hD hDne
        obtain ⟨z, hz, rfl⟩ := Finset.mem_image.1 hD
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz
        rw [hfib z hz]
        refine ih (Nat.card (Subgroup.zpowers z)) ?_ z rfl
        rw [← hy]
        have hle : Subgroup.zpowers z ≤ Subgroup.zpowers y :=
          Subgroup.zpowers_le.2 hz
        have hss : (Subgroup.zpowers z : Set G) ⊂
            (Subgroup.zpowers y : Set G) := by
          refine ⟨hle, fun hsub => hDne (le_antisymm hle ?_)⟩
          intro a ha
          exact hsub ha
        have hlt := Set.ncard_lt_ncard hss (Set.toFinite _)
        rwa [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq,
          SetLike.coe_sort_coe, SetLike.coe_sort_coe] at hlt
  have hmaps2 : ∀ h ∈ (Finset.univ : Finset G),
      Subgroup.zpowers h ∈ Finset.univ.image
        (fun h : G => Subgroup.zpowers h) :=
    fun h _ => Finset.mem_image_of_mem _ (Finset.mem_univ h)
  rw [← Finset.sum_fiberwise_of_maps_to hmaps2 F]
  refine Finset.sum_eq_zero fun D hD => ?_
  obtain ⟨z, _, rfl⟩ := Finset.mem_image.1 hD
  exact key _ z rfl

set_option maxRecDepth 8000 in
/-- **Artin's induction theorem**, span form: on a finite group `G`
the constant function `1` is a `ℚ`-linear combination of the
characters induced from the trivial characters of the CYCLIC subgroups
of `G` (Serre, *Linear Representations of Finite Groups*, §9.2,
Theorem 17).

Proof (the standard duality argument, run over `ℚ` so that the
coefficients come out rational): if `1` were not in the span `W` of
the `Ind_{⟨y⟩}^G 1` inside the finite-dimensional `ℚ`-space of
functions `G → ℚ`, a linear functional `ϕ` would vanish on `W` but not
at `1`. Writing `ϕ u = Σ_g u g · fd g` with `fd g = ϕ (Pi.single g 1)`
and putting `F h = Σ_x fd (x h x⁻¹)`, the vanishing of `ϕ` on every
`Ind_{⟨y⟩}^G 1` says exactly (`sum_indTrivCyclic_mul`) that every
cyclic partial sum of `F` vanishes; hence `Σ_g F g = 0`
(`sum_eq_zero_of_cyclic_sums`), i.e. `|G| · Σ_g fd g = 0`, i.e.
`ϕ 1 = Σ_g fd g = 0` — a contradiction. -/
theorem exists_artin_coeffs (G : Type*) [Group G] [Fintype G] :
    ∃ c : G → ℚ, ∀ g : G, ∑ y : G, c y * indTrivCyclic y g = 1 := by
  have hspan : (fun _ => (1 : ℚ)) ∈
      Submodule.span ℚ (Set.range (indTrivCyclic (G := G))) := by
    by_contra hmem
    obtain ⟨φ, hφ1, hφ0⟩ :=
      Submodule.exists_dual_map_eq_bot_of_notMem hmem inferInstance
    set fd : G → ℚ := fun g => φ (Pi.single g 1) with hfddef
    have hrep : ∀ u : G → ℚ, φ u = ∑ g : G, u g * fd g := by
      intro u
      conv_lhs => rw [← Finset.univ_sum_single u]
      rw [map_sum]
      refine Finset.sum_congr rfl fun g _ => ?_
      have hs : Pi.single g (u g) = u g • Pi.single g (1 : ℚ) := by
        ext j; by_cases hj : j = g <;> simp [hj]
      rw [hs, map_smul, smul_eq_mul]
    -- `hval` is read off `hφ0` without re-elaborating `⊥`: stating the
    -- bottom submodule of `ℚ` afresh sends instance synthesis into a
    -- loop in this module's instance context.
    have hval := Submodule.eq_bot_iff _ |>.1 hφ0
    have hzero : ∀ y : G, ∑ g : G, indTrivCyclic y g * fd g = 0 := by
      intro y
      rw [← hrep]
      exact hval _ (Submodule.mem_map_of_mem (Submodule.subset_span ⟨y, rfl⟩))
    have hcyc : ∀ y : G,
        ∑ h ∈ Finset.univ.filter (fun h => h ∈ Subgroup.zpowers y),
          ∑ x : G, fd (x * h * x⁻¹) = 0 := by
      intro y
      have hN : (Nat.card (Subgroup.zpowers y) : ℚ) ≠ 0 := by
        have hp : 0 < Nat.card (Subgroup.zpowers y) := Nat.card_pos
        exact_mod_cast hp.ne'
      have h2 := sum_indTrivCyclic_mul y fd
      rw [hzero y] at h2
      rcases mul_eq_zero.1 h2.symm with h | h
      · exact absurd (inv_eq_zero.1 h) hN
      · exact h
    have hsum := sum_eq_zero_of_cyclic_sums
      (fun h => ∑ x : G, fd (x * h * x⁻¹)) hcyc
    have hcard : ∑ g : G, (∑ x : G, fd (x * g * x⁻¹))
        = Fintype.card G * ∑ g : G, fd g := by
      rw [Finset.sum_comm]
      have hconj : ∀ x : G, ∑ g : G, fd (x * g * x⁻¹) = ∑ g : G, fd g := by
        intro x
        refine Fintype.sum_equiv
          ((Equiv.mulLeft x).trans (Equiv.mulRight x⁻¹)) _ _ ?_
        intro h
        simp
      rw [Finset.sum_congr rfl (fun x _ => hconj x)]
      simp [Finset.sum_const, Finset.card_univ]
    rw [hcard] at hsum
    have hG : (Fintype.card G : ℚ) ≠ 0 := by
      have hp : 0 < Fintype.card G := Fintype.card_pos
      exact_mod_cast hp.ne'
    have hfd0 : ∑ g : G, fd g = 0 := by
      rcases mul_eq_zero.1 hsum with h | h
      · exact absurd h hG
      · exact h
    apply hφ1
    rw [hrep]
    simpa using hfd0
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℚ).1 hspan
  refine ⟨c, fun g => ?_⟩
  have hg := congrFun hc g
  simpa using hg

/-- **Artin's induction theorem — trivial-character form** (PROVEN
2026-07-24; FOUNDER leaf, pure finite group theory — the
group-theoretic engine of the `ℓ`-adic Brauer descent): for a finite
group `G` the trivial character is a `ℚ`-linear combination of
characters induced from one-dimensional characters of SOLVABLE (in
fact CYCLIC) subgroups. The data is presented explicitly and
self-containedly: subgroups `H i`, one-dimensional characters of `H i`
carried as functions `φ i : G → ℂ` extended by zero off `H i` (the
three conditions say exactly that: `φ i` vanishes outside `H i`, sends
`1` to `1`, and is multiplicative on `H i` — its values on `H i` are
then |G|-th roots of unity, each element having finite order), and
rationals `c i`, such that the Frobenius-formula combination
`Σᵢ cᵢ · |Hᵢ|⁻¹ · Σ_{x ∈ G} φᵢ(x⁻¹ g x)` — the `i`-th inner term is
the induced character `Ind_{Hᵢ}^G χᵢ` evaluated at `g` — is the
constant `1`.

RESTATEMENT (2026-07-24, ℤ → ℚ): this node was originally stated with
INTEGER coefficients `c i`, i.e. as BRAUER's induction theorem (Serre,
§10.5, Theorems 18–19; Isaacs, Theorem 8.4; Curtis–Reiner §15), whose
proof is a genuine project (`p`-elementary subgroups, algebraic
integrality of character values, the Brauer/Banaschewski counting
argument). Its consumer
(`exists_heckeField_system_of_witness_of_pieces`) only ever forms the
combination `Σᵢ cᵢ · (traces in the Hecke field `E`)`, and `E` is a
number field — a `ℚ`-algebra — so RATIONAL coefficients are exactly as
good as integral ones there; nothing downstream uses integrality. The
node is therefore restated with `c : Fin n → ℚ` and PROVEN, in the
weaker but sufficient ARTIN form (Serre, §9.2, Theorem 17: cyclic
subgroups, rational coefficients). The declaration keeps its
`brauer_`-name for continuity with its consumers and with the
`PROGRESS.md` tree. The subgroups produced are cyclic, hence
commutative, hence solvable — which is what solvable base change
consumes downstream.

PIN AUDIT (2026-07-24, hard search): the mathlib pin has the induction
functor (`Representation.ind`, `Mathlib/RepresentationTheory/
Induced.lean` — a categorical adjunction, no character formula) and
basic character theory (`Mathlib/RepresentationTheory/Character.lean`:
orthogonality only), but NO induced-character formula, NO virtual
characters, NO Artin or Brauer induction in any form (`grep Brauer`
over `Mathlib/`: only Brauer GROUPS of fields). The statement is
therefore self-contained (no `FDRep`, no decidability or subtype
baggage — the extension-by-zero form makes the induced character an
unrestricted sum over `G`), in the exact shape its consumer needs, and
the Artin development above (`cyclicIndicator`, `indTrivCyclic`,
`sum_indTrivCyclic_mul`, `sum_eq_zero_of_cyclic_sums`,
`exists_artin_coeffs`) is written from scratch in-tree.

PROOF: `exists_artin_coeffs` on `G` produces rational coefficients
`c : G → ℚ` with `Σ_{y ∈ G} c y · Ind_{⟨y⟩}^G 1 = 1`; reindex the
family along `Fin (Fintype.card G) ≃ G`, take `H i = ⟨y i⟩` (cyclic,
hence commutative, hence solvable by `isSolvable_of_comm`) and
`φ i = ` the extension-by-zero indicator of `H i`, whose three
character conditions are immediate, and transport the `ℚ`-identity
into `ℂ` along the field embedding `ℚ → ℂ`.

SOUNDNESS AUDIT (2026-07-24): a true classical theorem with NO vacuity
route — this node carries no arithmetic hypotheses, so unlike the
arithmetic leaves of this module it must be (and is) directly true as
stated: Serre §9.2, Theorem 17, applied to `1_G`, with each cyclic
subgroup relabelled solvable. Edge `G = 1`: the family is the single
cyclic subgroup `⟨1⟩ = ⊤` with coefficient `1`. -/
theorem brauer_induction_trivial_character (G : Type*) [Group G]
    [Fintype G] :
    ∃ (n : ℕ) (H : Fin n → Subgroup G) (φ : Fin n → G → ℂ)
      (c : Fin n → ℚ),
      (∀ i, IsSolvable (H i)) ∧
      (∀ i, ∀ g ∉ H i, φ i g = 0) ∧
      (∀ i, φ i 1 = 1) ∧
      (∀ i, ∀ a ∈ H i, ∀ b ∈ H i, φ i (a * b) = φ i a * φ i b) ∧
      (∀ g : G, ∑ i, (c i : ℂ) * (Nat.card (H i) : ℂ)⁻¹ *
        ∑ x : G, φ i (x⁻¹ * g * x) = 1) := by
  obtain ⟨c, hc⟩ := exists_artin_coeffs G
  let e : Fin (Fintype.card G) ≃ G := (Fintype.equivFin G).symm
  refine ⟨Fintype.card G, fun i => Subgroup.zpowers (e i),
    fun i g => ((cyclicIndicator (e i) g : ℚ) : ℂ), fun i => c (e i),
    ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    exact isSolvable_of_comm (fun a b => mul_comm' a b)
  · intro i g hg
    simp [cyclicIndicator, hg]
  · intro i
    simp [cyclicIndicator]
  · intro i a ha b hb
    have ha' : a ∈ Subgroup.zpowers (e i) := ha
    have hb' : b ∈ Subgroup.zpowers (e i) := hb
    have hab : a * b ∈ Subgroup.zpowers (e i) := mul_mem ha' hb'
    simp [cyclicIndicator, ha', hb', hab]
  · intro g
    have hterm : ∀ i : Fin (Fintype.card G),
        ((c (e i) : ℂ) * (Nat.card (Subgroup.zpowers (e i)) : ℂ)⁻¹ *
          ∑ x : G, ((cyclicIndicator (e i) (x⁻¹ * g * x) : ℚ) : ℂ))
          = ((c (e i) * indTrivCyclic (e i) g : ℚ) : ℂ) := by
      intro i
      rw [indTrivCyclic]
      push_cast
      ring
    rw [Finset.sum_congr rfl (fun i _ => hterm i), ← Rat.cast_sum,
      Equiv.sum_comp e (fun y => c y * indTrivCyclic y g), hc g]
    norm_num

end ArtinInduction

/-- **The descended Hecke system over a fixed field** (the shared shape
of the `ℓ`-adic solvable-descent chain — the sharpest pin-stateable
joint of solvable base change on this pin): the Frobenius
characteristic polynomials of `ρ` restricted to `G_K`, `K = F^C`, are
`E`-coefficient polynomials through `ιO`/`ψℓ` away from a finite set of
places of `K`.

This is verbatim the conclusion of
`exists_descended_heckeSystem_of_solvable` with the subgroup as a
parameter; naming it lets the descent run as an INDUCTION along a
cyclic refinement of the solvable group: `C ↦ F^C` is
inclusion-reversing, so a chain `⊥ = C₀ ≤ ⋯ ≤ Cₙ = H` of subgroups is a
tower `F = F^{C₀} ⊇ ⋯ ⊇ F^{Cₙ} = K` of intermediate fields, each step
of which is the cyclic descent of the literature (Langlands 1980,
Arthur–Clozel 1989).

JOINT NOTE (2026-07-24): the reference Lean project (`~/cs/FLT`,
`FLT/GaloisRepresentation/Automorphic.lean`, `cyclic_base_change`)
states solvable base change at the AUTOMORPHIC joint — an `IsAutomorphic`
predicate on quaternionic forms, an iff between automorphy over `F` and
over a solvable `E/F`. This pin has no automorphy predicate (this
module records "modular" everywhere through Hecke eigensystems only:
`PotentialModularityWitness.modularF`), so that statement is not
vendorable — pin drift aside, the vocabulary does not exist here. The
eigensystem shape below is the corresponding joint in this module's own
vocabulary: it is what the Brauer gluing
(`exists_heckeField_system_of_witness_of_pieces`) consumes and all it
consumes.

Note that the restriction is taken from `ℚ` DIRECTLY at every stage
(`ρ.map (algebraMap ℚ (fixedField C))`), never as a restriction from
the previous stage: no compatibility of restrictions along the tower is
needed anywhere in the descent.

────────────────────────────────────────────────────────────────────
CUT-LEVEL REPAIR (2026-07-27) — THIS DATUM NOW CARRIES A CUSPIDAL
EIGENSYSTEM, AND ITS COEFFICIENT FIELD IS EXISTENTIAL.

THE DEFECT.  In its previous form this predicate was literally
`∃ S P, ∀ w ∉ S, (charFrob w).map ιO = (P w).map ψℓ` — bare
`E`-rationality of Frobenius characteristic polynomials against an
otherwise UNCONSTRAINED function `P`.  It contained no automorphy
whatsoever.  But the prime-degree step of the descent cites
Arthur–Clozel Ch. 3 Thm 4.2(d), whose INPUT is a cuspidal
`Gal(L/M)`-invariant automorphic `Π` over `L`.  Only the base case
`C = ⊥` supplied one — there `P` is `Wit.heckeF`, the Hilbert newform of
the carrier — while EVERY later inductive step fed the citation the
previous step's bare polynomial system, which is not an automorphic
object at all.  The citation was therefore unsupported at every stage
but the first, and no amount of added automorphic theory could repair
that: the defect was a missing HYPOTHESIS, not a missing theorem.

THE REPAIR.  The datum now carries, over `L = F^C`:

* (1) the eigensystem in HILBERT-NEWFORM SHAPE — the Hecke polynomial is
  `X² − a_w·X + Nw`, i.e. parallel weight `2` with trivial nebentypus,
  rather than an arbitrary polynomial;
* (2) CUSPIDALITY, as the Ramanujan–Petersson/Weil bound
  `‖φ(a_w)‖ ≤ 2√(Nw)` at every complex embedding `φ` of the coefficient
  field.  This is the formal shadow of cuspidality available in this
  module's vocabulary, and it is genuinely discriminating: an Eisenstein
  eigensystem has `a_w = 1 + Nw`, which EXCEEDS `2√(Nw)` for `Nw ≠ 1`, so
  the clause excludes exactly the objects AC 4.2(d) must exclude;
* (3) `Gal(L/M)`-INVARIANCE, in the stronger and self-contained form of
  invariance under the whole of `Aut(L/ℚ)`.  Since `C ⊴ D` gives
  `Gal(L/M) ↪ Aut(L/ℚ)`, this delivers precisely the invariance the
  citation consumes.  Clause (3) is PROVEN at every stage, not assumed —
  `charFrob` is invariant under a `ℚ`-automorphism of the base
  (`GaloisRep.charFrob_map_algEquiv`) and the coefficient embedding is
  injective, so the eigenvalue function inherits the invariance.

THE COEFFICIENT FIELD IS EXISTENTIAL, AND THIS IS FORCED.  The predicate
used to type its polynomials as `Polynomial Wit.E` — the SAME `Wit.E` at
every `C`.  That is not sustainable: the Hecke field GROWS down the
tower.  At a place `w` of `M` inert in `L/M` of degree `p`, the eigenvalue
upstairs and the one downstairs are related by the Dickson identity
`a_W = D_p(a_w, Nw)`; the descent KNOWS `a_W` and must SOLVE for `a_w`, so
`a_w` is a root of a degree-`p` polynomial over the previous field and is
in general of degree `p` over it, not in it.  Nothing in
`PotentialModularityWitness` constrains `E` beyond `Field`/`NumberField`,
and its DESCENT-CLOSURE note ("`E` is to be understood as chosen large
enough") is an UNDERSTANDING, not a hypothesis — unusable inside a Lean
proof of a leaf that universally quantifies over `Wit`.  So the datum now
existentially quantifies a number field `E'` with an embedding
`ψ : E' → ℚ̄_ℓ` and an embedding `ι : Wit.E → E'` compatible with it
(`ψ ∘ ι = ψℓ`), recording that the descended field CONTAINS the carrier's
Hecke field.

The residual `Wit.E`-rationality obligation this creates — needed only by
the DOWNSTREAM Brauer gluing, which must read all pieces in one field —
is now the named leaf `heckeField_descentClosed_of_witness` below, which
is exactly the formal content of the DESCENT-CLOSURE note.  Its proper
long-term home is a new FIELD of `PotentialModularityWitness`; that
structure is not this owner's to edit, so the obligation is stated here
where it is consumed.

UPDATE 2026-07-27: that move HAS been made.  `PotentialModularityWitness`
now carries the field `descentClosed`, so the sentence above about `E`
being constrained only by `Field`/`NumberField` is no longer accurate;
`heckeField_descentClosed_of_witness` is a proven projection onto the new
field, and the obligation is discharged at the single inhabitation site
by `exists_descentClosed_heckePackage`.  Nothing about this definition
changed — the coefficient field here is still, correctly, existential.

WHAT THIS BUYS, precisely: the prime step now RECEIVES the cuspidal,
`Gal(L/M)`-invariant object Thm 4.2(d) requires and RETURNS the cuspidal
`π` the next step needs, so the citation is supported at EVERY stage of
the tower rather than only the first. -/
def HeckeSystemDescendsTo {ℓ : ℕ} [Fact ℓ.Prime]
    {O : Type u} [CommRing O] [TopologicalSpace O] [IsTopologicalRing O]
    {ρ : GaloisRep ℚ O (Fin 2 → O)}
    (Wit : PotentialModularityWitness ℓ O ρ)
    (C : Subgroup (Wit.F ≃ₐ[ℚ] Wit.F)) : Prop :=
  ∃ (E' : Type u) (_ : Field E') (_ : NumberField E')
      (ψ : E' →+* AlgebraicClosure ℚ_[ℓ]) (ι : Wit.E →+* E'),
      (∀ x : Wit.E, ψ (ι x) = Wit.ψℓ x) ∧
      ∃ (S : Finset (HeightOneSpectrum (NumberField.RingOfIntegers
          (IntermediateField.fixedField C))))
        (a : HeightOneSpectrum (NumberField.RingOfIntegers
          (IntermediateField.fixedField C)) → E'),
        (∀ w ∉ S,
          ((ρ.map (algebraMap ℚ (IntermediateField.fixedField C))).charFrob
              w).map Wit.ιO =
            (Polynomial.X ^ 2 - Polynomial.C (a w) * Polynomial.X +
              Polynomial.C ((Ideal.absNorm w.asIdeal : ℕ) : E')).map ψ) ∧
        (∀ w ∉ S, ∀ φ : E' →+* ℂ,
          ‖φ (a w)‖ ≤ 2 * Real.sqrt (Ideal.absNorm w.asIdeal)) ∧
        (∀ τ : IntermediateField.fixedField C ≃ₐ[ℚ] IntermediateField.fixedField C,
          ∀ w ∉ S, NumberField.finitePlaceEquiv τ.toRingEquiv w ∉ S →
            a (NumberField.finitePlaceEquiv τ.toRingEquiv w) = a w)

-- `HeckeSystemDescendsToRaw` — the OLD, automorphy-free, fixed-`Wit.E` shape of
-- the descended Hecke system — stood here as transition scaffolding for the
-- 2026-07-27 cut-level repair, as the sole hypothesis of the trace-only route
-- (`exists_heckeTrace_of_prime_cyclic_step`, itself deleted 2026-07-27 as
-- free-floating).  It was RETIRED on 2026-07-27 once
-- that node and the two inert leaves beneath it were restated over the
-- EXISTENTIAL coefficient field: the predicate had no producer, and a dead
-- predicate left in place is how a refuted shape acquires new consumers.  The
-- fixed-`Wit.E` claim it encoded is the one the Dickson field-growth argument
-- refutes for an arbitrary carrier (see `HeckeSystemDescendsTo`'s
-- coefficient-field paragraph above).

/-- **Dévissage step for a finite solvable group** (proven; the engine of
`exists_cyclicRefinement_of_isSolvable` below): a nontrivial finite
solvable group `P` has a NORMAL subgroup `N ≠ ⊤` with CYCLIC quotient.

The statement is `∀`-quantified over the group and bounded by a natural
number `k` so that it can be proven by ordinary induction on `k` while
the group itself changes at every step (the recursion descends through
QUOTIENTS, which leave the original type). Normality is carried as an
anonymous existential so that the quotient group structure — hence
`IsCyclic` — is available inside the statement, exactly as in the
consumer below.

Proof: induction on the bound `k`.
* If `P` is itself cyclic, take `N = ⊥` (`P ⧸ ⊥ ≃* P`, and `⊥ ≠ ⊤`
  because `P` is nontrivial).
* Otherwise pick a normal subgroup `Q` with `⊥ ≠ Q ≠ ⊤`: if
  `commutator P = ⊥` then `P` is abelian, so for any `a ≠ 1` the
  subgroup `zpowers a` is normal, nontrivial, and not `⊤` (else `P`
  would be cyclic); if `commutator P ≠ ⊥` take `Q = commutator P`,
  which is `≠ ⊤` by `IsSolvable.commutator_lt_top_of_nontrivial`.
  Then `P ⧸ Q` is nontrivial, solvable, and strictly smaller
  (`Nat.card Q * Q.index = Nat.card P` with `1 < Nat.card Q`), so the
  inductive hypothesis gives `M ⊴ P ⧸ Q`, `M ≠ ⊤`, with cyclic
  quotient; pull it back: `N := M.comap (QuotientGroup.mk' Q)` is
  normal, is `≠ ⊤` because `Subgroup.comap` is injective along a
  surjection, and `P ⧸ N → (P ⧸ Q) ⧸ M` is injective, so `P ⧸ N` is
  cyclic by `isCyclic_of_injective`. -/
theorem exists_normal_ne_top_isCyclic_quotient_of_card_le (k : ℕ) :
    ∀ (P : Type*) [Group P] [Finite P] [IsSolvable P] [Nontrivial P],
      Nat.card P ≤ k → ∃ (N : Subgroup P) (_ : N.Normal), N ≠ ⊤ ∧ IsCyclic (P ⧸ N) := by
  induction k with
  | zero =>
      intro P _ _ _ _ hcard
      have := Nat.card_pos (α := P)
      omega
  | succ k ih =>
      intro P _ _ _ _ hcard
      by_cases hcyc : IsCyclic P
      · refine ⟨⊥, inferInstance, bot_ne_top, ?_⟩
        exact isCyclic_of_injective (QuotientGroup.quotientBot (G := P)).toMonoidHom
          (QuotientGroup.quotientBot (G := P)).injective
      · obtain ⟨Q, hQn, hQb, hQt⟩ : ∃ Q : Subgroup P, Q.Normal ∧ Q ≠ ⊥ ∧ Q ≠ ⊤ := by
          by_cases hcomm : commutator P = ⊥
          · haveI : IsMulCommutative P := (commutator_eq_bot_iff P).mp hcomm
            obtain ⟨a, ha⟩ := exists_ne (1 : P)
            refine ⟨Subgroup.zpowers a, inferInstance, ?_, ?_⟩
            · simpa [Subgroup.zpowers_eq_bot] using ha
            · exact fun h => hcyc (isCyclic_iff_exists_zpowers_eq_top.mpr ⟨a, h⟩)
          · exact ⟨commutator P, inferInstance, hcomm,
              (IsSolvable.commutator_lt_top_of_nontrivial P).ne⟩
        haveI := hQn
        obtain ⟨x, hx⟩ : ∃ x : P, x ∉ Q := by
          by_contra h
          exact hQt ((Subgroup.eq_top_iff' Q).mpr fun y => not_not.mp fun hy => h ⟨y, hy⟩)
        haveI hnt : Nontrivial (P ⧸ Q) :=
          ⟨⟨QuotientGroup.mk x, 1, by simpa [QuotientGroup.eq_one_iff] using hx⟩⟩
        have hcard' : Nat.card (P ⧸ Q) ≤ k := by
          have h1 : Nat.card Q * Q.index = Nat.card P := Subgroup.card_mul_index Q
          have h2 : 1 < Nat.card Q :=
            not_le.mp fun h => hQb ((Subgroup.card_le_one_iff_eq_bot Q).mp h)
          have h3 : Nat.card (P ⧸ Q) = Q.index := (Subgroup.index_eq_card Q).symm
          have h4 : 0 < Q.index := by rw [← h3]; exact Nat.card_pos
          rw [h3]
          nlinarith [h1, h2, h4, hcard]
        obtain ⟨M, hMn, hMt, hMc⟩ := ih (P ⧸ Q) hcard'
        haveI := hMn
        refine ⟨M.comap (QuotientGroup.mk' Q), inferInstance, ?_, ?_⟩
        · intro h
          exact hMt (Subgroup.comap_injective (QuotientGroup.mk'_surjective Q)
            (h.trans (Subgroup.comap_top (QuotientGroup.mk' Q)).symm))
        · refine isCyclic_of_injective
            (QuotientGroup.map (M.comap (QuotientGroup.mk' Q)) M (QuotientGroup.mk' Q) le_rfl) ?_
          intro a b hab
          obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
          obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
          simp only [QuotientGroup.map_mk] at hab
          rw [QuotientGroup.eq] at hab ⊢
          rw [Subgroup.mem_comap, _root_.map_mul, _root_.map_inv]
          exact hab

/-- **Cyclic refinement of a solvable subgroup, bounded form** (proven;
the induction carrying `exists_cyclicRefinement_of_isSolvable`): the
chain is built top-down by strong induction on the order of `H`, the
bound `k` making that induction an ordinary `Nat` induction.

At each stage: if `H = ⊥` the chain is `n = 0`, `C ≡ ⊥` (the step
condition is vacuous). Otherwise `↥H` is a nontrivial finite solvable
group, so the dévissage step above yields `N ⊴ ↥H`, `N ≠ ⊤`, with
cyclic quotient; `K := N.map H.subtype` is the corresponding subgroup
of `G`, it satisfies `K ≤ H`, `K.subgroupOf H = N`
(`Subgroup.comap_map_eq_self_of_injective`), it is solvable
(`Subgroup.inclusion` is injective into `↥H`), and it is strictly
smaller than `H` because `N ≠ ⊤`. The inductive hypothesis gives a
chain `⊥ = C 0 ≤ ⋯ ≤ C n = K`, which is extended by one step to `H`;
reindexing is by `fun i => if i < n + 1 then C i else H`. -/
theorem exists_cyclicRefinement_of_isSolvable_of_card_le {G : Type*} [Group G] [Finite G]
    (k : ℕ) :
    ∀ (H : Subgroup G), IsSolvable H → Nat.card H ≤ k →
      ∃ (n : ℕ) (C : ℕ → Subgroup G),
        C 0 = ⊥ ∧ C n = H ∧
        ∀ i < n, C i ≤ C (i + 1) ∧
          ∃ _ : ((C i).subgroupOf (C (i + 1))).Normal,
            IsCyclic (C (i + 1) ⧸ (C i).subgroupOf (C (i + 1))) := by
  induction k with
  | zero =>
      intro H _ hcard
      have := Nat.card_pos (α := (H : Type _))
      omega
  | succ k ih =>
      intro H hH hcard
      haveI := hH
      by_cases hbot : H = ⊥
      · exact ⟨0, fun _ => ⊥, rfl, hbot.symm, fun i hi => absurd hi (Nat.not_lt_zero i)⟩
      · haveI : Nontrivial H := (Subgroup.nontrivial_iff_ne_bot H).mpr hbot
        obtain ⟨N, hNn, hNt, hNc⟩ :=
          exists_normal_ne_top_isCyclic_quotient_of_card_le (Nat.card H) H le_rfl
        haveI := hNn
        have hKH : N.map H.subtype ≤ H := Subgroup.map_subtype_le N
        have hsub : (N.map H.subtype).subgroupOf H = N :=
          Subgroup.comap_map_eq_self_of_injective H.subtype_injective N
        have hKsolv : IsSolvable (N.map H.subtype) :=
          solvable_of_solvable_injective (Subgroup.inclusion_injective hKH)
        have hcardK : Nat.card (N.map H.subtype) ≤ k := by
          have h1 : Nat.card (N.map H.subtype) = Nat.card N :=
            (Nat.card_congr (Subgroup.equivMapOfInjective N H.subtype
              H.subtype_injective).toEquiv).symm
          have h2 : Nat.card N * N.index = Nat.card H := Subgroup.card_mul_index N
          have h3 : 1 < N.index := Subgroup.one_lt_index_of_ne_top hNt
          have h4 : 0 < Nat.card N := Nat.card_pos
          rw [h1]
          nlinarith [h2, h3, h4, hcard]
        obtain ⟨n, C, hC0, hCn, hCstep⟩ := ih (N.map H.subtype) hKsolv hcardK
        obtain ⟨D, hDlt, hDtop⟩ : ∃ D : ℕ → Subgroup G,
            (∀ i, i < n + 1 → D i = C i) ∧ D (n + 1) = H :=
          ⟨fun i => if i < n + 1 then C i else H, fun _ hi => if_pos hi, if_neg (by omega)⟩
        refine ⟨n + 1, D, ?_, hDtop, ?_⟩
        · rw [hDlt 0 (by omega), hC0]
        · intro i hi
          rcases lt_or_eq_of_le (Nat.lt_succ_iff.mp hi) with h | h
          · rw [hDlt i (by omega), hDlt (i + 1) (by omega)]
            exact hCstep i h
          · have e2 : D (i + 1) = H := by rw [h]; exact hDtop
            rw [hDlt i (by omega), e2, h, hCn, hsub]
            exact ⟨hKH, hNn, hNc⟩

/-- **Cyclic refinement of a solvable subgroup** (PROVEN 2026-07-25;
FOUNDER leaf, pure finite group theory — the group-theoretic engine of the
solvable-descent chain, as `brauer_induction_trivial_character` is the
engine of the Brauer decomposition): a solvable subgroup `H` of a
finite group `G` sits at the top of a finite ascending chain of
subgroups starting at `⊥`, each step `C i ≤ C (i+1)` being NORMAL with
CYCLIC quotient.

The data is presented explicitly and self-containedly: the chain as a
function `C : ℕ → Subgroup G` (only its values at `0, …, n` matter),
the endpoints as equations, and the step condition as inclusion plus
normality of `C i` inside `C (i+1)` (as a subgroup of the coerced group
`↥(C (i+1))`, i.e. `(C i).subgroupOf (C (i+1))`) plus cyclicity of the
quotient. Normality is carried as an anonymous existential precisely so
that the quotient group structure — and hence `IsCyclic` — is available
inside the statement.

Literature: the standard dévissage of a finite solvable group. `H` is
solvable, so its derived series `H ⊇ H' ⊇ H'' ⊇ ⋯` terminates at `⊥`
(mathlib: `derivedSeries`, `IsSolvable`) with ABELIAN quotients; each
abelian step is refined into cyclic steps by choosing generators one at
a time (equivalently by the structure theorem for finite abelian
groups: an abelian group with a chosen generating set
`{g₁, …, g_r}` gives the chain `⟨g₁⟩ ≤ ⟨g₁, g₂⟩ ≤ ⋯`, whose successive
quotients are cyclic), and the refined chain is reindexed by `ℕ`.
References: Rotman, *An Introduction to the Theory of Groups*, Thm 5.15
(solvable ⇔ a subnormal series with cyclic factors, for finite groups);
Isaacs, *Finite Group Theory*, §3B; Serre, *Linear Representations*,
§8.

PIN AUDIT (2026-07-24): the mathlib pin has `IsSolvable`,
`derivedSeries` and the abelian-quotient facts, and `IsCyclic` with the
finite-abelian structure theory, but no chain/refinement statement of
this shape (`grep` for `subnormal`, `compositionSeries` over
`Mathlib/GroupTheory/`: `CompositionSeries` is about SIMPLE factors, not
cyclic ones, and carries no solvability bridge). The leaf is therefore
stated self-containedly in the exact shape its consumer
(`exists_descended_heckeSystem_of_solvable`) needs; it is genuinely
provable in-tree — finite group theory only — but is a real project
(derived-series dévissage plus abelian refinement), hence a leaf.

SOUNDNESS AUDIT (2026-07-24): a true classical theorem with NO vacuity
route — this leaf carries no arithmetic hypotheses, so, like the Brauer
leaf above and unlike the arithmetic leaves of this module, it must be
(and is) directly true as stated. Edge `H = ⊥`: take `n = 0`, `C ≡ ⊥`,
the step condition being vacuous.

PROOF (2026-07-25): discharged in-tree, exactly as the pin audit
predicted, but by a single dévissage induction rather than by
"derived series, then refine each abelian quotient". The two are
equivalent and the one-step form is much shorter to formalize: the only
thing needed at the top is ONE normal subgroup of `↥H` with cyclic
quotient, and that is produced by
`exists_normal_ne_top_isCyclic_quotient_of_card_le` above (cyclic ⇒
`N = ⊥`; otherwise descend to a proper quotient, using
`commutator P ≠ ⊤` for nontrivial solvable `P`, or `zpowers a` when `P`
is abelian and non-cyclic). Recursing on the resulting smaller subgroup
(`exists_cyclicRefinement_of_isSolvable_of_card_le`) and prepending its
chain gives the statement; no structure theorem for finite abelian
groups is used. -/
theorem exists_cyclicRefinement_of_isSolvable {G : Type*} [Group G]
    [Finite G] (H : Subgroup G) (hH : IsSolvable H) :
    ∃ (n : ℕ) (C : ℕ → Subgroup G),
      C 0 = ⊥ ∧ C n = H ∧
      ∀ i < n, C i ≤ C (i + 1) ∧
        ∃ _ : ((C i).subgroupOf (C (i + 1))).Normal,
          IsCyclic (C (i + 1) ⧸ (C i).subgroupOf (C (i + 1))) :=
  exists_cyclicRefinement_of_isSolvable_of_card_le (Nat.card H) H hH le_rfl

/-- **Finitely many places of a number field lie over a rational prime**
(PROVEN, elementary bookkeeping): for a nonzero natural number `n` and a
number field `M`, all but finitely many finite places `w` of `M` satisfy
`n ∉ w`.

Proof: the ideal `span {n}` of `𝓞 M` is nonzero, so only finitely many
height-one primes divide it (`Ideal.finite_factors`), and in the Dedekind
domain `𝓞 M` "divides" is "contains" (`Ideal.dvd_iff_le`), which for the
principal ideal `span {n}` is exactly `n ∈ w`.

This is the bookkeeping that turns the POINTWISE determinant lemma
`charFrob_baseChange_coeff_zero_eq_absNorm` (whose hypothesis is
`ℓ ∉ w`) into an "away from a finite set of places" statement — the
shape `HeckeSystemDescendsTo` is written in. -/
theorem exists_finset_forall_natCast_notMem_asIdeal
    (M : Type u) [Field M] [NumberField M] (n : ℕ) (hn : n ≠ 0) :
    ∃ S : Finset (HeightOneSpectrum (NumberField.RingOfIntegers M)),
      ∀ w ∉ S, (n : NumberField.RingOfIntegers M) ∉ w.asIdeal := by
  classical
  have hne : (Ideal.span {(n : NumberField.RingOfIntegers M)}) ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact Nat.cast_ne_zero.mpr hn
  refine ⟨(Ideal.finite_factors hne).toFinset, fun w hw hmem => ?_⟩
  refine hw ?_
  rw [Set.Finite.mem_toFinset]
  exact Ideal.dvd_iff_le.mpr (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hmem))

/-- **A bound at every complex embedding transfers between number fields
along a shared image in a common overfield** (PROVEN; pure
algebraic-number theory, no arithmetic input whatsoever).

If `x : E'` and `c : E` have the SAME image in some characteristic-zero
field `Ω` — here always `ℚ̄_ℓ`, through the two chosen `ℓ`-adic places
`ψE'` and `ψE` — then `x` and `c` are literally the same algebraic
number, read in two different number fields.  Hence they have the same
minimal polynomial over `ℚ`, hence the same set of complex conjugates,
and any bound holding at every complex embedding of `E` holds at every
complex embedding of `E'`.

WHY THIS IS NEEDED HERE.  The descent statements of this module are
typed over an EXISTENTIAL coefficient field (see the coefficient-field
paragraph of `HeckeSystemDescendsTo`), while the Ramanujan–Petersson
citation is naturally a statement about the CARRIER's Hecke field
`Wit.E`.  The two fields are related only by having a common
`ℚ̄_ℓ`-realization, which is exactly the hypothesis `h` below — there is
in general no embedding `Wit.E → E'` available at the point of use.  So
this lemma is what lets a bound proven for the newform's eigenvalue be
read off for the descended eigenvalue.

PROOF.  `minpoly.algHom_eq` applied to `ψE'` and `ψE` (both injective,
being ring homomorphisms out of fields, and both automatically
`ℚ`-algebra maps in characteristic zero via `RingHom.toRatAlgHom`) gives
`minpoly ℚ x = minpoly ℚ (ψE' x) = minpoly ℚ (ψE c) = minpoly ℚ c`.
Then `NumberField.Embeddings.range_eval_eq_rootSet_minpoly` identifies
`{φ x | φ : E' →+* ℂ}` and `{φ c | φ : E →+* ℂ}` with the SAME root set
`(minpoly ℚ c).rootSet ℂ`, so every value `φ x` is some value `φ' c`. -/
theorem forall_complexEmbedding_norm_le_of_ringHom_eq {Ω : Type*} [Field Ω]
    [CharZero Ω] {E E' : Type*} [Field E] [NumberField E] [Field E']
    [NumberField E'] (ψE : E →+* Ω) (ψE' : E' →+* Ω) {c : E} {x : E'}
    (h : ψE' x = ψE c) {B : ℝ} (hB : ∀ φ : E →+* ℂ, ‖φ c‖ ≤ B) :
    ∀ φ : E' →+* ℂ, ‖φ x‖ ≤ B := by
  have hmin : minpoly ℚ x = minpoly ℚ c := by
    have h1 : minpoly ℚ (ψE' x) = minpoly ℚ x :=
      minpoly.algHom_eq ψE'.toRatAlgHom ψE'.injective x
    have h2 : minpoly ℚ (ψE c) = minpoly ℚ c :=
      minpoly.algHom_eq ψE.toRatAlgHom ψE.injective c
    rw [← h1, ← h2, h]
  intro φ
  have hx : φ x ∈ (minpoly ℚ c).rootSet ℂ := by
    rw [← hmin, ← NumberField.Embeddings.range_eval_eq_rootSet_minpoly]
    exact ⟨φ, rfl⟩
  rw [← NumberField.Embeddings.range_eval_eq_rootSet_minpoly] at hx
  obtain ⟨φ', hφ'⟩ := hx
  rw [← hφ']
  exact hB φ'

/-- **Ramanujan–Petersson for the CARRIER's Hilbert newform** (SORRIED
CITATION — Eichler–Shimura for parallel weight `2`, i.e. Deligne's
theorem via the Blasius/Carayol realization of a Hilbert newform of
parallel weight `2` in the `H¹` of a quaternionic Shimura variety,
together with the Weil conjectures for that variety; Deligne, *La
conjecture de Weil I*, Publ. IHÉS 43 (1974); Blasius, *Hilbert modular
forms and the Ramanujan conjecture*, in *Noncommutative Geometry and
Number Theory* (2006); Carayol, Ann. Sci. ÉNS 19 (1986); Shimura, Duke
Math. J. 45 (1978), for the parallel-weight-`2` normalization
`X² − a_w·X + Nw`).

**THIS IS THE IRREDUCIBLE CLASSICAL CONTENT** extracted from
`weilBound_of_charFrob_baseChange` below (2026-07-27).  It is stated at
the places of `F` — where the witness's newform actually lives — rather
than at the places of an intermediate field, so it is LITERALLY the
classical theorem and nothing else: no base change, no descent, no
coefficient-field bookkeeping.  That is what makes it the reusable form.

STATEMENT.  Away from the witness's own bad set, the linear coefficient
of the Hecke polynomial `Wit.heckeF W = X² − a_W·X + NW` — i.e. `−a_W` —
satisfies `‖φ(a_W)‖ ≤ 2√(NW)` at EVERY complex embedding `φ` of the
carrier's Hecke field.  (The bound is stated for `(heckeF W).coeff 1`
itself rather than for `a_W = −(heckeF W).coeff 1`; the two are
equivalent because `‖−z‖ = ‖z‖`.)

FALSITY AUDIT — **THIS STATEMENT WAS FALSE AS FIRST WRITTEN (2026-07-27,
the day it was split off) AND IS REPAIRED HERE BY RESTORING THE
RESIDUAL-IRREDUCIBILITY HALF OF THE HYPOTHESIS PACKAGE.**  As split off
from `weilBound_of_charFrob_baseChange` the leaf quantified over an
ARBITRARY `ρ` carrying NO hypotheses at all, and argued faithfulness
from `Wit.modularF` PINNING `heckeF` in terms of `ρ` (the paragraph
below, retained because it is correct as far as it goes).  That is true
and beside the point: the junk freedom is in `ρ`, not in `heckeF`.

COUNTEREXAMPLE to the unrepaired statement.  Take `ℓ ≥ 5`,
`O = ℤ_[ℓ]`, `ρ = 1 ⊕ ε_ℓ` (trivial character ⊕ `ℓ`-adic cyclotomic
character), `F = ℚ` (totally real, Galois over `ℚ`), `E = ℚ`,
`badF = ∅`, `heckeF w = X² − (1 + Nw)·X + Nw`, `ψℓ`/`ιO` the evident
embeddings, `B = ℤ_[3]`, `τF = 1 ⊕ ε_3`.  Every field of
`PotentialModularityWitness` holds — `modularF` and `matchF₃` because
`Frob_w` acts as `diag(1, Nw)` in both realizations, and
`descentClosed` because `a w = 1 + Nw` is already rational, so it is
`ι`-rational for every `ι`.  The conclusion demands
`‖1 + Nw‖ ≤ 2√(Nw)`, which FAILS at every `Nw ≥ 2`.  This is precisely
the EISENSTEIN eigensystem that the FAITHFULNESS paragraph below names
as what the bound exists to exclude: nothing in the witness structure
excludes it, because the structure records MODULARITY of `ρ|_{G_F}` but
never CUSPIDALITY of the form.

WHY THE REPAIR IS THE RESIDUAL PACKAGE AND NOT `hρ`.  `1 ⊕ ε_ℓ` is
itself HARDLY RAMIFIED — cyclotomic determinant; unramified outside
`ℓ`; flat at `ℓ`, its mod-`ℓ` reduction being the generic fibre of the
finite flat `ℤ/ℓ × μ_ℓ`; upper-triangular at `2` with the trivial (hence
unramified, square-one) quotient character.  So adding `hρ` alone would
NOT have repaired it, and the sibling
`weilBound_of_charFrob_baseChange_of_inert`, which DID carry `hρ`, was
false for the same `ρ` taken over `F = ℚ(√5)` with `C = ⊤`.  What
`1 ⊕ ε_ℓ` fails is IRREDUCIBILITY, which in this module is always a
SEPARATE hypothesis (`hirr`), is exactly what makes the attached Hilbert
form cuspidal rather than Eisenstein, and is exactly what both soundness
audits in this cluster already invoked — "an irreducible hardly ramified
mod-`ℓ` representation with `ℓ ≥ 5`" — while neither statement carried
it.  The residual block below is copied from
`exists_potentialModularityWitness_of_five_le`, where the witness is
built; the sole consumer, `heckeSystemDescendsTo_bot`, already binds
every piece of it, so the repair costs no new obligation anywhere.

CHECK THAT WOULD REFUTE THIS REPAIR: exhibit a residually irreducible
hardly ramified `ρ` with `ℓ ≥ 5` whose witness carries an Eisenstein
`heckeF`.  There is none, twice over — route (i), residual
irreducibility makes the attached Hilbert newform cuspidal, so Deligne
applies; route (ii), the package is classically unsatisfiable by this
module's headline `not_isIrreducible_of_isHardlyRamified_of_five_le`.
Note that route (ii) was ASSERTED by the sibling's soundness audit
before the repair and was NOT available to it, the irreducibility half
being absent from its binders; it is available now.

FAITHFULNESS (correct as far as it goes, and no longer the whole
story).  At every `W ∉ Wit.badF` the polynomial `Wit.heckeF W` is PINNED
by the structure field `Wit.modularF` — `(charFrob W).map Wit.ιO =
(heckeF W).map Wit.ψℓ` with `Wit.ψℓ` injective — so `heckeF W` is
determined by `ρ` and carries no freedom of its own for a junk witness
to exploit.  The bound is genuinely discriminating rather than
decorative: an Eisenstein eigensystem has `a_W = 1 + NW`, and
`1 + NW > 2√(NW)` for every `NW ≠ 1`, so it is exactly what excludes the
objects Arthur–Clozel Ch. 3 Thm 4.2(d) must exclude.

WHY IT IS NOT A FIELD OF `PotentialModularityWitness`, RE-REPORTED
UPWARD 2026-07-27 AND NOW WITH EVIDENCE.  It should be — CUSPIDALITY is
a property of the newform the structure records, in the same family as
`modularF` and `matchF₃`, and the producing leaf
`exists_potentialModularityWitness_of_five_le` is entitled to supply it
(it holds the whole residual package).  The falsity audit above is the
evidence: because the structure does not record it, EVERY leaf in this
cluster that needs cuspidality must re-import the entire residual
package as hypotheses, and the two that forgot to were both false.  The
architecturally correct repair is a `weilBoundF`/cuspidality FIELD on
`PotentialModularityWitness` (in `Modularity/MoretBailly.lean`),
discharged once at the inhabitation site; this leaf would then be a
one-line projection.  Not done here because that structure is outside
this task's region and adding a field breaks every construction site.

CIRCULARITY GUARD (inherited from pillar β, load-bearing): no discharge
through `Family.lean`, `Lift.lean`, or `Modularity/Interface.lean`. -/
theorem weilBound_heckeF_of_witness
    {ℓ : ℕ} (hℓodd : Odd ℓ) [Fact ℓ.Prime] (hℓ5 : 5 ≤ ℓ)
    {O : Type u} [CommRing O] [IsDomain O] [TopologicalSpace O]
    [IsTopologicalRing O] [Algebra ℤ_[ℓ] O] [IsLocalRing O]
    [Module.Finite ℤ_[ℓ] O] [IsModuleTopology ℤ_[ℓ] O]
    {ρ : GaloisRep ℚ O (Fin 2 → O)}
    (hrank : Module.rank O (Fin 2 → O) = 2)
    (hρ : IsHardlyRamified hℓodd hrank ρ)
    {k : Type u} [Field k] [Finite k] [Algebra ℤ_[ℓ] k]
    [TopologicalSpace k] [DiscreteTopology k]
    {Mbar : Type v} [AddCommGroup Mbar] [Module k Mbar] [Module.Finite k Mbar]
    [Module.Free k Mbar]
    (hMbar : Module.rank k Mbar = 2) {ρbar : GaloisRep ℚ k Mbar}
    (hρbar : IsHardlyRamified hℓodd hMbar ρbar)
    (hirr : ρbar.IsIrreducible)
    (π : O →+* k) (hπsurj : Function.Surjective π)
    (hπ : ∀ (q : ℕ) (hq : q.Prime), q ≠ 2 → q ≠ ℓ →
      (ρ.charFrob hq.toHeightOneSpectrumRingOfIntegersRat).map π =
        ρbar.charFrob hq.toHeightOneSpectrumRingOfIntegersRat)
    (Wit : PotentialModularityWitness ℓ O ρ) :
    ∀ W ∉ Wit.badF, ∀ φ : Wit.E →+* ℂ,
      ‖φ ((Wit.heckeF W).coeff 1)‖ ≤ 2 * Real.sqrt (Ideal.absNorm W.asIdeal) :=
  sorry

/-- **Ramanujan–Petersson at the places of `L = F^C` that do NOT match a
good place of `F`** (SORRIED CITATION; the residual half of
`weilBound_of_charFrob_baseChange` after the 2026-07-27 split).

THE SPLIT, and why this is the shape that is left.  `ρ` is a
representation of `G_ℚ` unramified outside `{2, ℓ}`, so its Frobenius
characteristic polynomial at a place depends only on the residue
CARDINALITY of that place (`charFrob_baseChange_eq_of_absNorm_eq`, below
in this module).  Hence whenever a place `w` of `L` matches a good place
`W` of `F` — same residue cardinality AND same Frobenius charpoly — the
eigenvalue at `w` IS the newform's eigenvalue at `W`, read inside
`ℚ̄_ℓ`, and the Weil bound at `w` follows from the classical theorem at
`W` (`weilBound_heckeF_of_witness`) with NO further automorphic input.
That half is PROVEN in the consumer below.

What genuinely remains is the INERT half: a place `w` of `L` lying under
places of `F` of strictly larger residue degree, so that no place of `F`
has residue cardinality `Nw` at all.  There the eigenvalue at `w` is not
any eigenvalue of the carrier's newform; it is an eigenvalue of the form
DESCENDED to `L`, related to the one upstairs by the Dickson identity
`a_W = D_f(a_w, Nw)` (`f` the residue degree of `F/L` at `w`).  Bounding
it is exactly the assertion that the descended system is CUSPIDAL, which
is the classical cyclic-descent statement (Langlands, *Base Change for
GL(2)*, Ann. of Math. Studies 96 (1980); Arthur–Clozel, Ann. of Math.
Studies 120 (1989), Ch. 3 Thm 4.2) combined with Ramanujan–Petersson for
the descended form.

WHY THE INEQUALITY UPSTAIRS DOES NOT SUFFICE, recorded so the cheap route
is not re-attempted.  From `|φ(a_W)| ≤ 2·Nw^{f/2}` and `α_W β_W = Nw^f`
one CANNOT conclude `|α_w| = |β_w| = √(Nw)`: that step needs the SHARP
form of the bound (the two Frobenius eigenvalues have absolute value
exactly `√(NW)`), which in turn needs `φ(a_W)` to be REAL — i.e. total
reality of the Hecke field of a parallel-weight-`2` Hilbert newform with
trivial nebentypus.  Total reality of `Wit.E` is NOT among the fields of
`PotentialModularityWitness`, and the eigenvalues live in `ℚ̄_ℓ` rather
than in `ℂ`, so the elementary route is unavailable at this pin in two
independent ways.  CHECK THAT WOULD REFUTE THIS: exhibit a proof of
`|α| = |β| = √q` from `α β = q`, `|α^f + β^f| ≤ 2 q^{f/2}` alone, for
some `f > 1`, with `α + β` not assumed real.  (It is false: take `q = 1`,
`f = 2`, `α = 2`, `β = 1/2`; then `α² + β² = 4.25 > 2`, so pick instead
`α = i·t`, `β = 1/(i·t)` — the point is that only reality forces the
conjugate pair.)

AXIS SEARCHED, AXIS NOT SEARCHED.  Searched: the elementary/algebraic
axis — deducing the bound downstairs from the bound upstairs by pure
inequalities on Frobenius eigenvalues, in every arrangement the available
`charFrob` API supports.  NOT searched: any route that first constructs
the descended automorphic object, which is the citation itself.

FALSITY AUDIT — **THIS STATEMENT WAS FALSE AS FIRST WRITTEN AND IS
REPAIRED HERE (2026-07-27) BY THE SAME RESIDUAL-IRREDUCIBILITY BLOCK
ADDED TO `weilBound_heckeF_of_witness`; READ THAT LEAF'S AUDIT FIRST.**
The soundness audit below asserted route (ii) — collapse of "an
irreducible hardly ramified mod-`ℓ` representation with `ℓ ≥ 5`" — but
the statement carried only `hρ`, never irreducibility, so route (ii) was
describing a package the binders did not contain.  Route (i) was equally
unavailable: DESCENT of a form is cuspidal only if the form upstairs is.

COUNTEREXAMPLE to the unrepaired statement, which `hρ` alone does not
block.  `ρ = 1 ⊕ ε_ℓ` over `O = ℤ_[ℓ]` IS hardly ramified (see the
sibling's audit for the four clauses).  Take `Wit.F = ℚ(√5)` — totally
real and Galois over `ℚ` — with `E = ℚ`, `badF = ∅`,
`heckeF W = X² − (1 + NW)·X + NW`, `B = ℤ_[3]`, `τF = (1 ⊕ ε_3)|_{G_F}`;
every field of `PotentialModularityWitness` holds as before.  Now take
`C = ⊤`, so `L = F^⊤ = ℚ`, `E' = ℚ`, `ψ = ψℓ`, `S = ∅`,
`a w = 1 + Nw`, which satisfies `ha`.  At a rational prime `p` INERT in
`ℚ(√5)` (i.e. `p ≡ ±2 mod 5`) every place of `F` over `p` has residue
norm `p²`, and no place of `F` over any other prime has norm `p`, so the
hypothesis "`∀ W ∉ badF`, `NW = Np → charFrob W ≠ charFrob w`" holds
VACUOUSLY.  The conclusion then demands `1 + p ≤ 2√p`, false for every
`p ≥ 2`; and there are infinitely many such `p`, so no finite `S'` can
absorb them.  Note this is exactly the INERT half — the counterexample
lives where the residual citation lives, not in the split half that is
proven below.

The repair, as for the sibling, is the residual-irreducibility block,
which is bound in full by the sole consumer `heckeSystemDescendsTo_bot`
and which restores BOTH soundness routes below.

SOUNDNESS AUDIT (both routes now genuinely available, which before the
repair neither was).  (i) Direct: the classical theorem, applied to the
Hilbert newform obtained by descending the carrier's newform to `L` —
cuspidal because residual irreducibility makes the form upstairs
cuspidal.  (ii) Collapse: the hypothesis package (an irreducible hardly
ramified mod-`ℓ` representation with `ℓ ≥ 5`) is classically
unsatisfiable — the headline of this module — so the statement is
classically true for every package.  Route (ii) is a soundness
justification only, NOT an available Lean discharge: the headline
CONSUMES this subtree, so `absurd hirr …` is circular here.

CIRCULARITY GUARD (inherited from pillar β, load-bearing): no discharge
through `Family.lean`, `Lift.lean`, or `Modularity/Interface.lean`. -/
theorem weilBound_of_charFrob_baseChange_of_inert
    {ℓ : ℕ} (hℓodd : Odd ℓ) [Fact ℓ.Prime] (hℓ5 : 5 ≤ ℓ)
    {O : Type u} [CommRing O] [IsDomain O] [TopologicalSpace O]
    [IsTopologicalRing O] [Algebra ℤ_[ℓ] O] [IsLocalRing O]
    [Module.Finite ℤ_[ℓ] O] [IsModuleTopology ℤ_[ℓ] O]
    {ρ : GaloisRep ℚ O (Fin 2 → O)}
    (hrank : Module.rank O (Fin 2 → O) = 2)
    (hρ : IsHardlyRamified hℓodd hrank ρ)
    {k : Type u} [Field k] [Finite k] [Algebra ℤ_[ℓ] k]
    [TopologicalSpace k] [DiscreteTopology k]
    {Mbar : Type v} [AddCommGroup Mbar] [Module k Mbar] [Module.Finite k Mbar]
    [Module.Free k Mbar]
    (hMbar : Module.rank k Mbar = 2) {ρbar : GaloisRep ℚ k Mbar}
    (hρbar : IsHardlyRamified hℓodd hMbar ρbar)
    (hirr : ρbar.IsIrreducible)
    (π : O →+* k) (hπsurj : Function.Surjective π)
    (hπ : ∀ (q : ℕ) (hq : q.Prime), q ≠ 2 → q ≠ ℓ →
      (ρ.charFrob hq.toHeightOneSpectrumRingOfIntegersRat).map π =
        ρbar.charFrob hq.toHeightOneSpectrumRingOfIntegersRat)
    (Wit : PotentialModularityWitness ℓ O ρ)
    (C : Subgroup (Wit.F ≃ₐ[ℚ] Wit.F))
    (E' : Type u) [Field E'] [NumberField E']
    (ψ : E' →+* AlgebraicClosure ℚ_[ℓ])
    (S : Finset (HeightOneSpectrum (NumberField.RingOfIntegers
      (IntermediateField.fixedField C))))
    (a : HeightOneSpectrum (NumberField.RingOfIntegers
      (IntermediateField.fixedField C)) → E')
    (ha : ∀ w ∉ S, ψ (a w) =
      - Wit.ιO (((ρ.map (algebraMap ℚ (IntermediateField.fixedField C))).charFrob
        w).coeff 1)) :
    ∃ S' : Finset (HeightOneSpectrum (NumberField.RingOfIntegers
        (IntermediateField.fixedField C))),
      ∀ w, w ∉ S → w ∉ S' →
        (∀ W ∉ Wit.badF,
          Ideal.absNorm W.asIdeal = Ideal.absNorm w.asIdeal →
            (ρ.map (algebraMap ℚ Wit.F)).charFrob W ≠
              (ρ.map (algebraMap ℚ (IntermediateField.fixedField C))).charFrob w) →
        ∀ φ : E' →+* ℂ,
          ‖φ (a w)‖ ≤ 2 * Real.sqrt (Ideal.absNorm w.asIdeal) :=
  sorry

/-- **Ramanujan–Petersson for the descended Hilbert eigensystem** (the
CUSPIDALITY clause of `HeckeSystemDescendsTo`).

**PROVEN 2026-07-27 BY A SPLIT/INERT DÉVISSAGE.**  This node was a single
opaque citation ("Eichler–Shimura for parallel weight `2`, i.e. Deligne's
theorem via the Blasius/Carayol realization of a Hilbert newform of
parallel weight `2` in the `H¹` of a quaternionic Shimura variety,
together with the Weil conjectures for that variety").  It is now an
assembly of two named leaves, exactly mirroring the trace/determinant
split that `heckeSystemDescendsTo_of_prime_cyclic_step` makes further down
this module:

* `weilBound_heckeF_of_witness` — the IRREDUCIBLE classical content,
  stated at the places of `F` where the carrier's newform actually
  lives, so that it is literally Deligne's theorem and nothing else.
  This is the reusable form, and it is what the SPLIT half consumes.
* `weilBound_of_charFrob_baseChange_of_inert` — the residual citation,
  needed only at places of `L = F^C` matching NO good place of `F`.
* `forall_complexEmbedding_norm_le_of_ringHom_eq` — PROVEN here, the
  bookkeeping that reads a bound over `Wit.E` as a bound over the
  existential coefficient field `E'`, the two being related only by a
  common realization in `ℚ̄_ℓ`.

THE SPLIT HALF, PROVEN.  `ρ` is a representation of `G_ℚ`, so its
Frobenius characteristic polynomial at a place depends only on the
residue cardinality.  Hence if some `W ∉ Wit.badF` has
`NW = Nw` and the same Frobenius charpoly, then `Wit.modularF` at `W`
identifies `ιO((charFrob w).coeff 1)` with `ψℓ((heckeF W).coeff 1)`, so
`a w` and `−(heckeF W).coeff 1` are the SAME algebraic number read in
two number fields, and the bound descends with no automorphic input.
**At the base of the tower — `C = ⊥`, the only present consumer, where
`L = F^⊥` is `F` itself in another model — every place is of this kind**,
so the base case's cuspidality clause now rests on the honest classical
statement rather than on a statement about an intermediate field.

The split condition is phrased through the Frobenius charpolys rather
than through residue cardinality alone because
`charFrob_baseChange_eq_of_absNorm_eq`, which turns the latter into the
former, is declared BELOW this node and below its consumer; the charpoly
form is the strictly weaker hypothesis and needs no such reordering.

STATEMENT.  Given an eigenvalue function `a` over `L = F^C` pinned by the
Frobenius traces (`ha` says `ψ (a w) = −ιO((charFrob w).coeff 1)`, which
determines `a w` uniquely at every good `w` because `ψ` is injective on a
field), all but finitely many of its values satisfy `‖φ(a w)‖ ≤ 2√(Nw)` at
every complex embedding `φ` of the coefficient field.

WHY THIS IS THE RIGHT SHAPE.  The hypothesis `ha` already asserts that the
trace is `ψ`-rational; the residual content of this leaf is therefore
PURELY the archimedean bound, which is exactly the part of "the descended
system is CUSPIDAL automorphic" that is expressible in this module's
vocabulary.  It is genuinely discriminating rather than decorative: the
Eisenstein eigensystem, which is what a NON-cuspidal descent would
produce, has `a_w = 1 + Nw`, and `1 + Nw > 2√(Nw)` for every `Nw ≠ 1`.  So
this clause is what stops the induction from propagating an Eisenstein
system into a citation (Arthur–Clozel Ch. 3 Thm 4.2(d)) that is false for
one.

THE FINITE EXCEPTIONAL SET `S'` is genuinely needed and is not a hedge: at
the finitely many ramified places, and at the places over `ℓ` where the
cyclotomic determinant clause does not apply, the Frobenius trace is not
the Hecke eigenvalue of the newform at all.

FAITHFULNESS REPAIR 2026-07-27 — **THIS STATEMENT WAS ALSO FALSE AS
WRITTEN**, by inheritance: its two leaves were, and the same
`ρ = 1 ⊕ ε_ℓ` / `F = ℚ(√5)` / `C = ⊤` witness refutes it directly (see
the FALSITY AUDITs on `weilBound_heckeF_of_witness` and
`weilBound_of_charFrob_baseChange_of_inert`).  The residual-irreducibility
block is therefore carried here too and forwarded to both leaves.  It is
PURE PLUMBING at this node — the proof below is unchanged apart from
passing the block along — and it costs the sole consumer,
`heckeSystemDescendsTo_bot`, nothing, since that theorem already binds
`hMbar`/`hρbar`/`hirr`/`π`/`hπsurj`/`hπ` for its own use.

SOUNDNESS AUDIT.  Both routes are available.  (i) Direct: the classical
theorem, applied to the Hilbert newform whose eigensystem `a` is —
cuspidal because `hirr` makes the form upstairs cuspidal.  (ii)
Collapse: the hypothesis package (an irreducible hardly ramified mod-`ℓ`
representation with `ℓ ≥ 5`) is classically unsatisfiable — the headline
of this module — so the statement is classically true for every package.
Route (ii) is a soundness justification only, NOT an available Lean
discharge: see the ROUTE AUDIT on
`exists_baseChangeDescentData_of_prime_cyclic_step_of_inert`, whose chain shows the
headline CONSUMES this subtree, so `absurd hirr …` is circular here.

CIRCULARITY GUARD (inherited from pillar β, load-bearing): no discharge
through `Family.lean`, `Lift.lean`, or `Modularity/Interface.lean`. -/
theorem weilBound_of_charFrob_baseChange
    {ℓ : ℕ} (hℓodd : Odd ℓ) [Fact ℓ.Prime] (hℓ5 : 5 ≤ ℓ)
    {O : Type u} [CommRing O] [IsDomain O] [TopologicalSpace O]
    [IsTopologicalRing O] [Algebra ℤ_[ℓ] O] [IsLocalRing O]
    [Module.Finite ℤ_[ℓ] O] [IsModuleTopology ℤ_[ℓ] O]
    {ρ : GaloisRep ℚ O (Fin 2 → O)}
    (hrank : Module.rank O (Fin 2 → O) = 2)
    (hρ : IsHardlyRamified hℓodd hrank ρ)
    {k : Type u} [Field k] [Finite k] [Algebra ℤ_[ℓ] k]
    [TopologicalSpace k] [DiscreteTopology k]
    {Mbar : Type v} [AddCommGroup Mbar] [Module k Mbar] [Module.Finite k Mbar]
    [Module.Free k Mbar]
    (hMbar : Module.rank k Mbar = 2) {ρbar : GaloisRep ℚ k Mbar}
    (hρbar : IsHardlyRamified hℓodd hMbar ρbar)
    (hirr : ρbar.IsIrreducible)
    (π : O →+* k) (hπsurj : Function.Surjective π)
    (hπ : ∀ (q : ℕ) (hq : q.Prime), q ≠ 2 → q ≠ ℓ →
      (ρ.charFrob hq.toHeightOneSpectrumRingOfIntegersRat).map π =
        ρbar.charFrob hq.toHeightOneSpectrumRingOfIntegersRat)
    (Wit : PotentialModularityWitness ℓ O ρ)
    (C : Subgroup (Wit.F ≃ₐ[ℚ] Wit.F))
    (E' : Type u) [Field E'] [NumberField E']
    (ψ : E' →+* AlgebraicClosure ℚ_[ℓ])
    (S : Finset (HeightOneSpectrum (NumberField.RingOfIntegers
      (IntermediateField.fixedField C))))
    (a : HeightOneSpectrum (NumberField.RingOfIntegers
      (IntermediateField.fixedField C)) → E')
    (ha : ∀ w ∉ S, ψ (a w) =
      - Wit.ιO (((ρ.map (algebraMap ℚ (IntermediateField.fixedField C))).charFrob
        w).coeff 1)) :
    ∃ S' : Finset (HeightOneSpectrum (NumberField.RingOfIntegers
        (IntermediateField.fixedField C))),
      ∀ w, w ∉ S → w ∉ S' → ∀ φ : E' →+* ℂ,
        ‖φ (a w)‖ ≤ 2 * Real.sqrt (Ideal.absNorm w.asIdeal) := by
  classical
  -- the residual INERT citation supplies the places that match no good place of `F`
  obtain ⟨Sin, hSin⟩ := weilBound_of_charFrob_baseChange_of_inert hℓodd hℓ5 hrank hρ
    hMbar hρbar hirr π hπsurj hπ Wit C E' ψ S a ha
  refine ⟨Sin, fun w hwS hwin φ => ?_⟩
  by_cases hsplit : ∃ W, W ∉ Wit.badF ∧
      Ideal.absNorm W.asIdeal = Ideal.absNorm w.asIdeal ∧
      (ρ.map (algebraMap ℚ Wit.F)).charFrob W =
        (ρ.map (algebraMap ℚ (IntermediateField.fixedField C))).charFrob w
  · -- SPLIT half, PROVEN: the eigenvalue at `w` IS the newform's eigenvalue at `W`
    obtain ⟨W, hWbad, hWnorm, hWcf⟩ := hsplit
    -- Deligne's bound at the good place `W` of `F`, transported across the sign
    have hB : ∀ φ' : Wit.E →+* ℂ,
        ‖φ' (-(Wit.heckeF W).coeff 1)‖ ≤ 2 * Real.sqrt (Ideal.absNorm W.asIdeal) := by
      intro φ'
      rw [map_neg, norm_neg]
      exact weilBound_heckeF_of_witness hℓodd hℓ5 hrank hρ hMbar hρbar hirr π hπsurj hπ
        Wit W hWbad φ'
    -- the carrier's modularity clause at `W`, read at the linear coefficient
    have hcoeff : Wit.ιO
        (((ρ.map (algebraMap ℚ (IntermediateField.fixedField C))).charFrob w).coeff 1) =
          Wit.ψℓ ((Wit.heckeF W).coeff 1) := by
      have h := congrArg (fun P : Polynomial (AlgebraicClosure ℚ_[ℓ]) => P.coeff 1)
        (Wit.modularF W hWbad)
      simp only [Polynomial.coeff_map] at h
      rw [← hWcf]
      exact h
    -- so `a w` and `−(heckeF W).coeff 1` are the SAME algebraic number in `ℚ̄_ℓ`
    have hψeq : ψ (a w) = Wit.ψℓ (-(Wit.heckeF W).coeff 1) := by
      rw [ha w hwS, hcoeff, map_neg]
    have hbound :=
      forall_complexEmbedding_norm_le_of_ringHom_eq Wit.ψℓ ψ hψeq hB φ
    rwa [hWnorm] at hbound
  · -- INERT half: the residual citation
    refine hSin w hwS hwin (fun W hWbad hWnorm hWcf => ?_) φ
    exact hsplit ⟨W, hWbad, hWnorm, hWcf⟩

/-- **The base of the descent chain — the witness's own eigensystem,
read over `F^⊥`** (PROVEN 2026-07-25; a pure TRANSPORT node, no
arithmetic content): the carrier's modularity clause `Wit.modularF` is a statement
about the number field `F`; the descent chain starts at the fixed field
of the trivial subgroup, `F^⊥`, which is `⊤ ≤ F` — the same field in a
different model. This leaf transports the clause across that model
change.

Classically (and formally, in principle): `IntermediateField.fixedField
⊥ = ⊤` (mathlib: `IntermediateField.fixedField_bot`) and
`IntermediateField.topEquiv : (⊤ : IntermediateField ℚ F) ≃ₐ[ℚ] F`, so
the two fields are ℚ-isomorphic number fields. A ℚ-isomorphism of
number fields carries height-one primes to height-one primes
bijectively, carries the arithmetic Frobenius conjugacy class at a
place to the class at its image, and `charFrob` is a characteristic
polynomial — invariant under conjugation. Hence `S := badF` and
`P := heckeF`, both transported along that bijection, witness the
conclusion.

WHY IT WAS A LEAF (2026-07-24): the transport is not formally free on
this pin. `GaloisRep.map` is defined through
`Field.absoluteGaloisGroup.map`, which "relies on an arbitrarily chosen
embedding of the algebraic closures" (`GaloisRep.lean`), and `charFrob`
is evaluated at `Field.AbsoluteGaloisGroup.adicArithFrob`, itself
defined through an arbitrary choice of a valuation on the algebraic
closure extending `v`. Independence of `charFrob` from those choices
(equivalently: its invariance under the conjugation relating two
choices) was exactly the missing API — `GaloisRep.charFrob` had no
transport lemma along an `AlgEquiv` of number fields anywhere in the
project or in the pin.

DISCHARGED (2026-07-25) BY THAT API, now written as the reusable module
`Deformations/RepresentationTheory/GaloisRepTransport.lean`:

* `Field.absoluteGaloisGroup.exists_conj_map_comp` (PROVEN there) —
  `Γ` is functorial up to conjugation by a SINGLE element: the two
  composite embeddings `Kᵃˡᵍ → Fᵃˡᵍ` of a tower differ by an
  automorphism of `Kᵃˡᵍ` (both are isomorphisms, since `Fᵃˡᵍ` is
  algebraic over `K`);
* `GaloisRep.charFrob_map_comp` (PROVEN there) — hence `charFrob` IS
  functorial along a tower, the conjugation being invisible to
  characteristic polynomials (`LinearEquiv.charpoly_conj`);
* `GaloisRep.charFrob_map_algEquiv` (PROVEN there) — the transport along
  a `K`-isomorphism of number fields, at every place where the
  restriction is unramified, over the arithmetic leaf
  `GaloisRep.charFrob_map_ringEquiv`;
* `GaloisRep.exists_finset_isUnramifiedAt_map` (leaf there) — the
  ramification bookkeeping: almost-everywhere unramifiedness is
  inherited by the restriction, which enlarges the bad set by finitely
  many places.

The residual depth therefore lives in those two general-purpose leaves
of `GaloisRepTransport.lean` (the completion-functoriality/Frobenius
comparison and the inertia inheritance), not in this node: HERE the
argument is complete — `IntermediateField.fixedField_bot` and
`IntermediateField.topEquiv` produce `e : F^⊥ ≃ₐ[ℚ] F`, the hardly
ramified hypothesis feeds the unramifiedness bookkeeping, and `S`, `P`
are `Wit.badF`, `Wit.heckeF` transported along the induced bijection of
places.

SOUNDNESS AUDIT (both ways, 2026-07-24): (i) direct — the statement is
`Wit.modularF` read through a ℚ-isomorphism of number fields, true for
EVERY carrier (no hypothesis beyond the carrier itself is used), and
(ii) collapse — the hypothesis package is classically unsatisfiable
(headline below), so the statement is classically true for every
package.

ROUTE AUDIT (2026-07-24): discharge by vacuity — `absurd hirr
(not_isIrreducible_of_isHardlyRamified_of_five_le …)`, the route the
interface leaves of `Modularity/Interface.lean` take — is NOT available
here: the headline consumes this node (headline ←
`exists_threeadic_compatible_member_of_five_le` ←
`exists_heckeField_system_of_witness` ←
`exists_descended_heckeSystem_of_solvable` ← this leaf), so the
vacuity route would be circular. The classical route above is the one
to follow.

CIRCULARITY GUARD (inherited from pillar β, load-bearing): no
discharge through `Family.lean`, `Lift.lean`, or
`Modularity/Interface.lean`. -/

theorem heckeSystemDescendsTo_bot
    {ℓ : ℕ} (hℓodd : Odd ℓ) [Fact ℓ.Prime] (hℓ5 : 5 ≤ ℓ)
    {O : Type u} [CommRing O] [IsDomain O] [TopologicalSpace O]
    [IsTopologicalRing O] [Algebra ℤ_[ℓ] O] [IsLocalRing O]
    [Module.Finite ℤ_[ℓ] O] [IsModuleTopology ℤ_[ℓ] O]
    (hZinj : Function.Injective (algebraMap ℤ_[ℓ] O))
    {ρ : GaloisRep ℚ O (Fin 2 → O)}
    (hrank : Module.rank O (Fin 2 → O) = 2)
    (hρ : IsHardlyRamified hℓodd hrank ρ)
    {k : Type u} [Field k] [Finite k] [Algebra ℤ_[ℓ] k]
    [TopologicalSpace k] [DiscreteTopology k]
    {W : Type v} [AddCommGroup W] [Module k W] [Module.Finite k W]
    [Module.Free k W]
    (hW : Module.rank k W = 2) {ρbar : GaloisRep ℚ k W}
    (hρbar : IsHardlyRamified hℓodd hW ρbar)
    (hirr : ρbar.IsIrreducible)
    (π : O →+* k) (hπsurj : Function.Surjective π)
    (hπ : ∀ (q : ℕ) (hq : q.Prime), q ≠ 2 → q ≠ ℓ →
      (ρ.charFrob hq.toHeightOneSpectrumRingOfIntegersRat).map π =
        ρbar.charFrob hq.toHeightOneSpectrumRingOfIntegersRat)
    (Wit : PotentialModularityWitness ℓ O ρ) :
    HeckeSystemDescendsTo Wit ⊥ := by
  classical
  -- (i) MODEL CHANGE: the base of the descent chain is the fixed field of the
  -- trivial subgroup, `F^⊥ = ⊤ ≤ F` (`IntermediateField.fixedField_bot`),
  -- which is `ℚ`-isomorphic to `F` itself (`IntermediateField.topEquiv`).
  have e : (IntermediateField.fixedField (⊥ : Subgroup (Wit.F ≃ₐ[ℚ] Wit.F)))
      ≃ₐ[ℚ] Wit.F :=
    (IntermediateField.equivOfEq IntermediateField.fixedField_bot).trans
      IntermediateField.topEquiv
  -- (ii) RAMIFICATION BOOKKEEPING: `ρ` is unramified away from the places of
  -- `2` and `ℓ` (hardly ramified), hence its restriction to `F^⊥` is
  -- unramified away from a finite set of places `T` — which is what makes the
  -- Frobenius characteristic polynomials transportable at all but finitely
  -- many places.
  have hS : ∀ v ∉ ({Nat.prime_two.toHeightOneSpectrumRingOfIntegersRat,
      (Fact.out : ℓ.Prime).toHeightOneSpectrumRingOfIntegersRat} :
        Finset (HeightOneSpectrum (NumberField.RingOfIntegers ℚ))),
      ρ.IsUnramifiedAt v := by
    intro v hv
    obtain ⟨p, hp, rfl⟩ :=
      IsHardlyRamified.exists_prime_eq_toHeightOneSpectrumRingOfIntegersRat v
    refine hρ.isUnramified p hp ⟨?_, ?_⟩
    · rintro rfl
      exact hv (Finset.mem_insert_self _ _)
    · rintro rfl
      exact hv (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
  obtain ⟨T, hT⟩ := GaloisRep.exists_finset_isUnramifiedAt_map
    (L := IntermediateField.fixedField (⊥ : Subgroup (Wit.F ≃ₐ[ℚ] Wit.F))) ρ _ hS
  -- the places over `ℓ`, where the cyclotomic determinant clause does not apply
  obtain ⟨Sl, hSl⟩ := exists_finset_forall_natCast_notMem_asIdeal
    (IntermediateField.fixedField (⊥ : Subgroup (Wit.F ≃ₐ[ℚ] Wit.F))) ℓ
    (Fact.out : ℓ.Prime).ne_zero
  -- (iii) THE COEFFICIENT FIELD at the base of the tower is the carrier's own
  -- Hecke field: nothing has been descended yet, so no growth has occurred.
  refine ⟨Wit.E, inferInstance, inferInstance, Wit.ψℓ, RingHom.id _,
    fun x => rfl, ?_⟩
  -- (iv) TRANSPORT: read the carrier's modularity clause `Wit.modularF`
  -- through `e`, using `GaloisRep.charFrob_map_algEquiv`; the bad set is the
  -- carrier's bad set pulled back along the induced bijection of places,
  -- enlarged by the ramified places `T` and the places over `ℓ`.
  set φ := NumberField.finitePlaceEquiv e.toRingEquiv with hφ
  set a : HeightOneSpectrum (NumberField.RingOfIntegers
      (IntermediateField.fixedField (⊥ : Subgroup (Wit.F ≃ₐ[ℚ] Wit.F)))) → Wit.E :=
    fun w => -(Wit.heckeF (φ w)).coeff 1 with hadef
  set S₀ := (Wit.badF.image φ.symm ∪ T) ∪ Sl with hS₀def
  have hmatch : ∀ w ∉ S₀,
      ((ρ.map (algebraMap ℚ (IntermediateField.fixedField
          (⊥ : Subgroup (Wit.F ≃ₐ[ℚ] Wit.F))))).charFrob w).map Wit.ιO =
        (Wit.heckeF (φ w)).map Wit.ψℓ := by
    intro w hw
    rw [hS₀def, Finset.mem_union, not_or, Finset.mem_union, not_or] at hw
    obtain ⟨⟨hbad, hTw⟩, _⟩ := hw
    have hbad' : φ w ∉ Wit.badF := by
      intro hmem
      exact hbad (by simpa [hφ] using Finset.mem_image_of_mem φ.symm hmem)
    rw [← GaloisRep.charFrob_map_algEquiv ρ e w (hT w hTw)]
    exact Wit.modularF _ hbad'
  -- the coefficient identity that drives all three clauses
  have ha : ∀ w ∉ S₀, Wit.ψℓ (a w) =
      - Wit.ιO (((ρ.map (algebraMap ℚ (IntermediateField.fixedField
        (⊥ : Subgroup (Wit.F ≃ₐ[ℚ] Wit.F))))).charFrob w).coeff 1) := by
    intro w hw
    have h1 := congrArg (fun P : Polynomial (AlgebraicClosure ℚ_[ℓ]) => P.coeff 1)
      (hmatch w hw)
    simp only [Polynomial.coeff_map] at h1
    rw [hadef]
    simp [h1]
  -- (v) CUSPIDALITY, from the Ramanujan citation
  obtain ⟨S', hS'⟩ := weilBound_of_charFrob_baseChange (ℓ := ℓ) hℓodd hℓ5 hrank hρ
    hW hρbar hirr π hπsurj hπ Wit
    (⊥ : Subgroup (Wit.F ≃ₐ[ℚ] Wit.F)) Wit.E Wit.ψℓ S₀ a ha
  have hfin : Module.finrank O (Fin 2 → O) = 2 :=
    Module.finrank_eq_of_rank_eq hrank
  refine ⟨S₀ ∪ S', a, ?_, ?_, ?_⟩
  · -- (1) the eigensystem, in Hilbert-newform shape
    intro w hw
    rw [Finset.mem_union, not_or] at hw
    have hmonic :
        ((ρ.map (algebraMap ℚ (IntermediateField.fixedField
          (⊥ : Subgroup (Wit.F ≃ₐ[ℚ] Wit.F))))).charFrob w).Monic := by
      rw [GaloisRep.charFrob_eq_charpoly_globalFrob]
      exact LinearMap.charpoly_monic _
    have hdeg :
        ((ρ.map (algebraMap ℚ (IntermediateField.fixedField
          (⊥ : Subgroup (Wit.F ≃ₐ[ℚ] Wit.F))))).charFrob w).natDegree = 2 := by
      rw [GaloisRep.charFrob_eq_charpoly_globalFrob, LinearMap.charpoly_natDegree, hfin]
    have hwl : (ℓ : NumberField.RingOfIntegers (IntermediateField.fixedField
        (⊥ : Subgroup (Wit.F ≃ₐ[ℚ] Wit.F)))) ∉ w.asIdeal := by
      refine hSl w ?_
      intro hmem
      exact hw.1 (by rw [hS₀def]; exact Finset.mem_union_right _ hmem)
    have hdet := charFrob_baseChange_coeff_zero_eq_absNorm hℓodd hrank hρ
      (IntermediateField.fixedField (⊥ : Subgroup (Wit.F ≃ₐ[ℚ] Wit.F))) w hwl
    refine Polynomial.ext fun n => ?_
    rw [Polynomial.coeff_map, Polynomial.coeff_map]
    match n with
    | 0 =>
      rw [hdet]
      simp
    | 1 =>
      have hc : (Polynomial.X ^ 2 - Polynomial.C (a w) * Polynomial.X +
          Polynomial.C ((Ideal.absNorm w.asIdeal : ℕ) : Wit.E)).coeff 1 = -(a w) := by
        simp
      rw [hc, map_neg, ha w hw.1]
      ring
    | 2 =>
      have h2 : ((ρ.map (algebraMap ℚ (IntermediateField.fixedField
          (⊥ : Subgroup (Wit.F ≃ₐ[ℚ] Wit.F))))).charFrob w).coeff 2 = 1 := by
        have h := hmonic.coeff_natDegree
        rwa [hdeg] at h
      rw [h2]
      simp
    | (m + 3) =>
      rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [hdeg]; omega)]
      simp [Polynomial.coeff_X_pow]
  · -- (2) CUSPIDALITY: the Ramanujan–Petersson bound
    intro w hw
    rw [Finset.mem_union, not_or] at hw
    exact hS' w hw.1 hw.2
  · -- (3) Gal-INVARIANCE: `charFrob` is invariant under a `ℚ`-automorphism of
    -- the base, and `ψℓ` is injective, so the eigenvalue function inherits it
    intro τ w hw hτw
    rw [Finset.mem_union, not_or] at hw
    rw [Finset.mem_union, not_or] at hτw
    have hTw : w ∉ T := by
      intro hmem
      exact hw.1 (by rw [hS₀def]; exact
        Finset.mem_union_left _ (Finset.mem_union_right _ hmem))
    have hcf := GaloisRep.charFrob_map_algEquiv ρ τ w (hT w hTw)
    refine Wit.ψℓ.injective ?_
    rw [ha _ hτw.1, ha _ hw.1, hcf]

/-- **Refining a cyclic quotient by one prime step** (PROVEN; pure finite
group theory, no citation): if `C ≤ D` with `C` normal in `D` and the
quotient `D/C` CYCLIC, and `C ≠ D`, then there is an intermediate
subgroup `C ≤ E ≤ D`, of strictly smaller order than `D`, such that

* `C` is normal in `E` with `E/C` again CYCLIC, and
* `E` is normal in `D` with `D/E` of PRIME order `p`.

This is the dévissage that reduces base change along an arbitrary cyclic
extension to base change along a PRIME-degree cyclic extension — the
shape in which the theorem of Langlands (*Base Change for GL(2)*, Ann.
of Math. Studies 96 (1980), Ch. 2) and Arthur–Clozel (*Simple Algebras,
Base Change, and the Advanced Theory of the Trace Formula*, Ann. of
Math. Studies 120 (1989), Ch. 3) is actually proved: the twisted trace
formula is run for a cyclic extension of PRIME degree, and the general
cyclic (a fortiori solvable) case is obtained by composing prime steps.
Iterating this lemma turns the general cyclic step into finitely many
prime steps, i.e. it is to
`heckeSystemDescendsTo_of_prime_cyclic_step` what
`exists_cyclicRefinement_of_isSolvable` is to the cyclic step.

Proof (formal): write `Q = D/C`, a finite cyclic group of order `n`, and
`n ≠ 1` because `C ≠ D`. Choose a prime `p ∣ n` and a generator `g` of
`Q`, and put `K = ⟨g^p⟩ ≤ Q`; then `#K = n/p`, so `K` has index `p`.
Take `E` to be the preimage of `K` in `D`, pushed into the ambient
group. Normality is automatic on both steps — `Q` is abelian (cyclic),
so `K` is normal, and each of `C.subgroupOf E`, `E.subgroupOf D` is
exhibited as the kernel of a homomorphism. `E/C` injects into `Q`
(it is the quotient of `E` by the kernel of `E → Q`), hence is cyclic as
a subgroup of a cyclic group, while `D/E` is the kernel-quotient of the
surjection `D → Q/K`, of order `#Q/K = p`. Finally `#E · p = #D`, which
gives the strict decrease of the order used as the induction measure. -/
theorem exists_intermediate_of_isCyclic_quotient {G : Type*} [Group G]
    [Finite G] (C D : Subgroup G) (hCD : C ≤ D)
    (hnormal : (C.subgroupOf D).Normal)
    (hcyclic : IsCyclic (D ⧸ C.subgroupOf D)) (hne : C ≠ D) :
    ∃ (E : Subgroup G) (p : ℕ), p.Prime ∧ C ≤ E ∧ E ≤ D ∧
      Nat.card E < Nat.card D ∧
      (∃ _ : (C.subgroupOf E).Normal, IsCyclic (E ⧸ C.subgroupOf E)) ∧
      (∃ _ : (E.subgroupOf D).Normal,
        Nat.card (D ⧸ E.subgroupOf D) = p) := by
  classical
  -- the cyclic quotient `Q = D/C` is nontrivial, since `C ≠ D`
  have hn1 : Nat.card (D ⧸ C.subgroupOf D) ≠ 1 := by
    intro h
    have hDC : D ≤ C :=
      Subgroup.subgroupOf_eq_top.mp
        (Subgroup.index_eq_one.mp ((Subgroup.index_eq_card _).trans h))
    exact hne (le_antisymm hCD hDC)
  obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd hn1
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := D ⧸ C.subgroupOf D)
  have hord : orderOf g = Nat.card (D ⧸ C.subgroupOf D) :=
    orderOf_eq_card_of_forall_mem_zpowers hg
  have hpord : p ∣ orderOf g := by rw [hord]; exact hpdvd
  -- `K = ⟨g ^ p⟩`, of order `n / p` and hence of index `p`
  set K : Subgroup (D ⧸ C.subgroupOf D) := Subgroup.zpowers (g ^ p)
    with hKdef
  have hKcard : Nat.card K = Nat.card (D ⧸ C.subgroupOf D) / p := by
    rw [hKdef, Nat.card_zpowers, orderOf_pow_of_dvd hp.ne_zero hpord, hord]
  have hKindex : K.index = p := by
    have hcardpos : 0 < Nat.card (D ⧸ C.subgroupOf D) := Nat.card_pos
    have hcard : Nat.card K * K.index = Nat.card (D ⧸ C.subgroupOf D) :=
      Subgroup.card_mul_index K
    obtain ⟨m, hm⟩ := hpdvd
    have hm0 : 0 < m := by
      rcases Nat.eq_zero_or_pos m with rfl | hpos
      · rw [hm] at hcardpos; simp at hcardpos
      · exact hpos
    rw [hKcard, hm, Nat.mul_div_cancel_left m hp.pos] at hcard
    exact Nat.eq_of_mul_eq_mul_left hm0 (by rw [hcard, Nat.mul_comm])
  -- `E`: the preimage of `K` in `D`, viewed as a subgroup of `G`
  set q : D →* D ⧸ C.subgroupOf D := QuotientGroup.mk' (C.subgroupOf D)
    with hqdef
  have hqsurj : Function.Surjective q := by
    rw [hqdef]; exact QuotientGroup.mk'_surjective _
  obtain ⟨E, hEdef⟩ :
      ∃ E : Subgroup G, E = (K.comap q).map D.subtype := ⟨_, rfl⟩
  have hED : E ≤ D := by rw [hEdef]; exact Subgroup.map_subtype_le _
  have hEsub : E.subgroupOf D = K.comap q := by
    rw [← Subgroup.comap_subtype, hEdef,
      Subgroup.comap_map_eq_self_of_injective D.subtype_injective]
  have hCE : C ≤ E := by
    intro c hc
    rw [hEdef]
    refine Subgroup.mem_map.mpr ⟨⟨c, hCD hc⟩, ?_, rfl⟩
    have hq1 : q ⟨c, hCD hc⟩ = 1 := by
      rw [hqdef, QuotientGroup.mk'_apply]
      exact (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_subgroupOf.mpr hc)
    rw [Subgroup.mem_comap, hq1]
    exact one_mem K
  -- the top step `E ≤ D`: normal of prime index `p`
  haveI hEDnormal : (E.subgroupOf D).Normal := by
    rw [hEsub]; exact (inferInstance : K.Normal).comap q
  have hEDindex : (E.subgroupOf D).index = p := by
    rw [hEsub, K.index_comap_of_surjective hqsurj, hKindex]
  -- the bottom step `C ≤ E`: the kernel of `E → Q`, with cyclic quotient
  have hkerf : (q.comp (Subgroup.inclusion hED)).ker = C.subgroupOf E := by
    rw [← MonoidHom.comap_ker, hqdef, QuotientGroup.ker_mk',
      Subgroup.comap_inclusion_subgroupOf]
  haveI hCEnormal : (C.subgroupOf E).Normal := by
    rw [← hkerf]; exact MonoidHom.normal_ker _
  have hcycE : IsCyclic (E ⧸ C.subgroupOf E) := by
    have hlift : ∀ x ∈ C.subgroupOf E,
        (q.comp (Subgroup.inclusion hED)) x = 1 := fun x hx =>
      MonoidHom.mem_ker.mp (by rw [hkerf]; exact hx)
    refine isCyclic_of_injective
      (QuotientGroup.lift (C.subgroupOf E) _ hlift) ?_
    intro a b
    refine Quotient.inductionOn₂' a b ?_
    intro x y h
    have h' : (q.comp (Subgroup.inclusion hED)) x
        = (q.comp (Subgroup.inclusion hED)) y := h
    refine Quotient.sound' ?_
    rw [QuotientGroup.leftRel_apply, ← hkerf, MonoidHom.mem_ker, map_mul,
      map_inv, h']
    simp
  -- the induction measure: `#E · p = #D`
  have hlt : Nat.card E < Nat.card D := by
    have h1 : Nat.card (E.subgroupOf D) * (E.subgroupOf D).index
        = Nat.card D := Subgroup.card_mul_index _
    have h2 : Nat.card (E.subgroupOf D) = Nat.card E :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hED).toEquiv
    rw [h2, hEDindex] at h1
    have h3 : 0 < Nat.card E := Nat.card_pos
    calc Nat.card E < Nat.card E * 2 := by omega
      _ ≤ Nat.card E * p := Nat.mul_le_mul le_rfl hp.two_le
      _ = Nat.card D := h1
  exact ⟨E, p, hp, hCE, hED, hlt, ⟨hCEnormal, hcycE⟩,
    ⟨hEDnormal, by rw [← Subgroup.index_eq_card]; exact hEDindex⟩⟩

/-! ### Helpers for `charFrob_baseChange_eq_of_absNorm_eq`

The three arithmetic helpers below (and the linear-algebra one) are what
makes the residue-cardinality leaf go through, and they are stated for a
general base number field `Kb` deliberately: at the CONCRETE base `ℚ` the
elaborator resolves `Algebra ℚ (P.adicCompletion ℚ)` to
`DivisionRing.toRatAlgebra` and `CommSemiring ℚ` to `Rat.commSemiring`,
while `GaloisRep.toLocal` — being stated for a variable base field —
carries `HeightOneSpectrum.instAlgebraAdicCompletion` and
`Semifield.toCommSemiring`. Those instances are propositionally but NOT
definitionally equal, so a hand-written `algebraMap ℚ (P.adicCompletion ℚ)`
can never be `rw`- or `exact`-matched against `toLocal_apply`'s. Keeping
the base field a VARIABLE removes the ℚ-specific instance path and the two
spellings coincide on the nose. (Learned expensively, 2026-07-26: the
symptom is a `rewrite failed` / `isDefEq` timeout on two terms that
pretty-print identically.) -/

open scoped NumberField in
/-- **The residue characteristic of a finite place** (PROVEN helper): every
finite place `w` of a number field `K` lies over the place of a unique
rational prime `q`, and its absolute norm is a positive power of `q`.

The prime is `natGenerator` of `w.under (𝓞 ℚ)`, identified with a rational
prime by the proven classification
`IsHardlyRamified.exists_prime_eq_toHeightOneSpectrumRingOfIntegersRat`;
the norm formula is mathlib's `Ideal.absNorm_eq_pow_inertiaDeg'`, whose
`LiesOver (span {(q : ℤ)})` instance is supplied by maximality of `(q)` in
`ℤ`. The exponent is nonzero because `absNorm I = 1 ↔ I = ⊤`. -/
theorem exists_prime_place_rat (K : Type u) [Field K] [NumberField K]
    (w : HeightOneSpectrum (𝓞 K)) :
    ∃ (q e : ℕ) (hq : q.Prime), 0 < e ∧
      Ideal.comap (algebraMap (𝓞 ℚ) (𝓞 K)) w.asIdeal =
        hq.toHeightOneSpectrumRingOfIntegersRat.asIdeal ∧
      Ideal.absNorm w.asIdeal = q ^ e := by
  classical
  -- the place below `w` is the place of a prime number `q`
  obtain ⟨q, hq, hpq⟩ : ∃ (q : ℕ) (hq : q.Prime),
      w.under (𝓞 ℚ) = hq.toHeightOneSpectrumRingOfIntegersRat :=
    IsHardlyRamified.exists_prime_eq_toHeightOneSpectrumRingOfIntegersRat (w.under (𝓞 ℚ))
  have hcomap : Ideal.comap (algebraMap (𝓞 ℚ) (𝓞 K)) w.asIdeal =
      hq.toHeightOneSpectrumRingOfIntegersRat.asIdeal := by
    rw [← hpq]
    rfl
  -- `q` lies in `w`
  have hqw : (q : 𝓞 K) ∈ w.asIdeal := by
    have h1 : (q : 𝓞 ℚ) ∈ hq.toHeightOneSpectrumRingOfIntegersRat.asIdeal := by
      rw [asIdeal_toHeightOneSpectrumRingOfIntegersRat]
      exact Ideal.mem_span_singleton_self _
    rw [← hcomap, Ideal.mem_comap] at h1
    rwa [map_natCast] at h1
  -- hence `w` lies over `(q)` in `ℤ`
  have hle : Ideal.span {(q : ℤ)} ≤ w.asIdeal.under ℤ := by
    rw [Ideal.span_le, Set.singleton_subset_iff]
    show ((q : ℤ)) ∈ Ideal.comap (algebraMap ℤ (𝓞 K)) w.asIdeal
    rw [Ideal.mem_comap, map_natCast]
    exact hqw
  have hmax : (Ideal.span {(q : ℤ)}).IsMaximal :=
    Ideal.IsPrime.isMaximal hq.toHeightOneSpectrumInt.isPrime
      hq.toHeightOneSpectrumInt.ne_bot
  have hunderZ : Ideal.span {(q : ℤ)} = w.asIdeal.under ℤ :=
    hmax.eq_of_le (Ideal.IsPrime.under ℤ w.asIdeal).ne_top hle
  haveI : w.asIdeal.LiesOver (Ideal.span {(q : ℤ)}) := ⟨hunderZ⟩
  have hnorm : Ideal.absNorm w.asIdeal =
      q ^ ((Ideal.span {(q : ℤ)}).inertiaDeg' w.asIdeal) :=
    Ideal.absNorm_eq_pow_inertiaDeg' w.asIdeal hq
  refine ⟨q, (Ideal.span {(q : ℤ)}).inertiaDeg' w.asIdeal, hq, ?_, hcomap, hnorm⟩
  rcases Nat.eq_zero_or_pos ((Ideal.span {(q : ℤ)}).inertiaDeg' w.asIdeal) with h0 | h
  · exfalso
    rw [h0, pow_zero] at hnorm
    exact w.isPrime.ne_top (Ideal.absNorm_eq_one_iff.mp hnorm)
  · exact h


open scoped NumberField in
/-- **The global Frobenius at `w` is a conjugate of a local one at the place
below** (PROVEN helper; the arithmetic core): if the ideal of the place `P`
of the base `Kb` is the contraction of the ideal of `w`, then the image in
`Γ Kb` of the arithmetic Frobenius at `w` — pushed down `Γ K_w → Γ K → Γ Kb`
— is conjugate in `Γ Kb` to the image of an element `X ∈ Γ (Kb)_P` which
raises the residue field to the `Nw`-th power.

Both halves come from `CompletionTransport.lean`: the completion map
`(Kb)_P →+* K_w` exists and is LOCAL because `P` pulls back from `w`
(`valuation_map_le_of_le_one`, `adicCompletionMap_mem_integers`), it carries
the Frobenius congruence downstairs (`icMap_smul` +
`mem_maximalIdeal_of_icMap`, the reflection principle), and the two
factorisations of `Kb → K_w` differ by a single conjugation
(`exists_conj_map_comp'`). The exponent is `Nw` rather than `NP`: this is
the ONLY difference from `Field.absoluteGaloisGroup.isArithFrobAt_map`,
which demands equal residue cardinalities — here the residue degree is
absorbed into the exponent, which is exactly what makes the leaf work at
places of arbitrary residue degree. -/
theorem exists_conj_map_adicArithFrob_base {Kb : Type*} [Field Kb] [NumberField Kb]
    (P : HeightOneSpectrum (𝓞 Kb)) (K : Type*) [Field K] [NumberField K] [Algebra Kb K]
    (w : HeightOneSpectrum (𝓞 K))
    (hcomap : Ideal.comap (algebraMap (𝓞 Kb) (𝓞 K)) w.asIdeal = P.asIdeal) :
    ∃ (μ : Field.absoluteGaloisGroup Kb)
      (X : Field.absoluteGaloisGroup (P.adicCompletion Kb)),
      (∀ z : IntegralClosure ↥(P.adicCompletionIntegers Kb)
          (AlgebraicClosure (P.adicCompletion Kb)),
        X • z - z ^ (Ideal.absNorm w.asIdeal) ∈
          IsLocalRing.maximalIdeal (IntegralClosure ↥(P.adicCompletionIntegers Kb)
            (AlgebraicClosure (P.adicCompletion Kb)))) ∧
      Field.absoluteGaloisGroup.map (algebraMap Kb K)
          (Field.absoluteGaloisGroup.map (algebraMap K (w.adicCompletion K))
            (Field.AbsoluteGaloisGroup.adicArithFrob w)) =
        μ * Field.absoluteGaloisGroup.map
          (algebraMap Kb (P.adicCompletion Kb)) X * μ⁻¹ := by
  classical
  have hmem : P.asIdeal ≤ Ideal.comap (algebraMap (𝓞 Kb) (𝓞 K)) w.asIdeal :=
    le_of_eq hcomap.symm
  have hcompl : ∀ s : 𝓞 Kb, s ∉ P.asIdeal →
      algebraMap (𝓞 Kb) (𝓞 K) s ∉ w.asIdeal := by
    intro s hs h
    exact hs (hcomap ▸ (Ideal.mem_comap.mpr h))
  have hcomm : ∀ a : 𝓞 Kb,
      (algebraMap Kb K) (algebraMap (𝓞 Kb) Kb a)
        = algebraMap (𝓞 K) K (algebraMap (𝓞 Kb) (𝓞 K) a) := by
    intro a
    rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
  have hψ : UniformContinuous
      (WithVal.map (P.valuation Kb) (w.valuation K) (algebraMap Kb K)) :=
    WithVal.uniformContinuous_map_of_le _ _
      (IsDedekindDomain.HeightOneSpectrum.valuation_surjective Kb P) _
      (fun x hx => IsDedekindDomain.HeightOneSpectrum.valuation_map_le_of_le_one P w _ _
        hcomm hmem hcompl x hx)
  have hint : ∀ x ∈ P.adicCompletionIntegers Kb,
      IsDedekindDomain.HeightOneSpectrum.adicCompletionMap P w (algebraMap Kb K) hψ x
        ∈ w.adicCompletionIntegers K :=
    fun x hx => IsDedekindDomain.HeightOneSpectrum.adicCompletionMap_mem_integers P w _ hψ
      _ hcomm hx
  -- the residue cardinality upstairs is `Nw`
  have hcard : Nat.card (↥(w.adicCompletionIntegers K) ⧸
      (IsLocalRing.maximalIdeal (IntegralClosure ↥(w.adicCompletionIntegers K)
        (AlgebraicClosure (w.adicCompletion K)))).under ↥(w.adicCompletionIntegers K)) =
      Ideal.absNorm w.asIdeal := by
    rw [IsDedekindDomain.HeightOneSpectrum.natCard_under_maximalIdeal w,
      Ideal.absNorm_apply, Submodule.cardQuot_apply]
  -- the two factorisations of `Kb → K_w`
  obtain ⟨τ, hτ⟩ := Field.absoluteGaloisGroup.exists_conj_map_comp'
    (algebraMap Kb (P.adicCompletion Kb))
    (IsDedekindDomain.HeightOneSpectrum.adicCompletionMap P w (algebraMap Kb K) hψ)
    ((algebraMap K (w.adicCompletion K)).comp (algebraMap Kb K))
    (RingHom.ext fun x => by
      simpa using
        IsDedekindDomain.HeightOneSpectrum.adicCompletionMap_coe P w (algebraMap Kb K) hψ x)
  obtain ⟨τ₀, hτ₀⟩ := Field.absoluteGaloisGroup.exists_conj_map_comp'
    (algebraMap Kb K) (algebraMap K (w.adicCompletion K))
    ((algebraMap K (w.adicCompletion K)).comp (algebraMap Kb K)) rfl
  refine ⟨τ₀⁻¹ * τ,
    Field.absoluteGaloisGroup.map
      (IsDedekindDomain.HeightOneSpectrum.adicCompletionMap P w (algebraMap Kb K) hψ)
      (Field.AbsoluteGaloisGroup.adicArithFrob w), ?_, ?_⟩
  · intro z
    refine Field.absoluteGaloisGroup.mem_maximalIdeal_of_icMap P w _ hint ?_
    rw [map_sub, map_pow, Field.absoluteGaloisGroup.icMap_smul, ← hcard]
    exact Field.AbsoluteGaloisGroup.isArithFrobAt_adicArithFrob w
      (Field.absoluteGaloisGroup.icMap P w _ hint z)
  · have heq := (hτ₀ (Field.AbsoluteGaloisGroup.adicArithFrob w)).symm.trans
      (hτ (Field.AbsoluteGaloisGroup.adicArithFrob w))
    have hstep : Field.absoluteGaloisGroup.map (algebraMap Kb K)
        (Field.absoluteGaloisGroup.map (algebraMap K (w.adicCompletion K))
          (Field.AbsoluteGaloisGroup.adicArithFrob w))
        = τ₀⁻¹ * (τ * Field.absoluteGaloisGroup.map
            (algebraMap Kb (P.adicCompletion Kb))
            (Field.absoluteGaloisGroup.map
              (IsDedekindDomain.HeightOneSpectrum.adicCompletionMap P w (algebraMap Kb K) hψ)
              (Field.AbsoluteGaloisGroup.adicArithFrob w)) * τ⁻¹) * τ₀ := by
      rw [← heq]; group
    rw [hstep]; group

/-- **A unit of `End` conjugates through `LinearEquiv.conj`** (PROVEN
helper): two mutually inverse endomorphisms assemble into a linear
automorphism whose `LinearEquiv.conj` is left/right multiplication by
them. Stated for an abstract module on purpose — see the section note. -/
theorem exists_linearEquiv_conj_eq {R : Type*} [CommRing R] {N : Type*} [AddCommGroup N]
    [Module R N] (f g : Module.End R N) (h1 : f * g = 1) (h2 : g * f = 1) :
    ∃ u : N ≃ₗ[R] N, ∀ X : Module.End R N, u.conj X = f * X * g := by
  refine ⟨LinearEquiv.ofLinear f g
    (LinearMap.ext fun m => congrFun (congrArg (fun t : Module.End R N => ⇑t) h1) m)
    (LinearMap.ext fun m => congrFun (congrArg (fun t : Module.End R N => ⇑t) h2) m),
    fun X => ?_⟩
  refine LinearMap.ext fun m => ?_
  simp only [LinearEquiv.conj_apply, LinearMap.coe_comp, Function.comp_apply,
    LinearEquiv.coe_coe, LinearEquiv.ofLinear_apply,
    LinearEquiv.ofLinear_symm_apply, Module.End.mul_apply]

open scoped NumberField in
/-- **`charFrob` sees the global Frobenius only up to conjugacy and inertia**
(PROVEN helper): if the global Frobenii at `w` (of `Mf`) and at `v` (of `Lf`)
are, after pushing to `Γ Kb`, conjugates of two elements `XM`, `XL` of the
local group at ONE place `P` of `Kb` which differ by an element of
`localInertiaGroup P`, and `ρ` is unramified at `P`, then the two Frobenius
characteristic polynomials agree.

`ρ` kills the inertia discrepancy (`IsUnramifiedAt.localInertiaGroup_le`),
so the two `ρ`-images are conjugate by `ρ (μL μM⁻¹)`, and characteristic
polynomials do not see conjugation (`LinearEquiv.charpoly_conj`). -/
theorem charFrob_eq_of_conj_of_inertia {Kb : Type*} [Field Kb] [NumberField Kb]
    {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    {N : Type*} [AddCommGroup N] [Module A N] [Module.Free A N] [Module.Finite A N]
    (ρ : GaloisRep Kb A N)
    {Mf Lf : Type*} [Field Mf] [NumberField Mf] [Field Lf] [NumberField Lf]
    [Algebra Kb Mf] [Algebra Kb Lf]
    (w : HeightOneSpectrum (𝓞 Mf)) (v : HeightOneSpectrum (𝓞 Lf))
    (P : HeightOneSpectrum (𝓞 Kb)) (hunram : ρ.IsUnramifiedAt P)
    (μM μL : Field.absoluteGaloisGroup Kb)
    (XM XL : Field.absoluteGaloisGroup (P.adicCompletion Kb))
    (hXinert : XM⁻¹ * XL ∈ localInertiaGroup P)
    (hMeq : Field.absoluteGaloisGroup.map (algebraMap Kb Mf)
        (Field.absoluteGaloisGroup.map (algebraMap Mf (w.adicCompletion Mf))
          (Field.AbsoluteGaloisGroup.adicArithFrob w))
      = μM * Field.absoluteGaloisGroup.map (algebraMap Kb (P.adicCompletion Kb)) XM * μM⁻¹)
    (hLeq : Field.absoluteGaloisGroup.map (algebraMap Kb Lf)
        (Field.absoluteGaloisGroup.map (algebraMap Lf (v.adicCompletion Lf))
          (Field.AbsoluteGaloisGroup.adicArithFrob v))
      = μL * Field.absoluteGaloisGroup.map (algebraMap Kb (P.adicCompletion Kb)) XL * μL⁻¹) :
    (ρ.map (algebraMap Kb Lf)).charFrob v = (ρ.map (algebraMap Kb Mf)).charFrob w := by
  have hι1 : ρ.toLocal P (XM⁻¹ * XL) = 1 := hunram.localInertiaGroup_le hXinert
  rw [GaloisRep.toLocal_apply] at hι1
  obtain ⟨ν, hνdef⟩ : ∃ ν : Field.absoluteGaloisGroup Kb, μL * μM⁻¹ = ν := ⟨_, rfl⟩
  have hνinv : ν⁻¹ = μM * μL⁻¹ := by rw [← hνdef]; group
  have hXLsplit : Field.absoluteGaloisGroup.map (algebraMap Kb (P.adicCompletion Kb)) XL
      = Field.absoluteGaloisGroup.map (algebraMap Kb (P.adicCompletion Kb)) XM *
        Field.absoluteGaloisGroup.map (algebraMap Kb (P.adicCompletion Kb)) (XM⁻¹ * XL) := by
    conv_lhs => rw [show XL = XM * (XM⁻¹ * XL) from by group]
    rw [map_mul]
  have hgL : Field.absoluteGaloisGroup.map (algebraMap Kb Lf)
        (Field.absoluteGaloisGroup.map (algebraMap Lf (v.adicCompletion Lf))
          (Field.AbsoluteGaloisGroup.adicArithFrob v))
      = ν * Field.absoluteGaloisGroup.map (algebraMap Kb Mf)
          (Field.absoluteGaloisGroup.map (algebraMap Mf (w.adicCompletion Mf))
            (Field.AbsoluteGaloisGroup.adicArithFrob w)) *
        (μM * Field.absoluteGaloisGroup.map (algebraMap Kb (P.adicCompletion Kb))
          (XM⁻¹ * XL) * μL⁻¹) := by
    rw [hLeq, hXLsplit, hMeq, ← hνdef]
    group
  have hκ : (ρ (μM * Field.absoluteGaloisGroup.map
      (algebraMap Kb (P.adicCompletion Kb)) (XM⁻¹ * XL) * μL⁻¹) : Module.End A N) = ρ ν⁻¹ := by
    rw [hνinv, map_mul, map_mul, hι1, mul_one, map_mul]
  have hunit : (ρ ν : Module.End A N) * ρ ν⁻¹ = 1 := by
    rw [← map_mul, mul_inv_cancel, map_one]
  have hunit' : (ρ ν⁻¹ : Module.End A N) * ρ ν = 1 := by
    rw [← map_mul, inv_mul_cancel, map_one]
  obtain ⟨u, hu⟩ := exists_linearEquiv_conj_eq (ρ ν : Module.End A N) (ρ ν⁻¹) hunit hunit'
  have hLHS : (ρ.map (algebraMap Kb Lf)).toLocal v
        (Field.AbsoluteGaloisGroup.adicArithFrob v)
      = u.conj ((ρ.map (algebraMap Kb Mf)).toLocal w
        (Field.AbsoluteGaloisGroup.adicArithFrob w)) := by
    rw [hu, GaloisRep.toLocal_apply, GaloisRep.map_apply, GaloisRep.toLocal_apply,
      GaloisRep.map_apply, hgL, map_mul, map_mul, hκ]
  show ((ρ.map (algebraMap Kb Lf)).toLocal v
      (Field.AbsoluteGaloisGroup.adicArithFrob v)).charpoly
    = ((ρ.map (algebraMap Kb Mf)).toLocal w
      (Field.AbsoluteGaloisGroup.adicArithFrob w)).charpoly
  rw [hLHS, LinearEquiv.charpoly_conj]

open scoped NumberField in
/-- **The Frobenius characteristic polynomial of a hardly ramified `ρ`
depends only on the RESIDUE CARDINALITY of the place** (PROVEN
2026-07-26, cut the same day; PURE ALGEBRAIC NUMBER THEORY — no automorphic input
whatsoever): for `ρ` hardly ramified, for ANY two number fields `M`, `L`
and any places `w` of `M` and `v` of `L` of EQUAL absolute norm, with the
residue characteristic of `w` different from `2` and `ℓ`, the Frobenius
characteristic polynomials of the two base-changed representations
coincide:

  `(ρ|_{G_L}).charFrob v = (ρ|_{G_M}).charFrob w`  whenever `Nv = Nw`.

Note that `v` is NOT required to lie over `w`, and `L` is not required to
contain `M`: the statement is that `charFrob` of a representation of
`G_ℚ` unramified at `q` is a function of the residue cardinality alone.

Classical proof (this is the argument that was carried out; see the
DISCHARGE note below for the four helpers it was factored through).  By
the two exposed `rfl`-lemmas `GaloisRep.toLocal_apply`
and `GaloisRep.map_apply` — used the same way by the PROVEN determinant
lemma `charFrob_baseChange_coeff_zero_eq_absNorm` above —
`(ρ|_{G_M}).charFrob w` is the charpoly of `ρ` evaluated at the element
`g_w ∈ G_ℚ` obtained by pushing the arithmetic Frobenius at `w` through
`G_{M_w} → G_M → G_ℚ`.  That element is an arithmetic Frobenius at SOME
place `P` of `ℚᵃˡᵍ` above the rational prime `q` under `w`: it acts on
the residue field of `P` by `x ↦ x^{Nw}` (this is the content of the
proven `cyclotomicCharacter_adicArithFrob_base_eq_absNorm`, whose
roots-of-unity input `adicArithFrob_rootsOfUnity_pow_base` is exactly
this action), and it is determined by that datum only modulo the inertia
subgroup `I_P`.  Since `Nv = Nw`, the element `g_v` attached to `v` is an
arithmetic Frobenius with the SAME exponent at some place `P'` of `ℚᵃˡᵍ`,
necessarily above the same rational prime `q` (the absolute norm of a
prime is a power of its residue characteristic).  All places of `ℚᵃˡᵍ`
over `q` are `G_ℚ`-conjugate, so `g_v = σ g_w σ⁻¹ · ι` for some
`σ ∈ G_ℚ` and some `ι ∈ I_{P'}`.  Now `q ≠ 2, ℓ` (that is what `hw2` and
`hwℓ` say about `w`, and `hnorm` transports the residue characteristic to
`v`), so `hρ.isUnramified` gives `ρ ι = 1`, and a characteristic
polynomial is invariant under conjugation.  Hence the two charpolys are
equal.

WHY IT IS HERE (the SPLIT-PLACE half of the prime cyclic step).  This is
the engine that discharges, with no automorphic input, every place of
`M = F^D` that is SPLIT in `L/M`: if `w` has a place `v` of `L` above it
with residue degree `1` then `Nv = Nw`, so this lemma identifies the two
Frobenius characteristic polynomials and the descended system over `L`
(the hypothesis `hC` of the prime cyclic step) already answers at `w`.
The residual automorphic citation
`exists_baseChangeDescentData_of_prime_cyclic_step_of_inert` is thereby confined to
the places of `M` whose residue cardinality is realized by NO good place
of `L` — classically the INERT places.  It is the same style of
sharpening as the trace/determinant split one level up: peel off the half
that is pure algebraic number theory, leave the automorphic citation
strictly smaller.

FAITHFULNESS AUDIT (2026-07-26).  `hnorm` is load-bearing and the
statement is FALSE without it (two places of different residue
cardinality have different determinant coefficients `Nv ≠ Nw`, by the
proven `charFrob_baseChange_coeff_zero_eq_absNorm`).  The hypotheses
`hw2`, `hwℓ` are load-bearing too: at `q = 2` or `q = ℓ` the
representation is ramified, the inertia ambiguity in `g_w` is not killed,
and the charpoly genuinely depends on the choice of place of `ℚᵃˡᵍ` and
of the lift.  NOT VACUOUS: the conclusion is an equality of two
`Polynomial O`-valued invariants of an arbitrary hardly ramified `ρ`, and
`Nv = Nw` happens for infinitely many pairs (all places of degree `1`
over a fixed rational prime).

NO CIRCULARITY: this leaf mentions neither the carrier `Wit` nor any
automorphic datum, and its proof route (`toLocal_apply`/`map_apply`
+ the conjugacy of places of `ℚᵃˡᵍ` over `q` + `IsHardlyRamified.isUnramified`)
runs entirely inside `GaloisRep.lean`/`AbsoluteGaloisGroup.lean` material
already used by the proven lemmas of this section.

DISCHARGE (2026-07-26, CARRIED OUT).  The predicted route worked, with the
"all places of `ℚᵃˡᵍ` over `q` are conjugate" step realised WITHOUT any
theory of places of `ℚᵃˡᵍ`: both global Frobenii are pushed DOWN to the
single local group `Γ ℚ_q` at the rational place `q`, where the conjugacy
becomes the statement that two elements inducing the same power map on the
residue field differ by inertia.  Four helpers above:

* `exists_prime_place_rat` — `w` lies over a unique rational prime `q` and
  `Nw = q^e` with `e > 0`, so `Nv = Nw` forces the SAME `q` for `v`
  (`q ∣ q'^{e'}` and both prime).  This is where `hnorm` transports the
  residue characteristic, and hence `hw2`/`hwℓ`, from `w` to `v`;
* `exists_conj_map_adicArithFrob_base` — `g_w = μ_M · X_M · μ_M⁻¹` with
  `X_M ∈ Γ ℚ_q` satisfying `X_M z ≡ z^{Nw}` on the integral closure.  Note
  the EXPONENT is `Nw = q^e`, not `q`: `Field.absoluteGaloisGroup.isArithFrobAt_map`
  is unusable here because it demands equal residue cardinalities, so the
  exponent-`Nw` congruence is transported by hand (the reflection principle
  `mem_maximalIdeal_of_icMap` plus `icMap_smul` does it verbatim);
* the exponent-`Nw` version of `IsArithFrobAt.mul_inv_mem_inertia` (inline,
  four lines): `X_L · X_M⁻¹ ∈ localInertiaGroup q`, since both satisfy the
  SAME congruence — this is the whole force of `Nv = Nw`;
* `charFrob_eq_of_conj_of_inertia` — `hρ.isUnramified q` (legitimate since
  `q ∉ {2, ℓ}`) kills the inertia factor, so the two `ρ`-images are
  conjugate and `LinearEquiv.charpoly_conj` finishes.

PERFORMANCE / INSTANCE NOTE, worth reading before touching this proof: see
the section note above the helpers.  Writing `algebraMap ℚ (P.adicCompletion ℚ)`
at the CONCRETE base `ℚ` picks instances that are propositionally but not
definitionally equal to the ones `GaloisRep.toLocal` carries, and every
attempt to bridge them diverges (`isDefEq` timeout on terms that print
identically).  Keeping the base field a variable in the helpers is what
makes the proof elaborate at all, and it also keeps the concrete module
`Fin 2 → O` out of the `moduleTopology` unfoldings that otherwise cost
tens of seconds per step. -/
theorem charFrob_baseChange_eq_of_absNorm_eq {ℓ : ℕ}
    (hℓodd : Odd ℓ) [Fact ℓ.Prime]
    {O : Type u} [CommRing O] [TopologicalSpace O] [IsTopologicalRing O]
    [IsLocalRing O] [Algebra ℤ_[ℓ] O]
    {ρ : GaloisRep ℚ O (Fin 2 → O)}
    (hrank : Module.rank O (Fin 2 → O) = 2)
    (hρ : IsHardlyRamified hℓodd hrank ρ)
    (M L : Type u) [Field M] [NumberField M] [Field L] [NumberField L]
    (w : HeightOneSpectrum (NumberField.RingOfIntegers M))
    (v : HeightOneSpectrum (NumberField.RingOfIntegers L))
    (hw2 : ((2 : ℕ) : NumberField.RingOfIntegers M) ∉ w.asIdeal)
    (hwℓ : ((ℓ : ℕ) : NumberField.RingOfIntegers M) ∉ w.asIdeal)
    (hnorm : Ideal.absNorm v.asIdeal = Ideal.absNorm w.asIdeal) :
    (ρ.map (algebraMap ℚ L)).charFrob v =
      (ρ.map (algebraMap ℚ M)).charFrob w := by
  classical
  obtain ⟨q, e, hq, _he, hcomapM, hnormM⟩ := exists_prime_place_rat M w
  obtain ⟨q', e', hq', he', hcomapL, hnormL⟩ := exists_prime_place_rat L v
  -- the two residue characteristics agree
  have hqq : q' = q := by
    have h1 : q' ^ e' = q ^ e := by rw [← hnormL, ← hnormM, hnorm]
    have h2 : q' ∣ q ^ e := h1 ▸ dvd_pow_self q' he'.ne'
    exact (Nat.prime_dvd_prime_iff_eq hq' hq).mp (hq'.dvd_of_dvd_pow h2)
  subst hqq
  have hcomapM' : Ideal.comap (algebraMap (𝓞 ℚ) (𝓞 M)) w.asIdeal =
      hq'.toHeightOneSpectrumRingOfIntegersRat.asIdeal := hcomapM
  have hcomapL' : Ideal.comap (algebraMap (𝓞 ℚ) (𝓞 L)) v.asIdeal =
      hq'.toHeightOneSpectrumRingOfIntegersRat.asIdeal := hcomapL
  -- `q ≠ 2` and `q ≠ ℓ`, read off from `w`
  have hmemM : ∀ n : ℕ, (n : 𝓞 ℚ) ∈ hq'.toHeightOneSpectrumRingOfIntegersRat.asIdeal →
      ((n : ℕ) : 𝓞 M) ∈ w.asIdeal := by
    intro n hn
    rw [← hcomapM', Ideal.mem_comap] at hn
    rwa [map_natCast] at hn
  have hqnat : ((q' : ℕ) : 𝓞 ℚ) ∈ hq'.toHeightOneSpectrumRingOfIntegersRat.asIdeal := by
    rw [asIdeal_toHeightOneSpectrumRingOfIntegersRat]
    exact Ideal.mem_span_singleton_self _
  have hq2 : q' ≠ 2 := by
    rintro rfl; exact hw2 (hmemM 2 hqnat)
  have hqℓ : q' ≠ ℓ := by
    rintro rfl; exact hwℓ (hmemM q' hqnat)
  obtain ⟨μM, XM, hXM, hMeq⟩ :=
    exists_conj_map_adicArithFrob_base hq'.toHeightOneSpectrumRingOfIntegersRat M w hcomapM'
  obtain ⟨μL, XL, hXL, hLeq⟩ :=
    exists_conj_map_adicArithFrob_base hq'.toHeightOneSpectrumRingOfIntegersRat L v hcomapL'
  rw [hnorm] at hXL
  -- the two rational Frobenii differ by inertia
  have h1 : XL * XM⁻¹ ∈ localInertiaGroup hq'.toHeightOneSpectrumRingOfIntegersRat := by
    intro z
    have key := sub_mem (hXL (XM⁻¹ • z)) (hXM (XM⁻¹ • z))
    rw [sub_sub_sub_cancel_right, smul_inv_smul] at key
    rw [mul_smul]
    exact key
  have h2 : XM⁻¹ * XL ∈ localInertiaGroup hq'.toHeightOneSpectrumRingOfIntegersRat := by
    have h3 := Field.absoluteGaloisGroup.conj_mem_localInertiaGroup
      hq'.toHeightOneSpectrumRingOfIntegersRat XM⁻¹ (XL * XM⁻¹) h1
    rwa [show XM⁻¹ * (XL * XM⁻¹) * (XM⁻¹)⁻¹ = XM⁻¹ * XL from by group] at h3
  exact charFrob_eq_of_conj_of_inertia ρ w v hq'.toHeightOneSpectrumRingOfIntegersRat
    (hρ.isUnramified q' hq' ⟨hq2, hqℓ⟩) μM μL XM XL h2 hMeq hLeq

/-- **ARTHUR–CLOZEL DESCENT FOR ONE PRIME-DEGREE CYCLIC STEP — THE
LITERATURE CITATION ITSELF** (sorry LEAF, cut 2026-07-26, THIRD OWNER):
Arthur–Clozel, *Simple Algebras, Base Change, and the Advanced Theory of
the Trace Formula*, Ann. of Math. Studies 120 (1989), **Ch. 3 Thm 4.2(d)**
(WEAK LIFTING, descent half), with **Ch. 3 Thm 3.1** (fibres of global
base change), **Ch. 3 Thm 5.1** (STRONG LIFTING) and **Ch. 1 §6** (base
change lifting of local representations — the twisted character identity
`Θ_{BC(π)}(g × σ) = Θ_π(N g)`).  For `GL(2)` this is Langlands, *Base
Change for GL(2)*, Ann. of Math. Studies 96 (1980).

**RESTATED 2026-07-27 OVER THE EXISTENTIAL COEFFICIENT FIELD — the repair
this docstring's own finding (6) below prescribes is now DONE, here and in
the two nodes above it.**  The `L`-side eigensystem is no longer typed at
`Wit.E`: it is given over an arbitrary number field `EL` with an embedding
`ψL : EL → ℚ̄_ℓ`, and the descended data are returned over an
EXISTENTIALLY quantified number field `EM` with `ψM : EM → ℚ̄_ℓ` and
`ιM : EL →+* EM` satisfying `ψM ∘ ιM = ψL`.  Nothing else moved: the
arithmetic hypothesis package, the `η`-torsor shape of the conclusion
(`ζ w ^ p = 1`, `coeff 1 = ζ w * ψM (a w)`, `coeff 0 = ζ w ^ 2 * ψM (δ w)`)
and the inert-places restriction are all verbatim what they were.

Why the old form could not stand: findings (6) and (7) below show that for
an ARBITRARY carrier the descended eigenvalue need not lie in `ψℓ(Wit.E)`
at all — at an inert `w` it is a ROOT of the degree-`p` Dickson relation
`a_W = D_p(a_w, Nw)`, so the Hecke field grows by degree `≤ p` per downward
step, and no a-priori bound pins it back (counterexample in (7)).  A leaf
demanding `Wit.E`-rationality of the descended trace is therefore not
merely hard, it is unprovable as stated, and restating it is the fix rather
than a weakening.

WHAT THE CITED THEOREM SAYS, verbatim in the source's notation.  `E/F` is
cyclic of prime degree `l`, `η` is a character of `A_F^×` vanishing
exactly on `F^× N(A_E^×)` — by class field theory, a generator of the
character group of `Gal(E/F)`.  Ch. 3 Thm 4.2(d): *"Assume `Π` is
cuspidal, `Π = Π ∘ σ`.  Then there is `π` cuspidal lifting to `Π`; all
such `π` are conjugate by tensor product by a power of `η`."*  Ch. 3 Thm
5.1 upgrades "lifting" from "at almost all places" to "at every place",
so the relation between `π` and `Π` is the local character identity at
each place, hence a relation between Hecke eigenvalues.  Ch. 3 Thm 3.1 is
the general fibre statement (`t_{π',v} = t_{π,v} ∘ N` for almost all `v`
forces `π' ≅ π ⊗ χ`).

TRANSLATED INTO THIS MODULE'S VOCABULARY (there is no automorphic
vocabulary on this pin — see the PIN AUDIT on the consumer below — so
the citation is stated through Frobenius characteristic polynomials, as
everything else in this module is).  Write `M = F^D`, `L = F^C`, so
`L/M` is cyclic of degree `p` (`hcard`), and let `w` be a place of `M`
at which the `L`-system `(SL, PL, hPL)` says nothing directly — the
INERT places, `∀ v ∉ SL, Nv ≠ Nw`.  Classically:

* `ρ|_{G_L}` is, through Carayol local–global compatibility, the
  representation of a cuspidal `Π` over `L` whose eigensystem is `PL`;
  `Π` is `Gal(L/M)`-invariant because `ρ|_{G_L}` extends to `G_M`;
* by **Thm 4.2(d)** there is a cuspidal `π` over `M` with `BC(π) = Π`,
  and the fibre is `{π ⊗ η^j : 0 ≤ j < p}` — a TORSOR under the
  character group of `Gal(L/M)`, not a point;
* `ρ|_{G_M}` restricts on `G_L` to `ρ_Π = ρ_π|_{G_L}`, so (Thm 3.1 on
  the automorphic side, or Schur on the Galois side) `ρ|_{G_M} ≅ ρ_π ⊗ χ`
  for a character `χ` of `Gal(L/M)`, i.e. `ρ|_{G_M}` is attached to the
  member `π ⊗ χ` of that fibre.

Fix ONE member `π` whose Hecke field embeds in `E` — that is exactly
what the DESCENT-CLOSURE normalization of `PotentialModularityWitness.E`
provides (`E` may be enlarged to the compositum of the Hecke fields of
all descended forms without touching a consumer), and the central
character of `π` takes values in that same Hecke field.  Put
`ζ w = χ(Frob_w)`, `a w = −a_w(π)` and `δ w = ω_π(ϖ_w)·Nw` for that
fixed `π`.  Then `χ` has order dividing `p`, so `ζ w ^ p = 1`; the
charpoly of `(ρ_π ⊗ χ)(Frob_w)` is
`X² − ζ w · a_w(π) · X + ζ w ^ 2 · det ρ_π(Frob_w)`, because twisting a
rank-`2` representation by a character scales the charpoly's coefficient
in degree `i` by `ζ ^ (2 − i)`; and that is precisely the conclusion
below.  **The `ζ w ^ 2` on the constant coefficient and the `ζ w ^ 1` on
the linear one are the whole point of stating the citation this way.**

WHY THIS IS THE RIGHT SORRIED LEAF, AND WHAT IT BUYS (read with the
INFORMATION AUDIT on the consumer, which this refines).  The consumer
`exists_cuspidalHeckeEigenvalue_of_prime_cyclic_step_of_inert` asserts
outright that the descended eigenvalue satisfies
`ψM (aM w) = −ιO(coeff 1)`, over the descended coefficient field `EM`
this leaf produces (the field was fixed at `Wit.E` before the 2026-07-27
existential-coefficient-field restatement).  **That is not what
Arthur–Clozel proves.**
AC delivers descent only up to the `η`-torsor, and a reader checking the
consumer against Ch. 3 Thm 4.2(d) would find a gap exactly at the twist.
This leaf states what the reference delivers; the twist is then killed
HERE, in Lean, by a genuinely arithmetic step that is not part of the
citation:

  `ζ w ^ 2 · ψℓ (δ w) = ιO(coeff 0) = Nw` — the PROVEN
  `charFrob_baseChange_coeff_zero_eq_absNorm`, `ρ` being hardly ramified
  with cyclotomic determinant — so `ζ w ^ 2 ∈ ψℓ(E)`; and a `p`-th root
  of unity whose SQUARE lies in a subfield lies in that subfield
  (`p = 2`: `ζ ^ 2 = 1` so `ζ = ±1`; `p` odd: `ζ = (ζ ^ 2) ^ ((p+1)/2)`).

REFUTES ONE CLAIM OF THE PREVIOUS AUDIT.  The INFORMATION AUDIT below
states that "any cut along that seam needs `μ_p ⊆ Set.range ψℓ`, which is
FALSE for an abstract carrier".  That is correct for the seam it was
examining — selecting the `E`-rational ROOT of `D_p(X, Nw) − c`, where
the competing roots `ζ^j α + ζ^{−j} β` all have the SAME determinant `Nw`
and the determinant therefore separates nothing.  It is NOT correct for
the BASE-CHANGE-FIBRE seam cut here: the competing members `π ⊗ η^j` have
determinants `ζ^{2j}·Nw`, which are pairwise DISTINCT for `p` odd, so the
rationality of the determinant — free, and already proven in this module
— selects the member on the nose and no `p`-th root of unity is ever
required to lie in `E`.  The two seams are different precisely because
Dickson conjugates preserve the determinant and character twists do not.
Anyone tempted to re-close this node should check which of the two seams
they are on.

HONEST ACCOUNTING (this is a FAITHFULNESS cut, not a strength reduction).
Away from `ℓ` this leaf and its consumer are INTERDERIVABLE: the consumer
implies this leaf by taking `ζ w = 1`, `a w` the trace preimage and
`δ w = Nw`.  So no logical content has been removed, and the `sorry`
count is unchanged.  What changes is that the sorried statement is now
the shape the literature actually delivers — descent up to the
`η`-torsor — instead of a statement that silently absorbs the selection
of the untwisted member, and that selection is now a checked Lean proof
rather than a paragraph of a docstring.

SOUNDNESS, both routes, inherited from the consumer and unweakened here:
(i) direct — the classical argument above, for a carrier whose `E` was
chosen by the DESCENT-CLOSURE normalization; (ii) collapse — the
arithmetic hypothesis package (an irreducible hardly ramified mod-`ℓ`
representation with `ℓ ≥ 5`) is classically unsatisfiable, so the
statement holds for every carrier, abstract ones included.  The
hypothesis package is retained VERBATIM from the consumer precisely to
keep route (ii) available.

CIRCULARITY GUARD (inherited from pillar β, load-bearing): no discharge
through `Family.lean`, `Lift.lean`, or `Modularity/Interface.lean`; and
the ROUTE AUDIT on the consumer applies verbatim — `absurd hirr
(not_isIrreducible_of_isHardlyRamified_of_five_le …)` is CIRCULAR here,
since the headline consumes this leaf through the chain recorded there.

FOURTH-OWNER AUDIT (2026-07-27).  Four findings.  Three of them close off
routes a reader of the docstring above would try FIRST, and the fourth is
the most promising unexplored one.  Each is stated with the check that
would refute it.

(1) CITATION-SCOPE DEFECT — THE CITED THEOREM'S INPUT IS NOT AMONG THE
HYPOTHESES.  Arthur–Clozel Ch. 3 Thm 4.2(d) takes as input a CUSPIDAL
automorphic `Π` over `L` that is `Gal(L/M)`-invariant, and returns the
descended `π` over `M`.  This leaf's binders contain no such object.
What they contain about `L` is `hPL` alone, and `hPL` is bare
`E`-RATIONALITY of Frobenius characteristic polynomials: it says they
agree with SOME function `PL : places of L → Polynomial E`, and `PL` is
otherwise unconstrained.  The only automorphic datum in scope anywhere is
`Wit.modularF`, and that is over `F`, not over `L`.

The defect is one level up, in the datum the induction propagates.  Read
`HeckeSystemDescendsTo` (defined above in this module): it is literally
`∃ S P, ∀ w ∉ S, (charFrob w).map ιO = (P w).map ψℓ`.  The BASE case
(`C = ⊥`, so `L = F`) is fine — there `hPL` IS `Wit.modularF`, the
`L`-side object really is the Hilbert newform, and AC applies.  EVERY
LATER STEP IS NOT: its `hPL` is the previous step's conclusion, a bare
polynomial system, and Thm 4.2(d) has nothing to act on.  So route (i)
above cannot be carried out here BY ANYONE, however much automorphic
theory is added to the pin — not for want of a theorem but for want of a
hypothesis.  The leaf itself remains TRUE (route (ii), collapse, is
untouched); this is a cut defect, not a falsity.

REPAIR (cut-level, NOT this owner's to make): strengthen
`HeckeSystemDescendsTo Wit C` to carry an automorphic eigensystem over
`F^C` — the analogue over `F^C` of `Wit.heckeF`, a cuspidal Hilbert
newform datum over the (totally real, since `F^C ⊆ F`) field `F^C` whose
Hecke polynomials are the charpolys — instead of an arbitrary
`Polynomial E`-valued function.  The prime step then RECEIVES the `Π`
Thm 4.2(d) requires and RETURNS the `π` the next step needs, and the
citation becomes supported at every stage rather than only the first.
That edit moves `HeckeSystemDescendsTo`, its `C = ⊥` base case,
`heckeSystemDescendsTo_of_prime_cyclic_step` and the final consumer, so
it needs a named owner.

CHECK THAT REFUTES (1): exhibit, among the binders of this theorem, an
object asserting automorphy of the `L`-eigensystem — or a hypothesis that
`C` is solvable, which would let AC descend `Wit.modularF` from `F` to
`L` first and supply `Π`.  There is neither.

(2) THE `ζ` IS FORMALLY VACUOUS: this leaf and the UNTWISTED statement
are EQUIVALENT, not merely "interderivable away from `ℓ`".  Forward: take
`ζ w = 1`, as the HONEST ACCOUNTING above records.  Backward: the PROVEN
body of the consumer
`exists_cuspidalHeckeEigenvalue_of_prime_cyclic_step_of_inert`
immediately below derives `ζ w ∈ Set.range ψM` from
`ζ w ^ 2 · ψM (δ w) = ιO(coeff 0) = Nw`, for BOTH parities of `p`, using
no hypothesis this leaf does not already carry.  Consequence: the
`η`-torsor the cut was made to expose is NOT visible in the statement,
and nobody should read the `ζ` as recording residual automorphic
ambiguity.  The cut's gain is presentational — the statement can be
checked line by line against Ch. 3 Thm 4.2(d) — not logical.

CHECK THAT REFUTES (2): find an instantiation where
`charFrob_baseChange_coeff_zero_eq_absNorm` fails, so `ιO(coeff 0) = Nw`
fails and `ζ w ^ 2` is not forced into `ψℓ(E)`.  Its only hypothesis
beyond `hρ` is that `w` avoids `ℓ`, and `S` is existentially quantified
here exactly as in the consumer (which discharges it with
`exists_finset_forall_natCast_notMem_asIdeal`), so there is none.

(3) `Wit.modularF` IS UNUSABLE AT EXACTLY THE PLACES THIS LEAF IS ABOUT.
Worth recording because it is the first shortcut anyone will try.  The
proven sibling `charFrob_baseChange_eq_of_absNorm_eq` equates charpolys
across DIFFERENT number fields whenever the absolute norms agree.  So a
single `u ∉ Wit.badF` with `Nu = Nw` would give
`charFrob_M w = charFrob_F u`, and `Wit.modularF` would close the leaf at
`w` for free with `ζ w = 1`.  It never happens.  Let `q` be the rational
prime under `w`, unramified in `F`, and `σ` a Frobenius at a place of `F`
over `q`.  Places of `F` over `q` have norm `q ^ (orderOf σ)`, and the
place of `F^D` (resp. `F^C`) in the double coset of `g` has residue
degree `min {n > 0 | g σ^n g⁻¹ ∈ D}` (resp. with `C`).  Put
`τ = g σ g⁻¹` and let `e = min {n | τ^n ∈ D}` be `w`'s residue degree.  A
matching place of `F` forces `orderOf σ = e`, hence `τ^e = 1 ∈ C`, hence
`min {n | τ^n ∈ C} ≤ e`; and `hCD : C ≤ D` forces
`min {n | τ^n ∈ C} ≥ min {n | τ^n ∈ D} = e`.  So they are equal, and the
place `v` of `L = F^C` in the same double coset has `Nv = q^e = Nw` —
which `hinert` forbids.  Hence outside the finite set of places under
`SL` (and the ramified ones), `hinert` PRECLUDES any matching place of
`F`: the automorphic datum we do have is blind to precisely these `w`.

CHECK THAT REFUTES (3): produce `τ ∈ Gal(F/ℚ)` with
`min {n | τ^n ∈ C} < min {n | τ^n ∈ D}`.  Impossible under `hCD`; the
argument is exactly as strong as that hypothesis and no stronger.

(4) THE UNCONDITIONAL GALOIS-DESCENT ROUTE, AND THE EXACT POINT WHERE IT
STOPS.  There is a route needing NO automorphic input, and it deserves
recording because it almost works — a future owner should not rediscover
it and then rediscover its obstruction.

Let `K ⊆ ℚ̄_ℓ` be a subfield containing the traces of `ρ|_{G_L}` on the
WHOLE group, and suppose `ρ|_{G_L}` is absolutely irreducible.  The
`K`-span `R` of `ρ(G_L)` in `M₂(ℚ̄_ℓ)` is then a `K`-form of `M₂`:
spanning by Burnside, and `dim_K R = 4` because the trace form is
`K`-valued on `ρ(G_L) · ρ(G_L) ⊆ ρ(G_L)` and nondegenerate.  A lift `g`
of a generator of `Gal(L/M)` normalizes `G_L`, so `x ↦ ρ(g) x ρ(g)⁻¹` is
a `K`-algebra automorphism of `R`; by Skolem–Noether it is inner, say by
`u ∈ R^×`, so `ρ(g) = λ · u` with `λ ∈ ℚ̄_ℓ^×` and `tr ρ(g) ∈ λ · K`.
Two constraints pin `λ` modulo `K^×`: `ρ(g)^p = ρ(g^p)` with `g^p ∈ G_L`
gives `λ^p ∈ K^×` (the scalar lies in `R`, whose centre is `K`), and
`det ρ(g) = Nrd(u) · λ^2` with `det ρ` cyclotomic, hence in `ℚ ⊆ K`,
gives `λ^2 ∈ K^×`.  For `p` ODD, `gcd(2, p) = 1`, so `λ ∈ K^×` and
`tr ρ(G_M) ⊆ K`.  This is the SAME phenomenon as the consumer's
`ζ`-killing proof, and it says what the `η`-torsor really is: the class
of `λ` in `ℚ̄_ℓ^× / K^×`, killed by `λ^2, λ^p ∈ K^×`.  At `p = 2` the two
constraints coincide and a genuine class of order `2` survives, so the
route is odd-`p`-only.

WHY IT DOES NOT CLOSE THE LEAF, precisely.  (a) It needs traces on ALL of
`G_L`, while `hPL` supplies them only at Frobenii; upgrading by
Chebotarev needs `{x | tr ρ(x) ∈ K}` CLOSED, and `K = ψℓ(E)` is not
closed in `ℚ̄_ℓ` — `E` is a number field (`Wit.numberFieldE`) and already
`ψℓ(ℚ) ∩ ℤ_ℓ = ℤ_(ℓ)` is dense in `ℤ_ℓ`.  What IS closed is the
completion `E_λ = ψℓ(E) · ℚ_ℓ`, a finite extension of `ℚ_ℓ`, and the
whole argument runs verbatim with `K = E_λ`.  So the route does prove,
unconditionally and with no automorphic input,

  `p` odd  ⟹  `ιO ((charFrob_M w).coeff 1) ∈ E_λ`,

and the ENTIRE residual content of this leaf is the gap between `E_λ` and
the number field `ψℓ(E)` — classically supplied by the algebraicity of
Hecke eigenvalues, and supplied by nothing here.  (b) It also needs
`ρ|_{G_L}` absolutely irreducible, which is NOT a hypothesis either:
`hirr` is irreducibility of `ρbar` over `ℚ`, and irreducibility can be
lost on restriction to a solvable extension.

CHECK THAT REFUTES (4): exhibit a proof that
`{x ∈ G_L | tr ρ(x) ∈ Set.range ψℓ}` is closed; or an a-priori bound
(degree over `ψℓ(E)` together with an archimedean/Weil bound on the
eigenvalues) pinning an element of `E_λ` that is algebraic of degree `≤ p`
over `ψℓ(E)` into `ψℓ(E)`.  The second is NOT hopeless and is the most
promising unexplored route here: at an inert `w` the unique place `W` of
`L` above it has `NW = Nw ^ p`, so `hPL` at `W` makes
`ιO ((charFrob_M w).coeff 1)` a root of the degree-`p` Dickson equation
`D_p(X, Nw) = ψℓ(c)`, hence algebraic of degree `≤ p` over `ψℓ(E)`.
Building that hypothesis needs the inert place and the `p`-th-power
Frobenius comparison; the proven helpers
`exists_conj_map_adicArithFrob_base` and `charFrob_eq_of_conj_of_inertia`
above are the right tools (`X_L` and `X_M ^ p` induce the same power map
on the residue field, hence differ by inertia), together with mathlib's
`Ideal.absNorm_eq_pow_inertiaDeg'_of_liesOver` and `Ideal.inertiaDeg_tower`
for `NW = Nw ^ p`.  Note this cut is NOT the one the INFORMATION AUDIT
above rejected: that objection ("needs `μ_p ⊆ Set.range ψℓ`") is about
deducing the conclusion FROM "some root of `D_p(X, Nw) − c` is
`E`-rational", whereas here the Dickson relation is an ADDED hypothesis
on a leaf that keeps the full arithmetic context.

FIFTH-OWNER AUDIT (2026-07-27).  Three findings: a STATUS check on the
repair proposed in (1); a SECOND, INDEPENDENT cut defect which that
repair does not fix and which its owner must fix at the same time; and
an explicit REFUTATION of the route (4) recommends as most promising.

(5) STATUS OF THE REPAIR PROPOSED IN (1): NOT LANDED as of 2026-07-27.
`HeckeSystemDescendsTo` above is still, verbatim,
`∃ S P, ∀ w ∉ S, (charFrob w).map ιO = (P w).map ψℓ` — no automorphic
clause, no newform datum.  So finding (1) stands unaltered and route (i)
remains unavailable at every step of the induction except the base.

CHECK THAT REFUTES (5): `grep -n 'def HeckeSystemDescendsTo' -A 14` in
this module.  If the body binds a cuspidal Hilbert newform datum over
`IntermediateField.fixedField C`, the repair has landed and (1), (5)
and (6) should all be re-read before any further work here.

(6) THE PROPOSED REPAIR IS NECESSARY BUT NOT SUFFICIENT — `Wit.E` IS
FIXED ALONG THE TOWER WHILE THE HECKE FIELD PROVABLY GROWS DOWN IT.
`HeckeSystemDescendsTo Wit C` types its polynomials as
`Polynomial Wit.E`: the SAME `Wit.E` at every `C`.  But the
DESCENT-CLOSURE note in the `PotentialModularityWitness` docstring
records — correctly — that the Hecke field GROWS on the way down, and
this leaf is exactly where it grows.  At its own inert `w`, with `W` the
unique place of `L` above it, the Satake parameters satisfy
`a_W = D_p(a_w, Nw)`, so `hPL` places `a_W` in `ψℓ(E)` and thereby forces
only that the DESCENDED `a_w` is algebraic of degree `≤ p` over `ψℓ(E)`;
`ℚ(α+β) ⊇ ℚ(α^p+β^p)` always, and the inclusion is PROPER in general.
Hence even with a cuspidal `Π` over `L` in hand and Thm 4.2(d) applied,
the `π` it returns has eigenvalues in a field that is in general a proper
extension of `Wit.E`, while the conclusion demands `a δ : … → Wit.E`.

Nothing repairs this INSIDE the leaf, because `Wit` is universally
quantified here.  The DESCENT-CLOSURE note resolves it by saying the
PRODUCING leaf `exists_potentialModularityWitness_of_five_le` "MUST be
understood as" choosing `E` large enough — but that is an understanding,
not a hypothesis: no clause of `PotentialModularityWitness` constrains
`E` beyond `Field` and `NumberField`, as that structure's own docstring
states outright ("no field asserts that `heckeF` GENERATES `E`").  A Lean
proof of this leaf may not use an understanding.  So strengthening
`HeckeSystemDescendsTo` to carry automorphy over `F^C` while KEEPING
`Polynomial Wit.E` yields a predicate whose prime step is still
unprovable: the automorphic datum arrives, and its eigenvalues land
outside the field the conclusion demands.

REPAIR (cut-level, and it must be made TOGETHER with (1)'s, by the same
owner): make the descended coefficient field EXISTENTIAL instead of
fixed —

  `∃ (E' : Type u) (_ : Field E') (_ : NumberField E')`
  `  (ψ' : E' →+* AlgebraicClosure ℚ_[ℓ]) (S) (P : … → Polynomial E'), …`

The base case `heckeSystemDescendsTo_bot` takes `E' := Wit.E`,
`ψ' := Wit.ψℓ` unchanged; each prime step is then free to enlarge.
DOWNSTREAM TOLERATES IT — checked, not assumed: the only use the final
consumer `threeadicRealization_det_cyclotomic_of_witness` makes of the
coefficient field is injectivity of the embedding (automatic for a
ring hom out of a field) and the characteristic-zero cast
`(Pv q).coeff 0 = q`; neither mentions `Wit.E` as such.  The one genuinely
new obligation sits at the Brauer gluing
`exists_heckeField_system_of_witness`, which glues `n` pieces and would
then hold `n` different `E'ᵢ`: it needs their COMPOSITUM inside `ℚ̄_ℓ`,
which is a finitely generated algebraic extension of `ℚ` and hence still
a number field, but that is a real formalization step and should be
budgeted.

CHECK THAT REFUTES (6): exhibit a clause of `PotentialModularityWitness`
(the structure above) tying `E` to `heckeF` or to the descent; or exhibit
a proof that `ℚ(a_w) = ℚ(D_p(a_w, Nw))`.

**THAT CHECK HAS SINCE BEEN MET (2026-07-27).**  The structure now
carries `descentClosed`, a clause tying `E` to the descent precisely as
demanded, discharged at the inhabitation site by
`exists_descentClosed_heckePackage`.  Finding (6) was correct when
written and its diagnosis stands — the growth of the Hecke field is real,
and the existential coefficient field in `HeckeSystemDescendsTo` is the
right response to it — but its conclusion that nothing constrains `E` is
now false, and the residual `Wit.E`-rationality it identified is
available as `heckeField_descentClosed_of_witness` (PROVEN).  The
original check text is retained below for the record; do not act on it.

ORIGINAL: exhibit a clause of `PotentialModularityWitness`
tying `E` to `heckeF` or to the descent; or exhibit
a proof that `ℚ(a_w) = ℚ(D_p(a_w, Nw))`.  The latter is false already at
`p = 2`, `Nw = 2`, `a_w = √2`, where `D_2(a_w, Nw) = a_w^2 − 2·Nw = −2`
generates `ℚ` while `a_w` does not lie in it.

(7) THE ROUTE (4) CALLS MOST PROMISING IS REFUTED BY AN EXPLICIT
COUNTEREXAMPLE.  Finding (4) proposes to close the `E_λ`-versus-`ψℓ(E)`
gap by "an a-priori bound (degree over `ψℓ(E)` together with an
archimedean/Weil bound on the eigenvalues) pinning an element of `E_λ`
that is algebraic of degree `≤ p` over `ψℓ(E)` into `ψℓ(E)`".  No such
bound exists, because the statement it would have to prove is FALSE.

Take `E = ℚ` (a legal `Wit.E`, by (6): nothing forces it larger), so
`ψℓ(E) = ℚ ⊆ ℚ_ℓ ⊆ E_λ`.  Take `p = 3`, `ℓ = 11`, `Nw = 9` (the norm of a
place of residue degree `2` over `3`), and `x = 3√3`.  Then:
`x ∈ ℚ_11` because `3 ≡ 5^2 mod 11`, so `x ∈ E_λ`; `x` is algebraic of
degree `2 ≤ p` over `ψℓ(E)`; the Dickson relation holds with `c = 0`,
since `D_3(X, N) = X^3 − 3NX` gives `D_3(3√3, 9) = 3√3·(27 − 27) = 0`;
and the Weil bound holds, `|x| = 3√3 ≈ 5.196 ≤ 2√Nw = 6`.  Yet `x ∉ ℚ`.
Every hypothesis of the proposed pinning is met and its conclusion fails,
and adding `E_λ`-membership does not help since the witness already lies
in `ℚ_ℓ` itself.  (`p = 2` fails the same way: `ℓ = 7`, `Nw = 2`,
`x = √2`, `c = −2`, `2 ≡ 3^2 mod 7`.)

This is not a claim that the arithmetic context cannot be used further —
only that the specific a-priori pinning (4) recommends cannot be proven,
so a future owner should not spend a cycle building the `p`-th-power
Frobenius comparison in order to reach it.  Findings (6) and (7) have the
same root: for an arbitrary carrier the descended eigenvalue genuinely
need NOT lie in `ψℓ(Wit.E)`, so the residual content of this leaf is not
merely the `E_λ`-to-`ψℓ(E)` gap that (4) describes — it is that the true
classical answer can sit outside the demanded field altogether.  Only the
cut-level repair (1)+(6) removes that.

CHECK THAT REFUTES (7): show `Wit.E` is constrained to contain the
descended Hecke fields — which is exactly the check that refutes (6), and
fails for the same reason.

(8) THE RAMANUJAN CLAUSE, ADDED 2026-07-27 (SEVENTH OWNER), AND WHAT IT
COSTS.  The conclusion now also carries, on the UNTWISTED coefficient
`a w` and for EVERY complex embedding `φ : EM →+* ℂ`, the archimedean
bound `‖φ (a w)‖ ≤ 2 √(Nw)`.  Three things to know about it.

*What it buys.*  It makes this leaf the SINGLE Arthur–Clozel citation of
the descent route.  Before the addition there were TWO sorried leaves
stating the same Thm 4.2(d) — this one in `η`-torsor form, and
`exists_cuspidalBaseChangeDescentData_of_prime_cyclic_step_of_inert` in
torsor form WITH the Ramanujan clause — and the cuspidal consumer was
proven over the second.  With the clause here, the second is redundant
and was DELETED (2026-07-27); the consumer
`exists_cuspidalHeckeEigenvalue_of_prime_cyclic_step_of_inert` is now
proven over this leaf directly.  The transfer is exact: that node's
witness is `−(e · a w)` where `ψM e = ζ w`, and `ψM (e ^ p) = ζ w ^ p = 1
= ψM 1` forces `e ^ p = 1` by injectivity of `ψM` (a ring hom out of a
field), so `φ (e) ^ p = 1` and `‖φ e‖ = 1` for EVERY `φ` — the bound
transfers unchanged, with no hypothesis of that node consumed.

*Why it costs the citation nothing.*  Thm 4.2(d) returns a CUSPIDAL `π`,
and the Ramanujan–Petersson bound for a cuspidal Hilbert newform of
parallel weight `2` (Blasius, following Brylinski–Labesse and Carayol) is
part of the same classical package that supplies the descent itself.  So
route (i) delivers the bound together with the eigenvalue rather than in
addition to it, and route (ii) — the arithmetic package
(`hρ`, `hρbar`, `hirr`, `ℓ ≥ 5`) being classically unsatisfiable — covers
it for every carrier exactly as it covers the rest of the conclusion.
Note finding (1) above: route (i) is in any case unavailable at every
step of the tower but the base, so the leaf's truth already rests on
route (ii) alone and the added clause does not change that.

*SCOPE OF THE ADDED CLAUSE, stated so nobody over-reads it.*  `PL` here
is an ARBITRARY polynomial function, so on route (i) the added bound is
supported only when `PL` is the genuine cuspidal `L`-eigensystem — which
is what the sole call site supplies
(`exists_cuspidalHeckeEigenvalue_of_prime_cyclic_step_of_inert`
instantiates `PL v = X² − C (aL v)·X + C (Nv)` from a
`HeckeSystemDescendsTo` datum, whose `a` carries the bound).  The edit
that would make route (i) support it for arbitrary `PL` is a single extra
binder,

  `(hPLcusp : ∀ v ∉ SL, ∀ φ : EL →+* ℂ,`
  `   ‖φ ((PL v).coeff 1)‖ ≤ 2 * Real.sqrt (Ideal.absNorm v.asIdeal))`,

threaded from the `h2L` field of `HeckeSystemDescendsTo` at that call
site.  It was deliberately NOT made, because it weakens a citation whose
truth does not depend on it and because the arithmetic hypothesis package
is retained VERBATIM to keep route (ii) available; a future owner who
wants the stronger form has the whole edit written out above.

CHECK THAT REFUTES (8): exhibit an instantiation of the arithmetic
package (`hρ` hardly ramified with `ℓ ≥ 5`, `ρbar` hardly ramified and
irreducible, `hπ` a reduction) — i.e. refute the module headline.  Any
such instantiation refutes the whole leaf, added clause or not; there is
no instantiation refuting only the clause.

THE CLASSICAL ARGUMENT, IN THREE MOVES — the joints of the literature
argument, in order (inherited 2026-07-27 from the deleted trace pair
`exists_heckeTrace_of_prime_cyclic_step{,_of_inert}`, whose docstrings
carried it; both were fully PROVEN but had lost every application to the
2026-07-27 reroute through the cuspidal side, so they were deleted as
free-floating and their unique content moved here):

* *Cyclic ascent (base change).*  `Gal(L/M) ≅ D/C` is cyclic of order
  `p`; Langlands' cyclic base change `BC_{L/M}` is defined on the
  cuspidal spectrum of `GL(2)/M` and characterized by the Arthur–Clozel
  twisted character identity.  The descended system over `L` is, through
  Carayol local–global compatibility, the eigensystem of a Hilbert
  newform `f_L` over `L`.
* *`Gal(L/M)`-invariance.*  `f_L`'s Galois representation is `ρ|_{G_L}` —
  the restriction to `G_L` of the representation `ρ|_{G_M}` of the LARGER
  group `G_M` — hence visibly `Gal(L/M)`-invariant: for `σ ∈ Gal(L/M)`,
  `f_L^σ` has the same Frobenius eigenvalues as `f_L` at almost all
  places, so `f_L^σ = f_L` by strong multiplicity one.
* *Cyclic descent (the twisted character identity).*  A
  `Gal(L/M)`-invariant cuspidal automorphic representation of `GL(2)/L`
  is in the image of base change from `GL(2)/M`, and its fibre is a
  torsor under the characters of `Gal(L/M)`.  So there is a Hilbert
  newform `f_M` over `M` with `BC_{L/M}(f_M) = f_L`; its `ℓ`-adic
  representation restricted to `G_L` agrees with `ρ|_{G_L}`, hence
  differs from `ρ|_{G_M}` by a twist by a character of `Gal(L/M)` — of
  order dividing `p`, so with values `p`-th roots of unity.

WHY PRIME DEGREE IS THE SHARPEST JOINT: the twisted trace formula of
Langlands/Arthur–Clozel is run for a cyclic extension of PRIME degree —
that is the case in which the character identity
`Θ_{BC(π)}(g × σ) = Θ_π(N g)` is proved and in which the fibre of base
change is a torsor under the (order-`p`) character group of `Gal(L/M)`.
The general cyclic case is not a separate theorem but the composition of
prime steps, and the general solvable case the composition of cyclic
ones.  This module carries both compositions formally
(`exists_intermediate_of_isCyclic_quotient` for cyclic → prime,
`exists_cyclicRefinement_of_isSolvable` for solvable → cyclic), so this
node is the ONLY remaining citation on the descent route: below it lie
the trace formula and the twisted character identity, not further
group-theoretic bookkeeping.

FULL LITERATURE: Langlands 1980 and Arthur–Clozel 1989 as above;
Barnet-Lamb–Gee–Geraghty–Taylor, *Potential automorphy and change of
weight*, Ann. of Math. 179 (2014), §5.3 (this descent per Brauer piece,
verbatim); Khare–Wintenberger, *Serre's modularity conjecture (I)*,
Invent. Math. 178 (2009), §5; Carayol, Ann. Sci. ÉNS 19 (1986).

PIN AUDIT (2026-07-24/25, inherited): no automorphic-representation
vocabulary exists on this pin, and the reference project's
`cyclic_base_change` (`~/cs/FLT`,
`FLT/GaloisRepresentation/Automorphic.lean`) is itself a sorried
statement phrased through an `IsAutomorphic` predicate on quaternionic
forms — vocabulary this project does not have.  Nothing is vendorable, on
this pin or after a pin-drift audit.

ROUTE AUDIT (2026-07-24, inherited, load-bearing): discharge by vacuity —
`absurd hirr (not_isIrreducible_of_isHardlyRamified_of_five_le …)`, the
route the interface leaves of `Modularity/Interface.lean` take — is NOT
available here: the headline CONSUMES this node (headline ←
`exists_threeadic_compatible_member_of_five_le` ←
`exists_heckeField_system_of_witness` ←
`exists_descended_heckeSystem_of_solvable` ←
`heckeSystemDescendsTo_of_cyclic_step` ←
`heckeSystemDescendsTo_of_prime_cyclic_step` ←
`exists_cuspidalHeckeEigenvalue_of_prime_cyclic_step_of_inert` ← this
leaf), so the vacuity route would be circular.

PLACEMENT: this leaf lives in this module rather than a new one because
it quantifies over `PotentialModularityWitness`, `IsHardlyRamified` and
`GaloisRep.charFrob`, all declared above; a separate module would have
to import this one and then be imported back by it. -/
theorem exists_baseChangeDescentData_of_prime_cyclic_step_of_inert
    {ℓ : ℕ} (hℓodd : Odd ℓ) [Fact ℓ.Prime] (hℓ5 : 5 ≤ ℓ)
    {O : Type u} [CommRing O] [IsDomain O] [TopologicalSpace O]
    [IsTopologicalRing O] [Algebra ℤ_[ℓ] O] [IsLocalRing O]
    [Module.Finite ℤ_[ℓ] O] [IsModuleTopology ℤ_[ℓ] O]
    (hZinj : Function.Injective (algebraMap ℤ_[ℓ] O))
    {ρ : GaloisRep ℚ O (Fin 2 → O)}
    (hrank : Module.rank O (Fin 2 → O) = 2)
    (hρ : IsHardlyRamified hℓodd hrank ρ)
    {k : Type u} [Field k] [Finite k] [Algebra ℤ_[ℓ] k]
    [TopologicalSpace k] [DiscreteTopology k]
    {W : Type v} [AddCommGroup W] [Module k W] [Module.Finite k W]
    [Module.Free k W]
    (hW : Module.rank k W = 2) {ρbar : GaloisRep ℚ k W}
    (hρbar : IsHardlyRamified hℓodd hW ρbar)
    (hirr : ρbar.IsIrreducible)
    (π : O →+* k) (hπsurj : Function.Surjective π)
    (hπ : ∀ (q : ℕ) (hq : q.Prime), q ≠ 2 → q ≠ ℓ →
      (ρ.charFrob hq.toHeightOneSpectrumRingOfIntegersRat).map π =
        ρbar.charFrob hq.toHeightOneSpectrumRingOfIntegersRat)
    (Wit : PotentialModularityWitness ℓ O ρ)
    (C D : Subgroup (Wit.F ≃ₐ[ℚ] Wit.F)) (hCD : C ≤ D)
    (hnormal : (C.subgroupOf D).Normal)
    (p : ℕ) (hp : p.Prime)
    (hcard : Nat.card (D ⧸ C.subgroupOf D) = p)
    (EL : Type u) [Field EL] [NumberField EL]
    (ψL : EL →+* AlgebraicClosure ℚ_[ℓ])
    (SL : Finset (HeightOneSpectrum (NumberField.RingOfIntegers
      (IntermediateField.fixedField C))))
    (PL : HeightOneSpectrum (NumberField.RingOfIntegers
      (IntermediateField.fixedField C)) → Polynomial EL)
    (hPL : ∀ v ∉ SL,
      ((ρ.map (algebraMap ℚ (IntermediateField.fixedField C))).charFrob
        v).map Wit.ιO = (PL v).map ψL) :
    ∃ (EM : Type u) (_ : Field EM) (_ : NumberField EM)
      (ψM : EM →+* AlgebraicClosure ℚ_[ℓ]) (ιM : EL →+* EM),
      (∀ x : EL, ψM (ιM x) = ψL x) ∧
      ∃ (S : Finset (HeightOneSpectrum (NumberField.RingOfIntegers
          (IntermediateField.fixedField D))))
        (a δ : HeightOneSpectrum (NumberField.RingOfIntegers
          (IntermediateField.fixedField D)) → EM)
        (ζ : HeightOneSpectrum (NumberField.RingOfIntegers
          (IntermediateField.fixedField D)) → AlgebraicClosure ℚ_[ℓ]),
        ∀ w ∉ S,
          (∀ v ∉ SL, Ideal.absNorm v.asIdeal ≠ Ideal.absNorm w.asIdeal) →
          ζ w ^ p = 1 ∧
          Wit.ιO (((ρ.map (algebraMap ℚ (IntermediateField.fixedField D))).charFrob
            w).coeff 1) = ζ w * ψM (a w) ∧
          Wit.ιO (((ρ.map (algebraMap ℚ (IntermediateField.fixedField D))).charFrob
            w).coeff 0) = ζ w ^ 2 * ψM (δ w) ∧
          (∀ φ : EM →+* ℂ,
            ‖φ (a w)‖ ≤ 2 * Real.sqrt (Ideal.absNorm w.asIdeal)) :=
  sorry

/-- **Cyclic descent of a CUSPIDAL Hilbert eigensystem, prime degree, at the
NON-SPLIT places** — Arthur–Clozel, *Simple Algebras, Base Change, and the
Advanced Theory of the Trace Formula*, Ann. of Math. Studies 120 (1989),
Ch. 3 Thm 4.2(d); Langlands, *Base Change for GL(2)*, Ann. of Math. Studies
96 (1980).

**PROVEN 2026-07-27 (SECOND OWNER; RE-BASED 2026-07-27 BY THE SEVENTH
OWNER OF THE CITATION)** over the torsor-shaped citation
`exists_baseChangeDescentData_of_prime_cyclic_step_of_inert` immediately
above — which now carries the Ramanujan clause as its fourth conjunct
(finding (8) of its docstring).  It was originally proven over a SECOND,
rival torsor-shaped citation
(`exists_cuspidalBaseChangeDescentData_of_prime_cyclic_step_of_inert`),
which differed from the surviving one only by that clause; adding the
clause upstream made it redundant and it was DELETED, so the descent route
now carries ONE citation for one theorem.  The mod-`ℓ` half of the
arithmetic package (`hW`, `hρbar`, `hirr`, `π`, `hπsurj`, `hπ`) is among
this node's binders because the surviving citation takes it; the consumer
`heckeSystemDescendsTo_of_prime_cyclic_step` already had every one of them
in scope, so nothing upstream had to change.  Note this also REPAIRS the
SOUNDNESS AUDIT below: route (ii) appeals to the module headline, which
needs `hirr`, and `hirr` was not previously a binder here.

What is factored out of the
citation and PROVEN here is the removal of the base-change character twist,
together with the observation that a twist of absolute value `1` cannot move
an archimedean bound.  See the ATOMICITY AUDIT below for why this axis is
available while the cuspidality-peeling axis is not.

**THIS IS THE REPAIRED FORM OF THE CITATION, AND THE POINT OF THE
2026-07-27 CUT-LEVEL REPAIR.**  Thm 4.2(d) takes as input a CUSPIDAL
automorphic `Π` over `L` that is `Gal(L/M)`-invariant, and returns a
cuspidal `π` over `M` whose Hecke eigenvalues are the descended ones.  The
previous statement of this step had NO such object among its binders —
its `L`-side hypothesis was bare `E`-rationality of Frobenius charpolys
against an unconstrained polynomial function — so the citation had nothing
to act on at any stage of the tower but the first.  Here the input is
present and explicit:

* `hSL` gives the eigensystem over `L` in HILBERT-NEWFORM SHAPE
  (`X² − a_w·X + Nw`: parallel weight `2`, trivial nebentypus);
* `hcusp` is CUSPIDALITY, as the Ramanujan–Petersson bound — which
  excludes the Eisenstein eigensystem `a_w = 1 + Nw`, the one object for
  which Thm 4.2(d) fails;
* `hinv` is invariance under `Aut(L/ℚ)`, which contains `Gal(L/M)` because
  `hCD`/`hnormal` make `L/M` Galois — so it delivers exactly the
  `Gal(L/M)`-invariance the theorem requires.

THE COEFFICIENT FIELD GROWS, AND THE CONCLUSION SAYS SO.  The descended
field `EM` is existentially quantified, with an embedding `ιM : EL → EM`
compatible with the embeddings into `ℚ̄_ℓ`.  This is FORCED, not
defensive: at an inert `w` the unique place `W` of `L` above it has
`NW = Nw^p`, and the eigenvalues satisfy the Dickson identity
`a_W = D_p(a_w, Nw)`.  The descent knows `a_W` and must solve for `a_w`,
so `a_w` is a ROOT of a degree-`p` polynomial over `EL` and is in general
of degree `p` over it.  A statement typed at a fixed `Wit.E` at every
stage of the tower is therefore not provable for an arbitrary carrier,
however much automorphic theory is available.

REFUTED ROUTE, RECORDED SO IT IS NOT RE-ATTEMPTED (2026-07-27, checked
numerically in PARI/GP).  A previous audit proposed closing the old
fixed-field statement by an a-priori bound: at an inert `w` the Dickson
relation makes the eigenvalue algebraic of degree `≤ p` over `ψℓ(E)`, and
the Weil bound was supposed to pin such an element into `ψℓ(E)`.  **That
is false.**  Counterexample: `E = ℚ`, `p = 3`, `ℓ = 11`, `Nw = 9`,
`x = 3√3`, `c = 0`.  Then `D₃(x, 9) = x³ − 27x = 81√3 − 81√3 = 0 = ψℓ(c)`;
`x` is algebraic of degree `2 ≤ 3` over `ℚ`; the Weil bound holds since
`3√3 ≈ 5.196 ≤ 6 = 2√9`; and `3 ≡ 5² (mod 11)` is a quadratic residue, so
`√3 ∈ ℚ₁₁` and the witness already lies in `ℚ_ℓ ⊆ E_λ` — adding
`E_λ`-membership therefore does not rescue the route either.  Yet
`3√3 = √27 ∉ ℚ = ψℓ(E)`, so the conclusion fails with every hypothesis
satisfied.  CHECK THAT WOULD REFUTE THIS REFUTATION: exhibit an error in
one of those four verifications — the Dickson evaluation, the degree, the
archimedean bound, or the residue symbol.

The split half of the prime step needs NO automorphic input and is proven
inline in the consumer below: if some good place `v` of `L` has
`Nv = Nw` then `charFrob_M w = charFrob_L v`
(`charFrob_baseChange_eq_of_absNorm_eq`, `charFrob` depending only on the
residue cardinality) and the `L`-side eigensystem already answers, its
value pushed forward along `ιM`.  In particular every place SPLIT in `L/M`
is off this node's plate, so what remains is exactly the INERT half — the
hypothesis `∀ v ∉ SL, Nv ≠ Nw` in the conclusion.

SOUNDNESS AUDIT.  (i) Direct: the classical theorem, whose hypotheses are
now genuinely present among the binders.  (ii) Collapse: the arithmetic
package is classically unsatisfiable (the module headline), so the
statement is classically true for every package.  Route (ii) is a
soundness justification, NOT an available Lean discharge — the headline
CONSUMES this subtree, so `absurd hirr …` is circular here, and every
intermediate link of that chain is declared far below this node and is not
even in scope.

ATOMICITY AUDIT (2026-07-27; AXIS SEARCHED IS NAMED, so the next owner
knows where to start).  The obvious cut is to peel the CUSPIDALITY clause
off the conclusion — leaving a trace-only leaf, pure Arthur–Clozel — and
recover `‖φ(aM w)‖ ≤ 2√(Nw)` afterwards by applying
`weilBound_of_charFrob_baseChange` at `D` to the produced `(EM, ψM, aM)`.
That route is MECHANICALLY available (`weilBound_of_charFrob_baseChange`
is declared above this node and its binders are all present here), and it
was NOT taken, for two reasons, in increasing order of importance:

* it does not typecheck without extra work — `weilBound_of_charFrob_baseChange`
  needs its trace identity `ha` at EVERY `w ∉ S`, whereas the identity here
  is conditional on `w` being inert.  Closing that gap means defining `aM`
  at the split places too (`aM w := ιM (aL v)` for a good `v` of `L` with
  `Nv = Nw`, legitimate by `charFrob_baseChange_eq_of_absNorm_eq`), which
  ABSORBS the automorphy-free split half into a citation leaf — the exact
  opposite of the trace/determinant discipline this module follows.
* more decisively, it would be LESS FAITHFUL to the literature.  Thm 4.2(d)
  returns a CUSPIDAL `π`; cuspidality is part of the theorem's output, not
  a separate obligation to be re-derived from a second citation.  Peeling
  it off would replace one honest citation by two, and would make the
  descended system's cuspidality rest on a Ramanujan statement about a form
  whose existence the first citation had just asserted.

AXIS NOT SEARCHED (recorded 2026-07-27 by the first auditor; TAKEN
2026-07-27 by the second, and it is the axis this node is now cut along):
any route that first constructs the descended automorphic object.  That is
the citation itself, and nothing short of it will do — in particular the
coefficient field `EM` must be ONE number field serving ALL of the
infinitely many places at once, which is an automorphic finiteness
statement with no elementary substitute.

WHAT THE FIRST AUDIT MISSED, AND WHY THE VERDICT WAS ONLY AS WIDE AS ITS
AXIS.  It ranged over cuts of the CONCLUSION — which clause to drop — and
correctly found none.  It did not range over cuts of the CITATION'S SHAPE,
even though this module had already made exactly such a cut one node up:
the (now deleted) trace-only sibling
`exists_heckeTrace_of_prime_cyclic_step_of_inert` was PROVEN over
`exists_baseChangeDescentData_of_prime_cyclic_step_of_inert`, which states
Thm 4.2(d) in the shape the reference actually delivers — descent only up
to the torsor of characters of `Gal(L/M)` — and then removes the twist
formally, using the cyclotomic determinant to force the `p`-th root of
unity `ζ w` into `ψM(EM)`.  The counterexample to "irreducible" was
therefore sitting in the same file, in the sibling that consumes this node.

THE CUT, AND WHY IT IS NOT THE REJECTED ONE.  The rejected route peels the
cuspidality clause OFF the conclusion and re-derives it from a SECOND
citation (`weilBound_of_charFrob_baseChange` at `D`), which both fails to
typecheck without absorbing the automorphy-free split half and replaces one
honest citation by two.  This cut does neither: the citation
`exists_baseChangeDescentData_of_prime_cyclic_step_of_inert` still
RETURNS a cuspidal object — the Ramanujan bound is its fourth conjunct, on
the untwisted eigenvalue `a`, exactly where Thm 4.2(d) puts it — and no
second citation appears anywhere in this proof.  What is factored out is
only the torsor bookkeeping, and that is PROVEN:

* the cyclotomic determinant (`charFrob_baseChange_coeff_zero_eq_absNorm`)
  identifies `(charFrob w).coeff 0` with `Nw`, so `ζ w ^ 2 = ψM (Nw / δ w)`
  lies in `ψM(EM)`; a `p`-th root of unity whose square lies in a subfield
  lies in it (`p = 2` by factoring `ζ² − 1`, `p` odd by
  `ζ = (ζ²)^{(p+1)/2}`), giving `e : EM` with `ψM e = ζ w`;
* `ψM` is injective, so `e ^ p = 1` in `EM` itself, hence `‖φ e‖ = 1` at
  every complex embedding `φ` (`Complex.norm_eq_one_of_pow_eq_one`).  The
  descended eigenvalue `aM w := −(e · a w)` therefore satisfies the value
  identity by construction and inherits the Ramanujan bound from the
  citation's `a` unchanged.

The archimedean half is the load-bearing new observation: the twist is
invisible to the bound because it is a root of unity, which is precisely
why cuspidality can be carried THROUGH the torsor rather than peeled off
it.  CHECK THAT WOULD REFUTE THIS CUT: exhibit a `ζ` with `ζ ^ p = 1`,
`ζ ∈ ψM(EM)`, and a complex embedding `φ` of `EM` with `‖φ (ψM⁻¹ ζ)‖ ≠ 1`.

CONCLUSION (superseding the first audit's): the RESIDUAL leaf
`exists_baseChangeDescentData_of_prime_cyclic_step_of_inert` is
irreducible at this pin and needs Arthur–Clozel; this node is not, and is
now proven over it.

CIRCULARITY GUARD (inherited from pillar β, load-bearing): no discharge
through `Family.lean`, `Lift.lean`, or `Modularity/Interface.lean`. -/
theorem exists_cuspidalHeckeEigenvalue_of_prime_cyclic_step_of_inert
    {ℓ : ℕ} (hℓodd : Odd ℓ) [Fact ℓ.Prime] (hℓ5 : 5 ≤ ℓ)
    {O : Type u} [CommRing O] [IsDomain O] [TopologicalSpace O]
    [IsTopologicalRing O] [Algebra ℤ_[ℓ] O] [IsLocalRing O]
    [Module.Finite ℤ_[ℓ] O] [IsModuleTopology ℤ_[ℓ] O]
    (hZinj : Function.Injective (algebraMap ℤ_[ℓ] O))
    {ρ : GaloisRep ℚ O (Fin 2 → O)}
    (hrank : Module.rank O (Fin 2 → O) = 2)
    (hρ : IsHardlyRamified hℓodd hrank ρ)
    {k : Type u} [Field k] [Finite k] [Algebra ℤ_[ℓ] k]
    [TopologicalSpace k] [DiscreteTopology k]
    {W : Type v} [AddCommGroup W] [Module k W] [Module.Finite k W]
    [Module.Free k W]
    (hW : Module.rank k W = 2) {ρbar : GaloisRep ℚ k W}
    (hρbar : IsHardlyRamified hℓodd hW ρbar)
    (hirr : ρbar.IsIrreducible)
    (π : O →+* k) (hπsurj : Function.Surjective π)
    (hπ : ∀ (q : ℕ) (hq : q.Prime), q ≠ 2 → q ≠ ℓ →
      (ρ.charFrob hq.toHeightOneSpectrumRingOfIntegersRat).map π =
        ρbar.charFrob hq.toHeightOneSpectrumRingOfIntegersRat)
    (Wit : PotentialModularityWitness ℓ O ρ)
    (C D : Subgroup (Wit.F ≃ₐ[ℚ] Wit.F)) (hCD : C ≤ D)
    (hnormal : (C.subgroupOf D).Normal)
    (p : ℕ) (hp : p.Prime)
    (hcard : Nat.card (D ⧸ C.subgroupOf D) = p)
    (EL : Type u) [Field EL] [NumberField EL]
    (ψL : EL →+* AlgebraicClosure ℚ_[ℓ])
    (SL : Finset (HeightOneSpectrum (NumberField.RingOfIntegers
      (IntermediateField.fixedField C))))
    (aL : HeightOneSpectrum (NumberField.RingOfIntegers
      (IntermediateField.fixedField C)) → EL)
    (hSL : ∀ w ∉ SL,
      ((ρ.map (algebraMap ℚ (IntermediateField.fixedField C))).charFrob w).map Wit.ιO =
        (Polynomial.X ^ 2 - Polynomial.C (aL w) * Polynomial.X +
          Polynomial.C ((Ideal.absNorm w.asIdeal : ℕ) : EL)).map ψL)
    (_hcusp : ∀ w ∉ SL, ∀ φ : EL →+* ℂ,
      ‖φ (aL w)‖ ≤ 2 * Real.sqrt (Ideal.absNorm w.asIdeal))
    (_hinv : ∀ τ : IntermediateField.fixedField C ≃ₐ[ℚ] IntermediateField.fixedField C,
      ∀ w ∉ SL, NumberField.finitePlaceEquiv τ.toRingEquiv w ∉ SL →
        aL (NumberField.finitePlaceEquiv τ.toRingEquiv w) = aL w) :
    ∃ (EM : Type u) (_ : Field EM) (_ : NumberField EM)
      (ψM : EM →+* AlgebraicClosure ℚ_[ℓ]) (ιM : EL →+* EM),
      (∀ x : EL, ψM (ιM x) = ψL x) ∧
      ∃ (S : Finset (HeightOneSpectrum (NumberField.RingOfIntegers
          (IntermediateField.fixedField D))))
        (aM : HeightOneSpectrum (NumberField.RingOfIntegers
          (IntermediateField.fixedField D)) → EM),
        ∀ w ∉ S,
          (∀ v ∉ SL, Ideal.absNorm v.asIdeal ≠ Ideal.absNorm w.asIdeal) →
          ψM (aM w) = - Wit.ιO (((ρ.map (algebraMap ℚ
            (IntermediateField.fixedField D))).charFrob w).coeff 1) ∧
          (∀ φ : EM →+* ℂ,
            ‖φ (aM w)‖ ≤ 2 * Real.sqrt (Ideal.absNorm w.asIdeal)) := by
  classical
  -- Arthur–Clozel Ch. 3 Thm 4.2(d), in the shape the reference delivers: the
  -- descended CUSPIDAL eigensystem `a` over a Hecke field `EM ⊇ EL` (the field
  -- GROWS across the step, by Dickson), together with the `Gal(L/M)`-character
  -- twist `ζ` that the torsor leaves undetermined.
  obtain ⟨EM, _, _, ψM, ιM, hψι, S₀, a, δ, ζ, hdata⟩ :=
    exists_baseChangeDescentData_of_prime_cyclic_step_of_inert hℓodd hℓ5
      hZinj hrank hρ hW hρbar hirr π hπsurj hπ Wit C D hCD hnormal p hp hcard
      EL ψL SL
      (fun v => Polynomial.X ^ 2 - Polynomial.C (aL v) * Polynomial.X +
        Polynomial.C ((Ideal.absNorm v.asIdeal : ℕ) : EL)) hSL
  -- the finitely many places over `ℓ`, where `ρ` is ramified and the
  -- cyclotomic-determinant lemma does not apply
  obtain ⟨Sℓ, hSℓ⟩ := exists_finset_forall_natCast_notMem_asIdeal
    (IntermediateField.fixedField D) ℓ (Fact.out : ℓ.Prime).ne_zero
  -- the untwisting element, chosen once for every place at which it exists
  obtain ⟨e, he⟩ : ∃ e : HeightOneSpectrum (NumberField.RingOfIntegers
      (IntermediateField.fixedField D)) → EM,
      ∀ w, (∃ x : EM, ψM x = ζ w) → ψM (e w) = ζ w := by
    refine ⟨fun w => if h : ∃ x : EM, ψM x = ζ w then h.choose else 1, fun w h => ?_⟩
    show ψM (if h : ∃ x : EM, ψM x = ζ w then h.choose else 1) = ζ w
    rw [dif_pos h]
    exact h.choose_spec
  refine ⟨EM, inferInstance, inferInstance, ψM, ιM, hψι, S₀ ∪ Sℓ,
    fun w => -(e w * a w), fun w hw hinert => ?_⟩
  simp only [Finset.mem_union, not_or] at hw
  obtain ⟨hw₀, hwℓ⟩ := hw
  obtain ⟨hζp, hcoeff1, hcoeff0, hbound⟩ := hdata w hw₀ hinert
  -- the constant coefficient is the rational integer `Nw` (cyclotomic determinant)
  have hdet : ((ρ.map (algebraMap ℚ (IntermediateField.fixedField D))).charFrob
      w).coeff 0 = (Ideal.absNorm w.asIdeal : O) :=
    charFrob_baseChange_coeff_zero_eq_absNorm hℓodd hrank hρ _ w (hSℓ w hwℓ)
  have hNw : (Ideal.absNorm w.asIdeal : EM) ≠ 0 :=
    Nat.cast_ne_zero.mpr fun h => w.ne_bot (Ideal.absNorm_eq_zero_iff.mp h)
  have hNψ : ψM ((Ideal.absNorm w.asIdeal : EM)) = ζ w ^ 2 * ψM (δ w) := by
    rw [← hcoeff0, hdet, map_natCast, map_natCast]
  have hδne : ψM (δ w) ≠ 0 := by
    intro h
    rw [h, mul_zero] at hNψ
    exact (map_ne_zero_iff _ ψM.injective).mpr hNw hNψ
  -- the SQUARE of the base-change twist is therefore forced into `ψM(EM)`
  have hζsq : ζ w ^ 2 = ψM ((Ideal.absNorm w.asIdeal : EM) / δ w) := by
    rw [map_div₀, hNψ, mul_div_assoc, div_self hδne, mul_one]
  -- and a `p`-th root of unity whose square lies in a subfield lies in it
  have hex : ∃ x : EM, ψM x = ζ w := by
    rcases hp.eq_two_or_odd' with hp2 | hpodd
    · rw [hp2] at hζp
      have h1 : (ζ w - 1) * (ζ w + 1) = 0 := by linear_combination hζp
      rcases mul_eq_zero.mp h1 with h | h
      · exact ⟨1, by rw [map_one]; linear_combination -h⟩
      · exact ⟨-1, by rw [map_neg, map_one]; linear_combination -h⟩
    · obtain ⟨m, hm⟩ := hpodd
      refine ⟨((Ideal.absNorm w.asIdeal : EM) / δ w) ^ (m + 1), ?_⟩
      rw [map_pow, ← hζsq, ← pow_mul]
      have h2 : 2 * (m + 1) = p + 1 := by omega
      rw [h2, pow_succ, hζp, one_mul]
  have hew : ψM (e w) = ζ w := he w hex
  -- `ψM` is injective, so the untwisting element is a `p`-th root of unity in `EM`
  have hep : e w ^ p = 1 := ψM.injective (by rw [map_pow, hew, hζp, map_one])
  refine ⟨?_, fun φ => ?_⟩
  · -- the value identity: the twist is removed exactly
    rw [map_neg, map_mul, hew, hcoeff1]
  · -- the Ramanujan bound survives the twist, a root of unity having modulus `1`
    have h1 : ‖φ (e w)‖ = 1 :=
      Complex.norm_eq_one_of_pow_eq_one (by rw [← map_pow, hep, map_one]) hp.ne_zero
    rw [map_neg, norm_neg, map_mul, norm_mul, h1, one_mul]
    exact hbound φ

/-- **One PRIME-degree cyclic step of solvable base change** (PROVEN,
2026-07-25, from the cuspidal-descent citation
`exists_cuspidalHeckeEigenvalue_of_prime_cyclic_step_of_inert` and the
cyclotomic determinant already established in this module.  NOTE: it was
proven over a trace-only citation `exists_heckeTrace_of_prime_cyclic_step`
until the 2026-07-27 cut-level repair rerouted it through the cuspidal
form; that trace pair thereby lost every application and was DELETED as
free-floating the same day.  The paragraphs below that name the trace
citation as the source describe the SPLIT, which is unchanged, not the
current call site):
if the eigensystem of `ρ` descends
to the fixed field `L = F^C`, and `C ≤ D` is normal with quotient `D/C`
of PRIME order `p` (equivalently: `L/M` is a cyclic Galois extension of
degree `p`, where `M = F^D`), then the eigensystem descends to `M`.

ASSEMBLY (2026-07-25) — THE TRACE/DETERMINANT SPLIT.  A rank-`2`
Frobenius characteristic polynomial is monic of degree `2`, hence
determined by its two lower coefficients, and the two carry completely
different arithmetic:

* the CONSTANT coefficient is the determinant, and `ρ` is hardly
  ramified, so its determinant is the `ℓ`-adic cyclotomic character; at a
  place `w ∤ ℓ` the cyclotomic character takes the value `Nw` at
  Frobenius, a RATIONAL INTEGER, which lies in every number field.  This
  is `charFrob_baseChange_coeff_zero_eq_absNorm` (proven earlier in this
  module over the pure algebraic-number-theory leaf
  `cyclotomicCharacter_adicArithFrob_base_eq_absNorm`), applied off the
  finite set of places over `ℓ` supplied by
  `exists_finset_forall_natCast_notMem_asIdeal`.  NO automorphic input.
* the LINEAR coefficient is `−a_w`, the Hecke eigenvalue of the descended
  newform.  That is the whole automorphic content of cyclic base change
  and descent, and it is exactly what the citation
  `exists_baseChangeDescentData_of_prime_cyclic_step_of_inert` supplies,
  through `exists_cuspidalHeckeEigenvalue_of_prime_cyclic_step_of_inert`.

The assembly is then formal: choose `a w ∈ E` with
`ψℓ (a w) = ιO (coeff 1)` off the citation's bad set, put
`P w = X² + a w · X + Nw`, and check the required identity
`(charFrob w).map ιO = (P w).map ψℓ` coefficientwise — degrees `0` and
`1` are the two inputs, degree `2` is monicity
(`LinearMap.charpoly_monic`) and everything above is zero
(`LinearMap.charpoly_natDegree` with `finrank O (Fin 2 → O) = 2`).

WHAT THIS BUYS.  Before the split, the whole quadratic was a literature
citation at EVERY stage of the descent tower; now the determinant half is
discharged at every stage by the cyclotomic determinant clause of `hρ`,
and the residual citation is one scalar per place.  It is the same split
the Carayol/Shimura sub-cut of this module makes at the base field `F`,
propagated down the tower.

The classical content of the prime step — three moves: cyclic ascent,
`Gal(L/M)`-invariance, cyclic descent by the twisted character identity —
is carried in full by the trace citation's docstring, together with the
literature and the PIN, SOUNDNESS, VACUITY, ROUTE and CIRCULARITY audits.

CIRCULARITY GUARD (inherited from pillar β, load-bearing): no discharge
through `Family.lean`, `Lift.lean`, or `Modularity/Interface.lean`. -/

theorem heckeSystemDescendsTo_of_prime_cyclic_step
    {ℓ : ℕ} (hℓodd : Odd ℓ) [Fact ℓ.Prime] (hℓ5 : 5 ≤ ℓ)
    {O : Type u} [CommRing O] [IsDomain O] [TopologicalSpace O]
    [IsTopologicalRing O] [Algebra ℤ_[ℓ] O] [IsLocalRing O]
    [Module.Finite ℤ_[ℓ] O] [IsModuleTopology ℤ_[ℓ] O]
    (hZinj : Function.Injective (algebraMap ℤ_[ℓ] O))
    {ρ : GaloisRep ℚ O (Fin 2 → O)}
    (hrank : Module.rank O (Fin 2 → O) = 2)
    (hρ : IsHardlyRamified hℓodd hrank ρ)
    {k : Type u} [Field k] [Finite k] [Algebra ℤ_[ℓ] k]
    [TopologicalSpace k] [DiscreteTopology k]
    {W : Type v} [AddCommGroup W] [Module k W] [Module.Finite k W]
    [Module.Free k W]
    (hW : Module.rank k W = 2) {ρbar : GaloisRep ℚ k W}
    (hρbar : IsHardlyRamified hℓodd hW ρbar)
    (hirr : ρbar.IsIrreducible)
    (π : O →+* k) (hπsurj : Function.Surjective π)
    (hπ : ∀ (q : ℕ) (hq : q.Prime), q ≠ 2 → q ≠ ℓ →
      (ρ.charFrob hq.toHeightOneSpectrumRingOfIntegersRat).map π =
        ρbar.charFrob hq.toHeightOneSpectrumRingOfIntegersRat)
    (Wit : PotentialModularityWitness ℓ O ρ)
    (C D : Subgroup (Wit.F ≃ₐ[ℚ] Wit.F)) (hCD : C ≤ D)
    (hnormal : (C.subgroupOf D).Normal)
    (p : ℕ) (hp : p.Prime)
    (hcard : Nat.card (D ⧸ C.subgroupOf D) = p)
    (hC : HeckeSystemDescendsTo Wit C) :
    HeckeSystemDescendsTo Wit D := by
  classical
  -- (i) the cuspidal, `Gal(L/M)`-invariant eigensystem over `L = F^C`
  obtain ⟨EL, _, _, ψL, ιL, hψιL, SL, aL, h1L, h2L, h3L⟩ := hC
  -- (ii) the automorphic citation, now with its input among the binders; it
  -- returns the descended CUSPIDAL eigensystem over `M = F^D`, over a Hecke
  -- field `EM ⊇ EL` (the field grows: see the Dickson paragraph there)
  obtain ⟨EM, _, _, ψM, ιM, hψιM, Sin, aM, hAC⟩ :=
    exists_cuspidalHeckeEigenvalue_of_prime_cyclic_step_of_inert hℓodd hℓ5 hZinj
      hrank hρ hW hρbar hirr π hπsurj hπ Wit C D hCD hnormal p hp hcard
      EL ψL SL aL h1L h2L h3L
  -- (iii) bookkeeping finite sets over `M`
  obtain ⟨Sl, hSl⟩ := exists_finset_forall_natCast_notMem_asIdeal
    (IntermediateField.fixedField D) ℓ (Fact.out : ℓ.Prime).ne_zero
  obtain ⟨S2, hS2⟩ := exists_finset_forall_natCast_notMem_asIdeal
    (IntermediateField.fixedField D) 2 (by norm_num)
  have hSun : ∀ v ∉ ({Nat.prime_two.toHeightOneSpectrumRingOfIntegersRat,
      (Fact.out : ℓ.Prime).toHeightOneSpectrumRingOfIntegersRat} :
        Finset (HeightOneSpectrum (NumberField.RingOfIntegers ℚ))),
      ρ.IsUnramifiedAt v := by
    intro v hv
    obtain ⟨q, hq, rfl⟩ :=
      IsHardlyRamified.exists_prime_eq_toHeightOneSpectrumRingOfIntegersRat v
    refine hρ.isUnramified q hq ⟨?_, ?_⟩
    · rintro rfl
      exact hv (Finset.mem_insert_self _ _)
    · rintro rfl
      exact hv (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
  obtain ⟨T, hT⟩ := GaloisRep.exists_finset_isUnramifiedAt_map
    (L := IntermediateField.fixedField D) ρ _ hSun
  set Sfull := ((Sin ∪ Sl) ∪ S2) ∪ T with hSfull
  have hdecomp : ∀ w : HeightOneSpectrum (NumberField.RingOfIntegers
      (IntermediateField.fixedField D)), w ∉ Sfull →
      w ∉ Sin ∧ w ∉ Sl ∧ w ∉ S2 ∧ w ∉ T := by
    intro w hw
    rw [hSfull] at hw
    simp only [Finset.mem_union, not_or] at hw
    exact ⟨hw.1.1.1, hw.1.1.2, hw.1.2, hw.2⟩
  -- (iv) THE TRACE/SPLIT DICHOTOMY.  At a place of `M` whose residue
  -- cardinality is realized by a good place of `L`, the two Frobenius
  -- charpolys coincide and the `L`-side eigensystem answers with NO
  -- automorphic input, its value pushed forward along `ιM`.  What is left is
  -- the inert half, which is exactly the citation's plate.
  have key : ∀ w : HeightOneSpectrum (NumberField.RingOfIntegers
      (IntermediateField.fixedField D)), ∃ x : EM, w ∉ Sfull →
      ψM x = - Wit.ιO (((ρ.map (algebraMap ℚ
        (IntermediateField.fixedField D))).charFrob w).coeff 1) ∧
      (∀ φ : EM →+* ℂ,
        ‖φ x‖ ≤ 2 * Real.sqrt (Ideal.absNorm w.asIdeal)) := by
    intro w
    by_cases hw : w ∈ Sfull
    · exact ⟨0, fun h => absurd hw h⟩
    · obtain ⟨hwin, hwl, hw2, hwT⟩ := hdecomp w hw
      by_cases hsplit : ∃ vL ∉ SL, Ideal.absNorm vL.asIdeal = Ideal.absNorm w.asIdeal
      · obtain ⟨vL, hvS, hvnorm⟩ := hsplit
        refine ⟨ιM (aL vL), fun _ => ⟨?_, ?_⟩⟩
        · rw [hψιM]
          have heq := charFrob_baseChange_eq_of_absNorm_eq hℓodd hrank hρ
            (IntermediateField.fixedField D) (IntermediateField.fixedField C) w vL
            (hS2 w hw2) (hSl w hwl) hvnorm
          have h := h1L vL hvS
          rw [heq] at h
          have hc1 := congrArg
            (fun P : Polynomial (AlgebraicClosure ℚ_[ℓ]) => P.coeff 1) h
          simp only [Polynomial.coeff_map] at hc1
          have hcc : (Polynomial.X ^ 2 - Polynomial.C (aL vL) * Polynomial.X +
              Polynomial.C ((Ideal.absNorm vL.asIdeal : ℕ) : EL)).coeff 1 =
              -(aL vL) := by simp
          rw [hcc, map_neg] at hc1
          rw [hc1]
          ring
        · intro φ
          have hb := h2L vL hvS (φ.comp ιM)
          rw [hvnorm] at hb
          simpa using hb
      · push Not at hsplit
        exact ⟨aM w, fun _ => hAC w hwin hsplit⟩
  choose a ha using key
  refine ⟨EM, inferInstance, inferInstance, ψM, ιM.comp ιL,
    fun x => by rw [RingHom.comp_apply, hψιM, hψιL], Sfull, a, ?_, ?_, ?_⟩
  · -- (1) the eigensystem, in Hilbert-newform shape.  The determinant half is
    -- the cyclotomic value `Nw` and needs no automorphic input.
    intro w hw
    have hfin : Module.finrank O (Fin 2 → O) = 2 :=
      Module.finrank_eq_of_rank_eq hrank
    have hmonic :
        ((ρ.map (algebraMap ℚ (IntermediateField.fixedField D))).charFrob w).Monic := by
      rw [GaloisRep.charFrob_eq_charpoly_globalFrob]
      exact LinearMap.charpoly_monic _
    have hdeg :
        ((ρ.map (algebraMap ℚ (IntermediateField.fixedField D))).charFrob
          w).natDegree = 2 := by
      rw [GaloisRep.charFrob_eq_charpoly_globalFrob, LinearMap.charpoly_natDegree, hfin]
    have hwl : (ℓ : NumberField.RingOfIntegers (IntermediateField.fixedField D))
        ∉ w.asIdeal := hSl w (hdecomp w hw).2.1
    have hdet := charFrob_baseChange_coeff_zero_eq_absNorm hℓodd hrank hρ
      (IntermediateField.fixedField D) w hwl
    refine Polynomial.ext fun n => ?_
    rw [Polynomial.coeff_map, Polynomial.coeff_map]
    match n with
    | 0 =>
      rw [hdet]
      simp
    | 1 =>
      have hc : (Polynomial.X ^ 2 - Polynomial.C (a w) * Polynomial.X +
          Polynomial.C ((Ideal.absNorm w.asIdeal : ℕ) : EM)).coeff 1 = -(a w) := by
        simp
      rw [hc, map_neg, (ha w hw).1]
      ring
    | 2 =>
      have h2 : ((ρ.map (algebraMap ℚ (IntermediateField.fixedField D))).charFrob
          w).coeff 2 = 1 := by
        have h := hmonic.coeff_natDegree
        rwa [hdeg] at h
      rw [h2]
      simp
    | (m + 3) =>
      rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [hdeg]; omega)]
      simp [Polynomial.coeff_X_pow]
  · -- (2) CUSPIDALITY, propagated by the citation
    intro w hw
    exact (ha w hw).2
  · -- (3) Gal-INVARIANCE, PROVEN afresh over `M` rather than propagated
    intro τ w hw hτw
    have hcf := GaloisRep.charFrob_map_algEquiv ρ τ w (hT w (hdecomp w hw).2.2.2)
    refine ψM.injective ?_
    rw [(ha _ hτw).1, (ha _ hw).1, hcf]

/-- **One cyclic step of solvable base change** (PROVEN, 2026-07-25, from
the prime-degree step `heckeSystemDescendsTo_of_prime_cyclic_step` — now
itself PROVEN, over the cuspidal-descent citation
`exists_baseChangeDescentData_of_prime_cyclic_step_of_inert` —
and the group-theoretic dévissage
`exists_intermediate_of_isCyclic_quotient`): if the eigensystem of `ρ`
descends to the fixed field `L = F^C`, and `C ≤ D` is normal with CYCLIC
quotient `D/C` (equivalently: `L/M` is a cyclic Galois extension, where
`M = F^D`), then the eigensystem descends to `M`.

ASSEMBLY (2026-07-25): the theorem of Langlands/Arthur–Clozel is about a
cyclic extension of PRIME degree — that is the degree in which the
twisted trace formula is run and the character identity proved — and the
general cyclic case is the composition of prime steps. So this node is
now the SECOND dévissage of the descent, above the solvable one: the
cyclic quotient `D/C` is refined into prime steps by
`exists_intermediate_of_isCyclic_quotient` (pure finite group theory,
proven here), and the eigensystem is carried up one prime step at a time
by `heckeSystemDescendsTo_of_prime_cyclic_step` (proven, over the
cuspidal-descent citation
`exists_baseChangeDescentData_of_prime_cyclic_step_of_inert`). Formally
the recursion is a strong induction on `#D`: either `C = D` and the
hypothesis `hC` already IS the conclusion, or one obtains an
intermediate `C ≤ E ≤ D` with `#E < #D`, `E/C` cyclic and `D/E` of prime
order, applies the induction hypothesis to `E` and the prime-degree
citation to `E ≤ D`. As in `exists_descended_heckeSystem_of_solvable`,
the fixed fields are taken as restrictions from `ℚ` at every stage, so
the induction needs no compatibility of restrictions along the tower —
indeed the intermediate subgroups never appear as fields at all, only as
subgroups fed back into `HeckeSystemDescendsTo`.

The classical content of the prime step, retained here for orientation
(the sorried node carries it in full), is three moves — the joints of the
literature argument, in order:

* *Cyclic ascent (base change).* `L/M` is cyclic of prime power degree
  after refinement; `Gal(L/M) ≅ D/C` acts on the automorphic side, and
  Langlands' cyclic base change `BC_{L/M}` is defined on the
  cuspidal spectrum of `GL(2)/M` and characterized by the Arthur–Clozel
  character identity below. The descended system over `L` (hypothesis
  `hC`) is, through Carayol local-global compatibility, the eigensystem
  of a Hilbert newform `f_L` over `L`.
* *`Gal(L/M)`-invariance.* `f_L`'s Galois representation is
  `ρ|_{G_L}` — the restriction to `G_L` of the representation
  `ρ|_{G_M}` of the LARGER group `G_M` — hence visibly
  `Gal(L/M)`-invariant: for `σ ∈ Gal(L/M)`, `f_L^σ` has the same
  Frobenius eigenvalues as `f_L` at almost all places, so `f_L^σ = f_L`
  by strong multiplicity one.
* *Cyclic descent (the Arthur–Clozel character identity).* A
  `Gal(L/M)`-invariant cuspidal automorphic representation of
  `GL(2)/L` is in the image of base change from `GL(2)/M`, and its
  fibre is a torsor under the characters of `Gal(L/M)` (Langlands,
  *Base Change for GL(2)*, Ann. of Math. Studies 96 (1980), Ch. 2 and
  Thm 4.2; Arthur–Clozel, *Simple Algebras, Base Change, and the
  Advanced Theory of the Trace Formula*, Ann. of Math. Studies 120
  (1989), Ch. 3 Thm 4.2 and Ch. 1 §6 for the twisted character
  identity `Θ_{BC(π)}(g × σ) = Θ_π(N g)` that defines and characterizes
  the transfer). So there is a Hilbert newform `f_M` over `M` with
  `BC_{L/M}(f_M) = f_L`; its `ℓ`-adic representation restricted to
  `G_L` agrees with `ρ|_{G_L}`, hence differs from `ρ|_{G_M}` by a
  twist by a character of `Gal(L/M)` — a finite-order character, whose
  values are roots of unity.

Carayol's local-global compatibility over `M` then identifies the
Frobenius characteristic polynomials of the (twisted) `f_M`-system with
Hecke polynomials; their coefficients — Hecke eigenvalues of `f_M`
enlarged by the twisting-character values — lie in the carrier's `E`,
which is, per the consumers' docstrings, the Hecke field OF THE
DESCENDED system, the normalization that absorbs exactly these
enlargements. The new bad set collects the places of `M` below the bad
set of the `L`-system, the places over `2`, `3`, `ℓ`, and the places
ramified in `L/M`.

Literature: Langlands 1980 and Arthur–Clozel 1989 as above (the cyclic
prime-degree case is the theorem; the general solvable case is the
dévissage carried out formally by the assembly
`exists_descended_heckeSystem_of_solvable` over
`exists_cyclicRefinement_of_isSolvable`);
Barnet-Lamb–Gee–Geraghty–Taylor, *Potential automorphy and change of
weight*, Ann. of Math. 179 (2014), §5.3 (this descent per Brauer piece,
verbatim); Khare–Wintenberger, *Serre's modularity conjecture (I)*,
Invent. Math. 178 (2009), §5; Carayol, Ann. Sci. ÉNS 19 (1986).

PIN AUDIT (2026-07-24): no automorphic-representation vocabulary exists
on this pin, and the reference project's `cyclic_base_change`
(`~/cs/FLT`) is itself a sorried statement in a vocabulary this project
does not have (see the `HeckeSystemDescendsTo` docstring); nothing is
vendorable. The terminal citation node of the descent is now the
prime-degree step below it: beneath THAT lie the trace formula and the
twisted character identity, not further group-theoretic bookkeeping.

SOUNDNESS AUDIT (both ways, 2026-07-24/25): unchanged in substance, and
now discharged rather than assumed: the residual sorry is the
prime-degree node, which carries the identical hypothesis package (in
particular route (ii), collapse by unsatisfiability of the hypotheses,
remains available there exactly as it was here — the sharpening is of
the group-theoretic hypothesis only).

ROUTE AUDIT (2026-07-24): as for the base leaf above, discharge by
vacuity through `not_isIrreducible_of_isHardlyRamified_of_five_le` is
NOT available — the headline consumes this node, so that route is
circular. The classical route above is the one to follow.

CIRCULARITY GUARD (inherited from pillar β, load-bearing): no
discharge through `Family.lean`, `Lift.lean`, or
`Modularity/Interface.lean`. -/
theorem heckeSystemDescendsTo_of_cyclic_step
    {ℓ : ℕ} (hℓodd : Odd ℓ) [Fact ℓ.Prime] (hℓ5 : 5 ≤ ℓ)
    {O : Type u} [CommRing O] [IsDomain O] [TopologicalSpace O]
    [IsTopologicalRing O] [Algebra ℤ_[ℓ] O] [IsLocalRing O]
    [Module.Finite ℤ_[ℓ] O] [IsModuleTopology ℤ_[ℓ] O]
    (hZinj : Function.Injective (algebraMap ℤ_[ℓ] O))
    {ρ : GaloisRep ℚ O (Fin 2 → O)}
    (hrank : Module.rank O (Fin 2 → O) = 2)
    (hρ : IsHardlyRamified hℓodd hrank ρ)
    {k : Type u} [Field k] [Finite k] [Algebra ℤ_[ℓ] k]
    [TopologicalSpace k] [DiscreteTopology k]
    {W : Type v} [AddCommGroup W] [Module k W] [Module.Finite k W]
    [Module.Free k W]
    (hW : Module.rank k W = 2) {ρbar : GaloisRep ℚ k W}
    (hρbar : IsHardlyRamified hℓodd hW ρbar)
    (hirr : ρbar.IsIrreducible)
    (π : O →+* k) (hπsurj : Function.Surjective π)
    (hπ : ∀ (q : ℕ) (hq : q.Prime), q ≠ 2 → q ≠ ℓ →
      (ρ.charFrob hq.toHeightOneSpectrumRingOfIntegersRat).map π =
        ρbar.charFrob hq.toHeightOneSpectrumRingOfIntegersRat)
    (Wit : PotentialModularityWitness ℓ O ρ)
    (C D : Subgroup (Wit.F ≃ₐ[ℚ] Wit.F)) (hCD : C ≤ D)
    (hnormal : (C.subgroupOf D).Normal)
    (hcyclic : IsCyclic (D ⧸ C.subgroupOf D))
    (hC : HeckeSystemDescendsTo Wit C) :
    HeckeSystemDescendsTo Wit D := by
  classical
  -- strong induction on the order of the upper group, refining the cyclic
  -- quotient one prime step at a time
  have key : ∀ N : ℕ, ∀ D' : Subgroup (Wit.F ≃ₐ[ℚ] Wit.F),
      Nat.card D' ≤ N → C ≤ D' →
      ∀ _hn : (C.subgroupOf D').Normal, IsCyclic (D' ⧸ C.subgroupOf D') →
      HeckeSystemDescendsTo Wit D' := by
    intro N
    induction N with
    | zero =>
      intro D' hcardD' _ _ _
      exact absurd hcardD' (Nat.not_le.mpr Nat.card_pos)
    | succ M ih =>
      intro D' hcardD' hCD' hnorm' hcyc'
      by_cases hEq : C = D'
      · exact hEq ▸ hC
      · obtain ⟨E, p, hp, hCE, hED', hlt, ⟨hnE, hcycE⟩, ⟨hnD, hcardD⟩⟩ :=
          exists_intermediate_of_isCyclic_quotient C D' hCD' hnorm' hcyc' hEq
        exact heckeSystemDescendsTo_of_prime_cyclic_step hℓodd hℓ5 hZinj
          hrank hρ hW hρbar hirr π hπsurj hπ Wit E D' hED' hnD p hp hcardD
          (ih E (by omega) hCE hnE hcycE)
  exact key (Nat.card D) D le_rfl hCD hnormal hcyclic

/-- **Descent-closure of the carrier's Hecke field** (PROVEN 2026-07-27 —
a one-line projection onto `PotentialModularityWitness.descentClosed`;
see the RESOLUTION note at the end of this docstring, which supersedes
the analysis below).

STATEMENT.  If the eigensystem of `ρ|_{G_K}`, `K = F^H`, is realized over
SOME number field `E'` containing `Wit.E` (through `ι`, compatibly with
the embeddings into `ℚ̄_ℓ`), then away from a further finite set its
values are already in the image of `Wit.E`.

WHY IT IS NEEDED, AND WHY IT LIVES HERE.  After the 2026-07-27 repair the
descent datum `HeckeSystemDescendsTo` carries an EXISTENTIAL coefficient
field, because the Hecke field provably grows down the Brauer tower (the
Dickson identity `a_W = D_p(a_w, Nw)` makes the descended eigenvalue a
root, of degree up to `p`, over the previous field).  That is the correct
statement of the descent.  But the DOWNSTREAM Brauer gluing
(`exists_heckeField_system_of_witness_of_pieces`) forms a single rational
combination `Σᵢ cᵢ · (traces)` of the `n` induced pieces, so it must read
every piece in ONE field.  This leaf is the bridge, and it is exactly the
assertion the witness docstring already makes: `E` "is to be understood
as a number field chosen large enough for the whole descent — e.g. the
compositum of the Hecke fields of all forms arising in the Brauer
decomposition, a FINITE compositum and hence still a number field."

THE HONEST ACCOUNTING, so nobody downstream misreads this.  That
understanding is NOT among the hypotheses of `PotentialModularityWitness`:
the structure constrains `E` only by `Field` and `NumberField`, and every
leaf here universally quantifies over the carrier.  So for an ARBITRARY
carrier this leaf is not derivable — it is a genuine additional demand on
`E`, and it is the price of keeping the downstream statements typed at
`Wit.E`.

PROPER LONG-TERM REPAIR (not this owner's to make): add descent-closure
as a FIELD of `PotentialModularityWitness`, discharged by the producing
leaf `exists_potentialModularityWitness_of_five_le`, which is entitled to
make the enlarged choice — the witness docstring already argues that
enlarging `E` costs nothing, since `ψℓ`, `ψ₃` extend along any finite
extension and `modularF`, `matchF₃` are preserved by functoriality of
`Polynomial.map`.  With that field present this leaf becomes a one-line
projection.  Stated here, where it is consumed, because the structure is
being edited by other owners.

SOUNDNESS AUDIT.  (i) Direct: true for the carrier the inhabitation leaf
produces, by the enlarged choice of `E` just described.  (ii) Collapse:
the arithmetic hypothesis package is classically unsatisfiable (the module
headline), so the statement is classically true for every package.

**CORRECTION TO ROUTE (ii), 2026-07-27 — IT DOES NOT APPLY TO THIS LEAF,
AND THAT IS THE WHOLE POINT.**  Route (ii) is inherited verbatim from the
neighbouring leaves, where it is correct.  Here it is not, and the check
takes one look at the binders: this declaration carries NO arithmetic
package at all.  There is no `hℓodd`, no `hℓ5`, no `IsHardlyRamified`, no
irreducibility hypothesis, no `[Algebra ℤ_[ℓ] O]` — only `Fact ℓ.Prime`, a
topological ring `O`, a representation `ρ`, and a witness for it.  So there
is nothing here for the module headline to contradict, and route (ii) is
not merely "unavailable as a Lean discharge" (which is what the sibling
audits mean) but INAPPLICABLE: it does not even establish classical truth.

Consequently this leaf has exactly ONE soundness justification, route (i),
and route (i) is a statement about the carrier the inhabitation leaf
CHOOSES — not about the arbitrary carrier this leaf quantifies over.  That
is precisely the gap the "HONEST ACCOUNTING" paragraph above describes, and
it is why the repair below is not a matter of taste.

WHAT WOULD REFUTE THIS CORRECTION: exhibit an arithmetic hypothesis among
the binders of `heckeField_descentClosed_of_witness`.  There is none.

REPORTED UPWARD 2026-07-27 (agent in `flt-lean-126`, dispatched at this
leaf): the conclusion is that this obligation MUST move into
`PotentialModularityWitness` as a field — it cannot be discharged where it
stands, and no amount of work at this node will change that.  Concretely
the field wanted is, for every subgroup `H` and every realization of the
descended system over a number field `E' ⊇ E`, that the eigenvalue function
takes values in `ι '' E` away from a finite set; equivalently, and more
usably, that `E` is descent-closed in the sense of the DESCENT-CLOSURE note
of the structure's own docstring.  `exists_potentialModularityWitness_of_five_le`
is entitled to supply it, since enlarging `E` to a finite compositum
preserves every existing field of the structure (`ψℓ`, `ψ₃` extend along a
finite extension; `modularF`, `matchF₃` are preserved by functoriality of
`Polynomial.map`).  With the field present this leaf is a one-line
projection.  The structure has another owner, so it was NOT moved here.

**RESOLUTION 2026-07-27 — THE MOVE WAS MADE; THIS LEAF IS NOW PROVEN.**
`PotentialModularityWitness` gained the field `descentClosed`, stated
exactly as the conclusion below, and this declaration is its projection.
The obligation itself did not vanish — it moved to where the carrier's
`E` is CHOSEN, which is the only place it can be honestly discharged:
the single inhabitation site
`exists_potentialModularityWitness_of_five_le` now enlarges the Hecke
block through the new sorried citation `exists_descentClosed_heckePackage`
(step (ii''), in the same style as the bad-set enlargement of step (ii')),
and hands the enlarged, descent-closed field to the carrier.  That
citation carries the FULL arithmetic package, so both soundness routes
(i) and (ii) are available to it — which is what the CORRECTION above
observes was NOT true here.  No consumer of this declaration changed:
`exists_descended_heckeSystem_of_solvable` still applies it with the same
arguments.  The paragraphs above are retained as the record of why the
move was necessary. -/
theorem heckeField_descentClosed_of_witness {ℓ : ℕ} [Fact ℓ.Prime]
    {O : Type u} [CommRing O] [TopologicalSpace O] [IsTopologicalRing O]
    {ρ : GaloisRep ℚ O (Fin 2 → O)}
    (Wit : PotentialModularityWitness ℓ O ρ)
    (H : Subgroup (Wit.F ≃ₐ[ℚ] Wit.F))
    (E' : Type u) [Field E'] [NumberField E']
    (ψ : E' →+* AlgebraicClosure ℚ_[ℓ]) (ι : Wit.E →+* E')
    (hψι : ∀ x : Wit.E, ψ (ι x) = Wit.ψℓ x)
    (S : Finset (HeightOneSpectrum (NumberField.RingOfIntegers
      (IntermediateField.fixedField H))))
    (a : HeightOneSpectrum (NumberField.RingOfIntegers
      (IntermediateField.fixedField H)) → E')
    (h1 : ∀ w ∉ S,
      ((ρ.map (algebraMap ℚ (IntermediateField.fixedField H))).charFrob w).map Wit.ιO =
        (Polynomial.X ^ 2 - Polynomial.C (a w) * Polynomial.X +
          Polynomial.C ((Ideal.absNorm w.asIdeal : ℕ) : E')).map ψ) :
    ∃ (S' : Finset (HeightOneSpectrum (NumberField.RingOfIntegers
        (IntermediateField.fixedField H))))
      (b : HeightOneSpectrum (NumberField.RingOfIntegers
        (IntermediateField.fixedField H)) → Wit.E),
      ∀ w, w ∉ S → w ∉ S' → ι (b w) = a w :=
  Wit.descentClosed H E' ψ ι hψι S a h1

/-- **Solvable base change — the descended Hecke system over a fixed
field** (PROVEN; the per-induced-piece citation leaf of the
`ℓ`-adic Brauer descent): for a SOLVABLE subgroup `H ≤ Gal(F/ℚ)` of
the potential-modularity carrier, the Hilbert eigensystem of the
witness descends from `F` to the fixed field `K = F^H`: the Frobenius
characteristic polynomials of `ρ|_{G_K}` at almost all places of `K`
are `E`-coefficient polynomials through `ιO`/`ψℓ`.

Classically: the Hilbert newform `f` over `F` attached to `ρ|_{G_F}`
(fields `modularF`/`heckeF` of the carrier) is `Gal(F/K)`-invariant,
because its Galois representation `ρ|_{G_F}` visibly extends to `G_K`
(it is the restriction of `ρ`). `Gal(F/K) ≅ H` is solvable, so
Langlands' cyclic base change and descent, iterated along a solvable
chain (Langlands, *Base Change for GL(2)*, Ann. of Math. Studies 96
(1980); Arthur–Clozel, *Simple Algebras, Base Change, and the Advanced
Theory of the Trace Formula*, Ann. of Math. Studies 120 (1989)),
produce a Hilbert newform `f_K` over `K` whose base change to `F` is
`f`; its attached `ℓ`-adic representation restricted to `G_F` agrees
with `ρ|_{G_F}`, so it differs from `ρ|_{G_K}` by a twist by a finite
character of `Gal(F/K)`. Carayol's local–global compatibility over `K`
identifies the Frobenius characteristic polynomials of the twisted
`f_K`-system with Hecke polynomials; their coefficients — Hecke
eigenvalues of `f_K` enlarged by the twisting-character values, roots
of unity — lie in the carrier's `E` (which is, per the consumer's
docstring parenthetical, the Hecke field OF THE DESCENDED system, the
normalization that absorbs exactly these enlargements). The bad set
`S` collects the places of `K` dividing the level, the places over
`2`, `3`, `ℓ`, and the places ramified in `F/K`.

Literature: Langlands 1980 and Arthur–Clozel 1989 (solvable base
change and descent for `GL(2)`); Barnet-Lamb–Gee–Geraghty–Taylor,
*Potential automorphy and change of weight*, Ann. of Math. 179
(2014), §5.3 (this descent per Brauer piece, verbatim);
Khare–Wintenberger, *Serre's modularity conjecture (I)*, Invent.
Math. 178 (2009), §5; Carayol, Ann. Sci. ÉNS 19 (1986) (local–global
compatibility over the totally real fixed field).

SOUNDNESS AUDIT (both ways, 2026-07-24): (i) direct — for the carrier
produced by the inhabitation leaf this is the chain above, with the
Hecke-field enlargements landing in `E` by the carrier's
normalization; for an abstract carrier the abstract-quantification
caveat of pillar β applies, and (ii) collapse — the hypothesis set
(an irreducible hardly ramified mod-`ℓ` representation, `ℓ ≥ 5`) is
classically unsatisfiable (headline below), so the statement is
classically true for every package.

CIRCULARITY GUARD (inherited from pillar β, load-bearing): no
discharge through `Family.lean`, `Lift.lean`, or
`Modularity/Interface.lean`.

ASSEMBLY (2026-07-24, PROVEN): the solvable descent is the DÉVISSAGE of
the literature made formal — the theorem of Langlands/Arthur–Clozel is
about a CYCLIC step, and the solvable case is reached by iterating it
along a cyclic refinement. So:
`exists_cyclicRefinement_of_isSolvable` (pure finite group theory: the
solvable `H` is the top of a chain `⊥ = C₀ ≤ ⋯ ≤ Cₙ = H` with each step
normal with cyclic quotient) + `heckeSystemDescendsTo_bot` (the base of
the chain: the carrier's own clause `Wit.modularF` transported from `F`
to `F^⊥`, a formal-transport leaf with no arithmetic content) +
`heckeSystemDescendsTo_of_cyclic_step` (one cyclic step of base change
and descent), glued by induction on the chain index through the shared
shape `HeckeSystemDescendsTo`. The fixed fields are taken as
restrictions from `ℚ` at every stage, so the induction needs no
compatibility of restrictions along the tower.
Those three nodes are the residual frontier of this node; the
circularity guard above binds the arithmetic ones (the refinement
leaf is pure group theory — nothing arithmetic to route through).
UPDATE (2026-07-25): the cyclic step has since been PROVEN by a second
dévissage of the same shape — `exists_intermediate_of_isCyclic_quotient`
refines a cyclic quotient into prime steps — and the prime step itself
has since been PROVEN too, by the trace/determinant split: the
determinant half of the descended Frobenius polynomial is the cyclotomic
value `Nw` (`charFrob_baseChange_coeff_zero_eq_absNorm`) and needs no
automorphic input at all.  So the arithmetic citation of the descent
route is now `exists_baseChangeDescentData_of_prime_cyclic_step_of_inert`
— one scalar per
place, the Hecke eigenvalue of the descended newform at prime degree,
which is exactly what Langlands/Arthur–Clozel prove.

ROUTE AUDIT (2026-07-24): discharge by vacuity — `absurd hirr
(not_isIrreducible_of_isHardlyRamified_of_five_le …)` — is NOT
available at this node or below it: the headline consumes this node
(headline ← `exists_threeadic_compatible_member_of_five_le` ←
`exists_heckeField_system_of_witness` ← this node), so the vacuity
route is circular here. The classical route above is the one the
sub-leaves must follow. -/

theorem exists_descended_heckeSystem_of_solvable
    {ℓ : ℕ} (hℓodd : Odd ℓ) [Fact ℓ.Prime] (hℓ5 : 5 ≤ ℓ)
    {O : Type u} [CommRing O] [IsDomain O] [TopologicalSpace O]
    [IsTopologicalRing O] [Algebra ℤ_[ℓ] O] [IsLocalRing O]
    [Module.Finite ℤ_[ℓ] O] [IsModuleTopology ℤ_[ℓ] O]
    (hZinj : Function.Injective (algebraMap ℤ_[ℓ] O))
    {ρ : GaloisRep ℚ O (Fin 2 → O)}
    (hrank : Module.rank O (Fin 2 → O) = 2)
    (hρ : IsHardlyRamified hℓodd hrank ρ)
    {k : Type u} [Field k] [Finite k] [Algebra ℤ_[ℓ] k]
    [TopologicalSpace k] [DiscreteTopology k]
    {W : Type v} [AddCommGroup W] [Module k W] [Module.Finite k W]
    [Module.Free k W]
    (hW : Module.rank k W = 2) {ρbar : GaloisRep ℚ k W}
    (hρbar : IsHardlyRamified hℓodd hW ρbar)
    (hirr : ρbar.IsIrreducible)
    (π : O →+* k) (hπsurj : Function.Surjective π)
    (hπ : ∀ (q : ℕ) (hq : q.Prime), q ≠ 2 → q ≠ ℓ →
      (ρ.charFrob hq.toHeightOneSpectrumRingOfIntegersRat).map π =
        ρbar.charFrob hq.toHeightOneSpectrumRingOfIntegersRat)
    (Wit : PotentialModularityWitness ℓ O ρ)
    (H : Subgroup (Wit.F ≃ₐ[ℚ] Wit.F)) (hH : IsSolvable H) :
    ∃ (S : Finset (HeightOneSpectrum (NumberField.RingOfIntegers
        (IntermediateField.fixedField H))))
      (P : HeightOneSpectrum (NumberField.RingOfIntegers
        (IntermediateField.fixedField H)) → Polynomial Wit.E),
      ∀ w ∉ S,
        ((ρ.map (algebraMap ℚ (IntermediateField.fixedField H))).charFrob
            w).map Wit.ιO = (P w).map Wit.ψℓ := by
  classical
  -- (i) the group-theoretic dévissage: a cyclic refinement of `H`
  obtain ⟨n, C, hC0, hCn, hstep⟩ :=
    exists_cyclicRefinement_of_isSolvable H hH
  -- (ii) descend along the chain, one cyclic step of base change at a
  -- time, starting from the carrier's own eigensystem at `F^⊥ = F`
  have key : ∀ i, i ≤ n → HeckeSystemDescendsTo Wit (C i) := by
    intro i
    induction i with
    | zero =>
      intro _
      rw [hC0]
      exact heckeSystemDescendsTo_bot hℓodd hℓ5 hZinj hrank hρ hW hρbar
        hirr π hπsurj hπ Wit
    | succ j ih =>
      intro hj
      obtain ⟨hle, hnormal, hcyclic⟩ := hstep j (by omega)
      exact heckeSystemDescendsTo_of_cyclic_step hℓodd hℓ5 hZinj hrank hρ
        hW hρbar hirr π hπsurj hπ Wit (C j) (C (j + 1)) hle hnormal
        hcyclic (ih (by omega))
  -- (iii) the top of the chain is `H` itself
  have hfinal := key n le_rfl
  rw [hCn] at hfinal
  -- (iv) the descended datum is realized over a number field `E'` that may be
  -- strictly larger than `Wit.E` (the Hecke field grows down the tower); the
  -- carrier's descent-closure brings it back to `Wit.E`, which is the field
  -- the downstream Brauer gluing must read every piece in
  obtain ⟨E', _, _, ψ, ι, hψι, S, a, h1, h2, h3⟩ := hfinal
  obtain ⟨S', b, hb⟩ := heckeField_descentClosed_of_witness Wit H E' ψ ι hψι S a h1
  refine ⟨S ∪ S', fun w => Polynomial.X ^ 2 - Polynomial.C (b w) * Polynomial.X +
    Polynomial.C ((Ideal.absNorm w.asIdeal : ℕ) : Wit.E), fun w hw => ?_⟩
  rw [Finset.mem_union, not_or] at hw
  rw [h1 w hw.1]
  have hψℓ : Wit.ψℓ = ψ.comp ι := by
    ext x
    exact (hψι x).symm
  rw [hψℓ, ← Polynomial.map_map]
  congr 1
  simp [Polynomial.map_add, Polynomial.map_sub, Polynomial.map_mul,
    Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C, hb w hw.1 hw.2]

set_option backward.isDefEq.respectTransparency false in
/-- **`charFrob` is monic** (PROVEN helper for the Brauer gluing): it is
by definition the characteristic polynomial of the local Frobenius
endomorphism of a finite free module.

(`Patching.lean` carries the same statement as `charFrob_monic`, but
that module lives DOWNSTREAM of this one — it imports
`Modularity/KhareWintenberger` — so the lemma is restated here under a
distinct name rather than imported; the proof is the two-line
unfolding to `LinearMap.charpoly_monic`.) -/
theorem charFrob_monic_of_free {A : Type*} [CommRing A]
    [TopologicalSpace A] [IsTopologicalRing A] {M : Type*} [AddCommGroup M]
    [Module A M] [Module.Finite A M] [Module.Free A M]
    (v : HeightOneSpectrum (NumberField.RingOfIntegers ℚ))
    (ρ : GaloisRep ℚ A M) : (ρ.charFrob v).Monic := by
  show ((ρ.toLocal v (Field.AbsoluteGaloisGroup.adicArithFrob v)).charpoly).Monic
  exact LinearMap.charpoly_monic _

set_option backward.isDefEq.respectTransparency false in
/-- **`charFrob` of a rank-`2` representation has degree `2`** (PROVEN
helper for the Brauer gluing): the characteristic polynomial of an
endomorphism of a finite free module has degree the rank.

(Downstream twin: `Patching.lean`'s `charFrob_natDegree`; see
`charFrob_monic_of_free` for why it is restated here.) -/
theorem charFrob_natDegree_of_rank_two {A : Type*} [CommRing A]
    [Nontrivial A] [TopologicalSpace A] [IsTopologicalRing A] {M : Type*}
    [AddCommGroup M] [Module A M] [Module.Finite A M] [Module.Free A M]
    (v : HeightOneSpectrum (NumberField.RingOfIntegers ℚ))
    (ρ : GaloisRep ℚ A M) (hdim : Module.rank A M = 2) :
    (ρ.charFrob v).natDegree = 2 := by
  show ((ρ.toLocal v
    (Field.AbsoluteGaloisGroup.adicArithFrob v)).charpoly).natDegree = 2
  rw [LinearMap.charpoly_natDegree]
  exact Module.finrank_eq_of_rank_eq (by exact_mod_cast hdim)

/-- **Coefficientwise lifting of a family of polynomials along a ring
homomorphism** (PROVEN helper, pure algebra): a family `p : ι →
Polynomial L` admits a family of `E`-preimages `P` that is correct at
exactly those indices where every coefficient of `p i` lies in the range
of `g : E →+* L`. This is `Polynomial.lifts_iff_coeff_lifts` made
uniform in the index by `choose` (indices failing the hypothesis get the
junk value `0`), and it is the formal half of the Brauer gluing below:
once the arithmetic leaves put each coefficient of the Frobenius
charpoly into `ψℓ(E)`, the `E`-polynomial family `Pv` demanded by the
statement is produced here, with no further arithmetic input. -/
theorem exists_polynomial_family_of_coeff_mem_range {ι : Type*}
    {E L : Type*} [CommRing E] [CommRing L] (g : E →+* L)
    (p : ι → Polynomial L) :
    ∃ P : ι → Polynomial E,
      ∀ i, (∀ n, (p i).coeff n ∈ Set.range g) → p i = (P i).map g := by
  classical
  have key : ∀ i, ∃ Q : Polynomial E,
      (∀ n, (p i).coeff n ∈ Set.range g) → p i = Q.map g := by
    intro i
    by_cases hi : ∀ n, (p i).coeff n ∈ Set.range g
    · obtain ⟨Q, hQ⟩ :=
        (Polynomial.mem_lifts _).1 ((Polynomial.lifts_iff_coeff_lifts _).2 hi)
      exact ⟨Q, fun _ => hQ.symm⟩
    · exact ⟨0, fun h => absurd h hi⟩
  choose P hP using key
  exact ⟨P, hP⟩

/-- **The rational prime `ℓ` is a unit at a place over `q ≠ ℓ`** (PROVEN
helper for the cyclotomic evaluation below): `ℓ` lies in the prime
complement of the `q`-adic ideal, so its `q`-adic valuation is `1`.

Port of `Family.lean`'s
`valued_natCast_adicCompletionIntegers_eq_one_of_ne`, which this module
may not import (CIRCULARITY GUARD); the only delta from that source is
`norm_cast` in place of its `simp only [algebraMap.coe_natCast]` in the
`hbridge` step, the latter making no progress in this file's instance
context. -/
lemma valued_natCast_adicCompletionIntegers_eq_one_of_ne
    {ℓ : ℕ} [hℓ : Fact ℓ.Prime] {q : ℕ}
    (hq : q.Prime) (hqℓ : q ≠ ℓ) :
    Valued.v ((((ℓ : ℕ) :
        HeightOneSpectrum.adicCompletionIntegers ℚ
          hq.toHeightOneSpectrumRingOfIntegersRat)) :
      HeightOneSpectrum.adicCompletion ℚ
        hq.toHeightOneSpectrumRingOfIntegersRat) = 1 := by
  set v := hq.toHeightOneSpectrumRingOfIntegersRat
  have hcompl : ((ℓ : ℕ) : NumberField.RingOfIntegers ℚ) ∈
      v.asIdeal.primeCompl := by
    intro hmem
    have hdvd := (Nat.Prime.mem_toHeightOneSpectrumRingOfIntegersRat_asIdeal
      hq _).mp hmem
    rw [map_natCast, Int.natCast_dvd_natCast] at hdvd
    exact hqℓ ((Nat.prime_dvd_prime_iff_eq hq hℓ.out).mp hdvd)
  have hint1 : HeightOneSpectrum.intValuation v
      ((ℓ : ℕ) : NumberField.RingOfIntegers ℚ) = 1 :=
    (HeightOneSpectrum.intValuation_eq_one_iff_mem_primeCompl
      v _).mpr hcompl
  have hK := (HeightOneSpectrum.valuedAdicCompletion_eq_valuation
      (v := v) (K := ℚ) (((ℓ : ℕ) : NumberField.RingOfIntegers ℚ))).trans
    ((HeightOneSpectrum.valuation_of_algebraMap
      (v := v) (K := ℚ) (((ℓ : ℕ) : NumberField.RingOfIntegers ℚ))).trans hint1)
  have hbridge : ((((ℓ : ℕ) :
        HeightOneSpectrum.adicCompletionIntegers ℚ v)) :
      HeightOneSpectrum.adicCompletion ℚ v) =
      @algebraMap _ _ _ _
        (HeightOneSpectrum.instAlgebraAdicCompletion
          (NumberField.RingOfIntegers ℚ) ℚ v)
        (((ℓ : ℕ) : NumberField.RingOfIntegers ℚ)) := by
    rw [map_natCast]
    norm_cast
  rw [hbridge]
  exact hK

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1000000 in
/-- **The arithmetic Frobenius at `q ≠ ℓ` raises `ℓ`-power roots of
unity to the `q`-th power** (PROVEN): at a prime `q ≠ ℓ` the `ℓ`-power
roots of unity are unramified, the arithmetic Frobenius reduces to
`x ↦ x^q` on the residue field, and roots of unity of order coprime to
`q` inject into the residue field, so the action is exactly `ζ ↦ ζ^q`.
Stated in the `modularCyclotomicCharacter.unique` hypothesis shape.

Port of `Family.lean`'s `adicArithFrob_rootsOfUnity_pow_of_ne` (a
forbidden import here — CIRCULARITY GUARD), itself the general-`ℓ` port
of the `3`-adic `adicArithFrob_rootsOfUnity_pow` of `GaloisRep.lean`.
Every lemma it consumes (`natCard_residue_quotient_toHeightOneSpectrum`,
`mem_completionIdeal_iff`, `isArithFrobAt_adicArithFrob`,
`absoluteGaloisGroup.lift_map`) already lies in this module's import
cone; only the helper above had to travel with it. -/
theorem adicArithFrob_rootsOfUnity_pow_of_ne
    {ℓ : ℕ} [hℓ : Fact ℓ.Prime] {q : ℕ}
    (hq : q.Prime) (hqℓ : q ≠ ℓ) (n : ℕ) :
    ∀ t ∈ rootsOfUnity (ℓ ^ n) (AlgebraicClosure ℚ),
      ((Field.absoluteGaloisGroup.map (algebraMap ℚ
        (HeightOneSpectrum.adicCompletion ℚ
          hq.toHeightOneSpectrumRingOfIntegersRat))
        (Field.AbsoluteGaloisGroup.adicArithFrob
          hq.toHeightOneSpectrumRingOfIntegersRat)).toRingEquiv) t =
        t ^ ((q : ZMod (ℓ ^ n)).val) := by
  intro t ht
  classical
  -- the `q` of the Frobenius specification is the residue cardinality
  have hcard :=
    GaloisRepresentation.natCard_residue_quotient_toHeightOneSpectrum hq
  set v := hq.toHeightOneSpectrumRingOfIntegersRat
  set f := algebraMap ℚ (HeightOneSpectrum.adicCompletion ℚ v)
  -- the root of unity, its power identity, and its image under the chosen
  -- embedding of algebraic closures
  have htL : ((t : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ) ^ (ℓ ^ n)
      = 1 := by
    have h1 := (mem_rootsOfUnity _ _).mp ht
    calc ((t : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ) ^ (ℓ ^ n)
        = ((t ^ (ℓ ^ n) : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ) := by
          push_cast; rfl
      _ = 1 := by rw [h1]; rfl
  set ζ : AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ v) :=
    AlgebraicClosure.map f ((t : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ)
    with hζdef
  have hζpow : ζ ^ (ℓ ^ n) = 1 := by
    rw [hζdef, ← map_pow, htL, map_one]
  -- the image is integral over the completion integers (it kills `X^{ℓⁿ}-1`)
  have hint : IsIntegral
      (HeightOneSpectrum.adicCompletionIntegers ℚ v) ζ := by
    refine ⟨Polynomial.X ^ (ℓ ^ n) - 1, ?_, ?_⟩
    · have := Polynomial.monic_X_pow_sub_C
        (R := HeightOneSpectrum.adicCompletionIntegers ℚ v)
        (1 : _) (n := ℓ ^ n) (pow_ne_zero _ hℓ.out.pos.ne')
      simpa [Polynomial.C_1] using this
    · simp [Polynomial.eval₂_sub, hζpow]
  set ζ' : IntegralClosure
      (HeightOneSpectrum.adicCompletionIntegers ℚ v)
      (AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ v)) :=
    ⟨ζ, hint⟩ with hζ'def
  have hζ'pow : ζ' ^ (ℓ ^ n) = 1 := by
    apply Subtype.ext
    push_cast [hζ'def]
    exact hζpow
  -- `ℓ` is a unit at the `q`-place (`q ≠ ℓ`), so `ℓⁿ` avoids the maximal
  -- ideal
  have hpnotin : ((ℓ : ℕ) ^ n : IntegralClosure
      (HeightOneSpectrum.adicCompletionIntegers ℚ v)
      (AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ v))) ∉
      IsLocalRing.maximalIdeal _ := by
    have hunit : IsUnit ((ℓ : ℕ) :
        HeightOneSpectrum.adicCompletionIntegers ℚ v) := by
      by_contra hnu
      have hmem := (IsLocalRing.mem_maximalIdeal _).mpr hnu
      have hlt := (HeightOneSpectrum.mem_completionIdeal_iff
        (K := ℚ) (v := v) _).mp hmem
      have h1 := valued_natCast_adicCompletionIntegers_eq_one_of_ne hq hqℓ
      exact absurd (lt_of_lt_of_le hlt h1.symm.le) (lt_irrefl _)
    have hunitIC : IsUnit (((ℓ : ℕ) ^ n) : IntegralClosure
        (HeightOneSpectrum.adicCompletionIntegers ℚ v)
        (AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ v))) := by
      have h1 := hunit.map (algebraMap
        (HeightOneSpectrum.adicCompletionIntegers ℚ v)
        (IntegralClosure
          (HeightOneSpectrum.adicCompletionIntegers ℚ v)
          (AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ v))))
      rw [map_natCast] at h1
      exact h1.pow n
    intro hmem
    exact ((IsLocalRing.mem_maximalIdeal _).mp hmem) hunitIC
  -- the Frobenius specification on the integral closure
  have hfrob := AlgHom.IsArithFrobAt.apply_of_pow_eq_one
    (Field.AbsoluteGaloisGroup.isArithFrobAt_adicArithFrob (v := v))
    hζ'pow (by exact_mod_cast hpnotin)
  rw [hcard] at hfrob
  -- read the specification off in `Kᵥᵃˡᵍ`
  have hfrobK : Field.AbsoluteGaloisGroup.adicArithFrob v ζ = ζ ^ q := by
    have h1 := hfrob
    rw [MulSemiringAction.toAlgHom_apply] at h1
    have h2 := congrArg Subtype.val h1
    rw [IntegralClosure.coe_smul] at h2
    have h3 : ((⟨ζ, hint⟩ : IntegralClosure _ _) ^ q).1 = ζ ^ q :=
      SubmonoidClass.coe_pow _ _
    simpa [hζ'def, AlgEquiv.smul_def] using h2.trans h3
  -- globalize through the chosen embedding, which is injective
  have hsq := Field.absoluteGaloisGroup.lift_map f
    (Field.AbsoluteGaloisGroup.adicArithFrob v)
    ((t : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ)
  have hmain : (Field.absoluteGaloisGroup.map f
      (Field.AbsoluteGaloisGroup.adicArithFrob v))
      ((t : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ) =
      ((t : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ) ^ q := by
    apply (AlgebraicClosure.map f).injective
    rw [hsq, map_pow]
    exact hfrobK
  -- the goal's `toRingEquiv` application is the automorphism application
  show (Field.absoluteGaloisGroup.map f
      (Field.AbsoluteGaloisGroup.adicArithFrob v))
      ((t : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ) = _
  rw [hmain]
  -- the exponent-mod juggle: `t^q = t^(q mod ℓⁿ)` since `t^{ℓⁿ} = 1`
  haveI : NeZero (ℓ ^ n) := ⟨pow_ne_zero _ hℓ.out.pos.ne'⟩
  have hval : ((q : ZMod (ℓ ^ n))).val = q % ℓ ^ n := ZMod.val_natCast _ q
  conv_lhs => rw [show q = ℓ ^ n * (q / ℓ ^ n) + q % ℓ ^ n from
    (Nat.div_add_mod q (ℓ ^ n)).symm]
  rw [pow_add, pow_mul, htL, one_pow, one_mul, hval]

/-- **The `ℓ`-adic cyclotomic character at an arithmetic Frobenius**
(PROVEN): at a rational prime `q ≠ ℓ` the `ℓ`-adic cyclotomic character
takes the value `q` on the global image of the arithmetic Frobenius at
`q`. By `ℓ`-adic continuity: `PadicInt.ext_of_toZModPow` reduces the
identity to every level `ℓⁿ`, where `cyclotomicCharacter.toZModPow` and
`modularCyclotomicCharacter.unique` identify the character value with
`q` from the roots-of-unity action above. Classically this is the
unramifiedness of the cyclotomic character away from `ℓ` together with
`Frob_q(ζ) = ζ^q` (Serre, *Abelian ℓ-adic Representations*, I.1;
Neukirch, *Algebraic Number Theory*, IV).

Port of `Family.lean`'s `cyclotomicCharacter_adicArithFrob_natCast`,
which the CIRCULARITY GUARD of this module forbids importing;
`GaloisRep.lean`'s `cyclotomicCharacter_adicArithFrob` is the same
statement hard-wired to `ℓ = 3`. Consumed by
`charFrob_coeff_zero_eq_natCast_of_isHardlyRamified` below, which is
what makes the DETERMINANT coefficient of the Brauer-descent Frobenius
charpolys rational and leaves the trace as the only coefficient
carrying automorphy content. -/
theorem cyclotomicCharacter_adicArithFrob_eq_natCast
    {ℓ : ℕ} [hℓ : Fact ℓ.Prime] {q : ℕ}
    (hq : q.Prime) (hqℓ : q ≠ ℓ) :
    ((cyclotomicCharacter (AlgebraicClosure ℚ) ℓ
      ((Field.absoluteGaloisGroup.map (algebraMap ℚ
        (HeightOneSpectrum.adicCompletion ℚ
          hq.toHeightOneSpectrumRingOfIntegersRat))
        (Field.AbsoluteGaloisGroup.adicArithFrob
          hq.toHeightOneSpectrumRingOfIntegersRat)).toRingEquiv) : ℤ_[ℓ]ˣ) :
      ℤ_[ℓ]) = (q : ℤ_[ℓ]) := by
  rw [← PadicInt.ext_of_toZModPow]
  intro n
  rw [map_natCast, cyclotomicCharacter.toZModPow]
  exact (modularCyclotomicCharacter.unique
    (hn := HasEnoughRootsOfUnity.natCard_rootsOfUnity (AlgebraicClosure ℚ)
      (ℓ ^ n))
    _ _ (adicArithFrob_rootsOfUnity_pow_of_ne hq hqℓ n)).symm

/-- **The determinant coefficient of a hardly ramified Frobenius
charpoly is `q`** (PROVEN from the cyclotomic leaf above): for a hardly
ramified `ρ` on a rank-`2` module and a prime `q ≠ ℓ`, the constant
coefficient of `charFrob ρ` at `q` is the rational integer `q`.

Proof: for a rank-`2` charpoly `det = (-1)² · coeff 0`
(`LinearMap.det_eq_sign_charpoly_coeff`); the determinant of the global
image of the local Frobenius is the cyclotomic-character value by
`IsHardlyRamified.det`; and that value is `q` by
`cyclotomicCharacter_adicArithFrob_eq_natCast`. (Port of the PROVEN
`Family.lean` lemma `charFrob_coeff_zero_eq_natCast`, restated without
the auxiliary `Algebra R (AlgebraicClosure ℚ_[ℓ])` instance; its
cyclotomic input is ported above, so this lemma is unconditional.)

Consequence for the Brauer gluing below: of the three nonzero
coefficients of the monic quadratic `charFrob`, only the TRACE
(`coeff 1`) carries automorphy content — `coeff 2 = 1` by monicity and
`coeff 0 = q` by this lemma. -/
theorem charFrob_coeff_zero_eq_natCast_of_isHardlyRamified {ℓ : ℕ}
    (hℓodd : Odd ℓ) [Fact ℓ.Prime]
    {O : Type u} [CommRing O] [TopologicalSpace O] [IsTopologicalRing O]
    [IsLocalRing O] [Algebra ℤ_[ℓ] O]
    {ρ : GaloisRep ℚ O (Fin 2 → O)}
    (hrank : Module.rank O (Fin 2 → O) = 2)
    (hρ : IsHardlyRamified hℓodd hrank ρ)
    {q : ℕ} (hq : q.Prime) (hqℓ : q ≠ ℓ) :
    (ρ.charFrob hq.toHeightOneSpectrumRingOfIntegersRat).coeff 0 = (q : O) := by
  have hfinrank : Module.finrank O (Fin 2 → O) = 2 :=
    Module.finrank_eq_of_rank_eq hrank
  -- the constant coefficient of a rank-`2` charpoly is the determinant
  have hdet := LinearMap.det_eq_sign_charpoly_coeff
    (ρ.toLocal hq.toHeightOneSpectrumRingOfIntegersRat
      (Field.AbsoluteGaloisGroup.adicArithFrob
        hq.toHeightOneSpectrumRingOfIntegersRat))
  rw [hfinrank, neg_one_sq, one_mul] at hdet
  -- the determinant of the global Frobenius image is `q`
  have hcyclo := hρ.det (Field.absoluteGaloisGroup.map (algebraMap ℚ
    (HeightOneSpectrum.adicCompletion ℚ
      hq.toHeightOneSpectrumRingOfIntegersRat))
    (Field.AbsoluteGaloisGroup.adicArithFrob
      hq.toHeightOneSpectrumRingOfIntegersRat))
  rw [GaloisRep.det_apply, cyclotomicCharacter_adicArithFrob_eq_natCast hq hqℓ,
    map_natCast] at hcyclo
  -- bridge the local-Frobenius determinant to the global one (the two
  -- spellings differ only in the subsingleton `Algebra ℚ _` instance)
  have hdetq : LinearMap.det (ρ.toLocal
      hq.toHeightOneSpectrumRingOfIntegersRat
      (Field.AbsoluteGaloisGroup.adicArithFrob
        hq.toHeightOneSpectrumRingOfIntegersRat)) = (q : O) := by
    rw [GaloisRep.toLocal_apply]
    convert hcyclo using 2
    congr 1
    congr 1
    congr 1
    exact Subsingleton.elim _ _
  rw [show ρ.charFrob hq.toHeightOneSpectrumRingOfIntegersRat =
      (ρ.toLocal hq.toHeightOneSpectrumRingOfIntegersRat
        (Field.AbsoluteGaloisGroup.adicArithFrob
          hq.toHeightOneSpectrumRingOfIntegersRat)).charpoly from rfl,
    ← hdet, hdetq]

/-- **`charFrob` transfer along a local hom of completions** (PROVEN
2026-07-25): let `ρ` be a Galois representation of `G_k` for a number
field `k`, UNRAMIFIED at a finite place `v` of `k`; let `f : k →+* K`
present a second number field and `w` a finite place of `K`. Suppose
there is a ring hom of completions `ε : k_v →+* K_w` which

* is compatible with `f` over `k` (`hεcomm`) — i.e. `w` lies over `v`;
* is LOCAL, `ε(𝒪_v) ⊆ 𝒪_w` (`hεint`);
* does not change the residue cardinality (`hcard`) — i.e. the residue
  degree `f(w|v)` is `1`.

Then the Frobenius characteristic polynomial of the RESTRICTION
`ρ|_{G_K}` at `w` equals that of `ρ` at `v`.

This is the "degree-one place" mechanism of the Brauer descent: a place
of residue degree one sees the same Frobenius conjugacy class as the
place below it, so the restricted representation has the same Frobenius
charpoly there. Note the ramification index is NOT constrained — only
`f(w|v) = 1` is used, because inertia at `v` is invisible to a `ρ`
unramified at `v`.

BASE FIELD KEPT GENERIC ON PURPOSE. Stating this over a variable `k`
rather than over `ℚ` is not generality for its own sake: over `ℚ` the
term `algebraMap ℚ (v.adicCompletion ℚ)` elaborates through
`DivisionRing.toRatAlgebra`, whereas `GaloisRep.toLocal` — hence
`charFrob` — uses `HeightOneSpectrum.instAlgebraAdicCompletion`. The two
are propositionally but not definitionally equal, and the ℚ-specialised
statement is unprovable as written without a `Subsingleton.elim` bridge
at every occurrence. With `k` a variable there is only one instance and
the mismatch cannot arise. (The same trap is why the neighbouring
`charFrob_coeff_zero_eq_natCast_of_isHardlyRamified` ends in
`exact Subsingleton.elim _ _`.)

PROOF (the pattern of `GaloisRep.charFrob_map_ringEquiv`, from which
every ingredient is borrowed): both `charFrob`s are `ρ` evaluated at an
element of `Γ k` produced by two arbitrary choices — a chosen embedding
of algebraic closures (`Field.absoluteGaloisGroup.map`) and a chosen
arithmetic Frobenius (`Field.AbsoluteGaloisGroup.adicArithFrob`). The
two factorisations `k → K → K_w` and `k → k_v → K_w` of the SAME ring
hom differ by one conjugation each
(`Field.absoluteGaloisGroup.exists_conj_map_comp'`, needed in its
algebraicity-free form because the middle field is a completion); and
`Field.absoluteGaloisGroup.isArithFrobAt_map` — whose residue-cardinality
side condition is exactly `hcard`, through
`IsDedekindDomain.HeightOneSpectrum.natCard_under_maximalIdeal` — says
the image of `Frob_w` in `Γ k_v` is again an arithmetic Frobenius, hence
`Frob_v · ι` with `ι ∈ localInertiaGroup v`
(`IsArithFrobAt.mul_inv_mem_inertia`, plus normality of inertia through
`Field.absoluteGaloisGroup.conj_mem_localInertiaGroup`). Unramifiedness
kills `ι`; `LinearEquiv.charpoly_conj` kills the conjugation.

SOUNDNESS AUDIT: `hv` is LOAD-BEARING (at a ramified `v` the two sides
are functions of two unrelated arbitrary choices and the statement is
false in general), and so is `hcard` (with residue degree `f > 1` the
correct right-hand side involves `Frob_v ^ f`, not `Frob_v`). Nothing is
vacuous: such an `ε` exists exactly when `w` lies over `v`, and then the
identity is the standard compatibility of Frobenius conjugacy classes
under restriction. -/
theorem charFrob_map_of_adicCompletionHom
    {k : Type*} [Field k] [NumberField k]
    {K : Type*} [Field K] [NumberField K]
    {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    {M : Type*} [AddCommGroup M] [Module A M] [Module.Finite A M] [Module.Free A M]
    (ρ : GaloisRep k A M) (f : k →+* K)
    (v : HeightOneSpectrum (NumberField.RingOfIntegers k))
    (w : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (hv : ρ.IsUnramifiedAt v)
    (ε : v.adicCompletion k →+* w.adicCompletion K)
    (hεint : ∀ x ∈ v.adicCompletionIntegers k, ε x ∈ w.adicCompletionIntegers K)
    (hcard : Nat.card (NumberField.RingOfIntegers k ⧸ v.asIdeal)
      = Nat.card (NumberField.RingOfIntegers K ⧸ w.asIdeal))
    (hεcomm : ε.comp (algebraMap k (v.adicCompletion k))
      = (algebraMap K (w.adicCompletion K)).comp f) :
    (ρ.map f).charFrob w = ρ.charFrob v := by
  classical
  -- the two factorisations of `k → K_w`, each costing one conjugation
  obtain ⟨τ₁, hτ₁⟩ := Field.absoluteGaloisGroup.exists_conj_map_comp'
    f (algebraMap K (w.adicCompletion K))
    ((algebraMap K (w.adicCompletion K)).comp f) rfl
  obtain ⟨τ₂, hτ₂⟩ := Field.absoluteGaloisGroup.exists_conj_map_comp'
    (algebraMap k (v.adicCompletion k)) ε
    ((algebraMap K (w.adicCompletion K)).comp f) hεcomm
  -- the residue cardinalities of the two `IsArithFrobAt` specifications agree
  have hcard' : Nat.card (↥(v.adicCompletionIntegers k) ⧸
        (IsLocalRing.maximalIdeal (IntegralClosure ↥(v.adicCompletionIntegers k)
          (AlgebraicClosure (v.adicCompletion k)))).under ↥(v.adicCompletionIntegers k)) =
      Nat.card (↥(w.adicCompletionIntegers K) ⧸
        (IsLocalRing.maximalIdeal (IntegralClosure ↥(w.adicCompletionIntegers K)
          (AlgebraicClosure (w.adicCompletion K)))).under ↥(w.adicCompletionIntegers K)) := by
    rw [IsDedekindDomain.HeightOneSpectrum.natCard_under_maximalIdeal,
      IsDedekindDomain.HeightOneSpectrum.natCard_under_maximalIdeal]
    exact hcard
  -- the transported Frobenius is again an arithmetic Frobenius at `v`, hence
  -- `Frob_v` times ONE inertia element
  obtain ⟨ι, hιmem, hιeq⟩ : ∃ ι ∈ localInertiaGroup v,
      Field.absoluteGaloisGroup.map ε (Field.AbsoluteGaloisGroup.adicArithFrob w)
        = Field.AbsoluteGaloisGroup.adicArithFrob v * ι := by
    have hX : IsArithFrobAt ↥(v.adicCompletionIntegers k)
        (Field.absoluteGaloisGroup.map ε (Field.AbsoluteGaloisGroup.adicArithFrob w))
        (IsLocalRing.maximalIdeal (IntegralClosure ↥(v.adicCompletionIntegers k)
          (AlgebraicClosure (v.adicCompletion k)))) :=
      Field.absoluteGaloisGroup.isArithFrobAt_map v w ε hεint hcard'
    have h1 : Field.absoluteGaloisGroup.map ε (Field.AbsoluteGaloisGroup.adicArithFrob w) *
        (Field.AbsoluteGaloisGroup.adicArithFrob v)⁻¹ ∈ localInertiaGroup v :=
      IsArithFrobAt.mul_inv_mem_inertia hX
        (Field.AbsoluteGaloisGroup.isArithFrobAt_adicArithFrob v)
    refine ⟨(Field.AbsoluteGaloisGroup.adicArithFrob v)⁻¹ *
      Field.absoluteGaloisGroup.map ε (Field.AbsoluteGaloisGroup.adicArithFrob w),
      ?_, by group⟩
    have h3 := Field.absoluteGaloisGroup.conj_mem_localInertiaGroup v
      (Field.AbsoluteGaloisGroup.adicArithFrob v)⁻¹
      (Field.absoluteGaloisGroup.map ε (Field.AbsoluteGaloisGroup.adicArithFrob w) *
        (Field.AbsoluteGaloisGroup.adicArithFrob v)⁻¹) h1
    rwa [show (Field.AbsoluteGaloisGroup.adicArithFrob v)⁻¹ *
        (Field.absoluteGaloisGroup.map ε (Field.AbsoluteGaloisGroup.adicArithFrob w) *
          (Field.AbsoluteGaloisGroup.adicArithFrob v)⁻¹) *
        ((Field.AbsoluteGaloisGroup.adicArithFrob v)⁻¹)⁻¹
        = (Field.AbsoluteGaloisGroup.adicArithFrob v)⁻¹ *
          Field.absoluteGaloisGroup.map ε (Field.AbsoluteGaloisGroup.adicArithFrob w)
        from by group] at h3
  -- the inertia discrepancy is killed by the unramifiedness hypothesis
  have hι1 : ρ (Field.absoluteGaloisGroup.map (algebraMap k (v.adicCompletion k)) ι) = 1 := by
    have h1' : ρ.toLocal v ι = 1 := hv.localInertiaGroup_le hιmem
    rwa [GaloisRep.toLocal_apply] at h1'
  -- the single conjugator, as a linear automorphism
  obtain ⟨μ, hμ⟩ : ∃ μ : Field.absoluteGaloisGroup k, τ₁⁻¹ * τ₂ = μ := ⟨_, rfl⟩
  have hunit : (ρ μ : Module.End A M) * ρ μ⁻¹ = 1 := by
    rw [← map_mul, mul_inv_cancel, map_one]
  have hunit' : (ρ μ⁻¹ : Module.End A M) * ρ μ = 1 := by
    rw [← map_mul, inv_mul_cancel, map_one]
  set u : M ≃ₗ[A] M :=
    LinearEquiv.ofLinear (ρ μ) (ρ μ⁻¹) (by ext m; exact congrFun (congrArg _ hunit) m)
      (by ext m; exact congrFun (congrArg _ hunit') m) with hu
  have hLHS : (ρ.map f).toLocal w (Field.AbsoluteGaloisGroup.adicArithFrob w)
      = u.conj (ρ.toLocal v (Field.AbsoluteGaloisGroup.adicArithFrob v)) := by
    have hstep : Field.absoluteGaloisGroup.map f
        (Field.absoluteGaloisGroup.map (algebraMap K (w.adicCompletion K))
          (Field.AbsoluteGaloisGroup.adicArithFrob w))
        = μ * (Field.absoluteGaloisGroup.map (algebraMap k (v.adicCompletion k))
              (Field.AbsoluteGaloisGroup.adicArithFrob v) *
            Field.absoluteGaloisGroup.map (algebraMap k (v.adicCompletion k)) ι) * μ⁻¹ := by
      rw [← map_mul, ← hιeq, ← hμ]
      have e1 := hτ₁ (Field.AbsoluteGaloisGroup.adicArithFrob w)
      have e2 := hτ₂ (Field.AbsoluteGaloisGroup.adicArithFrob w)
      rw [e2] at e1
      rw [show Field.absoluteGaloisGroup.map f
          (Field.absoluteGaloisGroup.map (algebraMap K (w.adicCompletion K))
            (Field.AbsoluteGaloisGroup.adicArithFrob w))
          = τ₁⁻¹ * (τ₁ * Field.absoluteGaloisGroup.map f
              (Field.absoluteGaloisGroup.map (algebraMap K (w.adicCompletion K))
                (Field.AbsoluteGaloisGroup.adicArithFrob w)) * τ₁⁻¹) * τ₁ from by group,
        ← e1]
      group
    rw [GaloisRep.toLocal_apply, GaloisRep.map_apply, GaloisRep.toLocal_apply, hstep,
      map_mul, map_mul, map_mul, hι1, mul_one]
    ext m
    simp only [LinearEquiv.conj_apply, LinearMap.coe_comp, Function.comp_apply,
      LinearEquiv.coe_coe, hu, LinearEquiv.ofLinear_apply,
      LinearEquiv.ofLinear_symm_apply, Module.End.mul_apply]
  show ((ρ.map f).toLocal w (Field.AbsoluteGaloisGroup.adicArithFrob w)).charpoly
    = (ρ.toLocal v (Field.AbsoluteGaloisGroup.adicArithFrob v)).charpoly
  rw [hLHS, LinearEquiv.charpoly_conj]

section DegreeOnePlaces

open scoped NumberField Pointwise

/-- **A local ring hom of adic completions along a place above** (PROVEN):
for a finite extension `K/k` of number fields and a finite place `w` of `K`
lying over the place `v` of `k`, the inclusion `k → K` completes to a ring
hom `k_v →+* K_w` which is LOCAL (it carries `𝒪_v` into `𝒪_w`) and
compatible with `k → K`.

This is the "functoriality of `adicCompletion` along `Ideal.under`" that
`exists_degreeOnePlace_of_brauer` below needs, and it is assembled entirely
from `CompletionTransport.lean`: the valuation comparison
`valuation_map_le_of_le_one` (whose ideal-theoretic hypotheses are `le_rfl`
and `id` once `v` is literally `w.under (𝓞 k)`), the uniform continuity
criterion `WithVal.uniformContinuous_map_of_le`, and then
`adicCompletionMap` with its two properties `adicCompletionMap_mem_integers`
and `adicCompletionMap_coe`.

WHY THE BASE FIELD IS GENERIC. Over `ℚ` the notation
`algebraMap ℚ (v.adicCompletion ℚ)` is ambiguous — `DivisionRing.toRatAlgebra`
and `HeightOneSpectrum.instAlgebraAdicCompletion` are propositionally but not
definitionally equal. Stating this over a generic base field `k` leaves only
one instance, and instantiating at `k := ℚ` therefore produces the
`instAlgebraAdicCompletion` form that
`exists_degreeOnePlace_of_brauer`'s conclusion pins with `@algebraMap`. Do
not specialise this lemma to `ℚ`. -/
theorem exists_adicCompletionHom_of_under
    {k K : Type*} [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]
    (w : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (v : HeightOneSpectrum (NumberField.RingOfIntegers k))
    (hvw : w.under (NumberField.RingOfIntegers k) = v) :
    ∃ ε : v.adicCompletion k →+* w.adicCompletion K,
      (∀ x ∈ v.adicCompletionIntegers k, ε x ∈ w.adicCompletionIntegers K) ∧
      ε.comp (algebraMap k (v.adicCompletion k)) =
        (algebraMap K (w.adicCompletion K)).comp (algebraMap k K) := by
  subst hvw
  set v := w.under (𝓞 k) with hv
  have hcomm : ∀ a : 𝓞 k,
      (algebraMap k K) (algebraMap (𝓞 k) k a)
        = algebraMap (𝓞 K) K (algebraMap (𝓞 k) (𝓞 K) a) := by
    intro a
    rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
  have hmem : v.asIdeal ≤ Ideal.comap (algebraMap (𝓞 k) (𝓞 K)) w.asIdeal := le_rfl
  have hcompl : ∀ s : 𝓞 k, s ∉ v.asIdeal →
      algebraMap (𝓞 k) (𝓞 K) s ∉ w.asIdeal := fun _ hs => hs
  have hψ : UniformContinuous (WithVal.map (v.valuation k) (w.valuation K) (algebraMap k K)) :=
    WithVal.uniformContinuous_map_of_le _ _
      (IsDedekindDomain.HeightOneSpectrum.valuation_surjective k v) _
      (fun x hx => IsDedekindDomain.HeightOneSpectrum.valuation_map_le_of_le_one v w _ _
        hcomm hmem hcompl x hx)
  exact ⟨IsDedekindDomain.HeightOneSpectrum.adicCompletionMap v w (algebraMap k K) hψ,
    fun x hx => IsDedekindDomain.HeightOneSpectrum.adicCompletionMap_mem_integers v w _ hψ
      _ hcomm hx,
    RingHom.ext fun x =>
      IsDedekindDomain.HeightOneSpectrum.adicCompletionMap_coe v w (algebraMap k K) hψ x⟩

/-- **A finite domain satisfying `z ^ N = z` identically has at most `N`
elements** (PROVEN): every element is a root of `X ^ N - X`, a nonzero
polynomial of degree `N` over a domain, and a polynomial has at most
`natDegree` roots (`Polynomial.card_le_degree_of_subset_roots`).

This is the counting half of "residue degree one" in
`exists_degreeOnePlace_of_brauer`: the Frobenius identity forces
`z ^ #(𝓞_ℚ/q) = z` on the whole residue ring `𝓞_{Kᵢ}/w`, which caps its
cardinality at `#(𝓞_ℚ/q)`; the reverse inequality is the injection of
residue rings. Stating it for a domain rather than a finite field avoids
having to produce the field structure on `𝓞_{Kᵢ}/w`. -/
theorem card_le_of_pow_eq_self {L : Type*} [CommRing L] [IsDomain L] [Finite L] {N : ℕ}
    (hN : 2 ≤ N) (h : ∀ z : L, z ^ N = z) : Nat.card L ≤ N := by
  classical
  have := Fintype.ofFinite L
  have hdeg : ((X : L[X]) ^ N - X).natDegree = N := by
    rw [natDegree_sub_eq_left_of_natDegree_lt]
    · simp
    · simp; omega
  have hne : ((X : L[X]) ^ N - X) ≠ 0 := by
    intro h0
    rw [h0, natDegree_zero] at hdeg
    omega
  have hsub : (Finset.univ : Finset L).val ⊆ ((X : L[X]) ^ N - X).roots := by
    intro z _
    rw [mem_roots hne, IsRoot, eval_sub, eval_pow, eval_X, h z, sub_self]
  have := Polynomial.card_le_degree_of_subset_roots hsub
  rw [hdeg] at this
  simpa [Nat.card_eq_fintype_card] using this

/-- **Some Brauer piece has a degree-one place above almost every
rational prime** (PROVEN 2026-07-25; the arithmetic core of the
induced-trace expansion below, and the ONLY place in the descent where
the Brauer decomposition is used): given a Brauer decomposition of the trivial
character of `Gal(F/ℚ)` into one-dimensional pieces `φ i` supported on
subgroups `H i` (`hbrauer`, `hφ0`, `hφ1`, `hφmul`) and, for each piece, a
finite bad set `S i` of places of the fixed field `Kᵢ = F^{H i}`, there
is a finite set `S₀` of rational primes outside of which EVERY rational
prime `q` admits an index `i` and a place `w ∉ S i` of `Kᵢ` lying over
`q` with residue degree ONE.

STATEMENT SHAPE. "`w` lies over `q` with `f(w|q) = 1`" is spelt out as
(i) equality of residue cardinalities,
`Nat.card (𝓞_ℚ / q) = Nat.card (𝓞_{Kᵢ} / w)`, and (ii) existence of a
LOCAL ring hom of completions `ε : ℚ_q →+* (Kᵢ)_w` compatible with
`ℚ → Kᵢ`. That is verbatim the input of
`charFrob_map_of_adicCompletionHom` above, which is what converts this
arithmetic statement into the trace identity. Spelling the place
relation this way — rather than through `Ideal.under` and
`Ideal.inertiaDeg` — avoids having to build, as a separate leaf, the
functoriality of `adicCompletion` along `Ideal.under`; that functoriality
is instead part of what this leaf asserts.

WHY THE `@algebraMap` IN `hεcomm` IS SPELT OUT. Over `ℚ` the notation
`algebraMap ℚ (q.adicCompletion ℚ)` resolves to `DivisionRing.toRatAlgebra`,
while `GaloisRep.toLocal` — and hence `charFrob` — uses
`HeightOneSpectrum.instAlgebraAdicCompletion`; the two are propositionally
but NOT definitionally equal. The instance is therefore pinned here, so
that this leaf's conclusion is literally the hypothesis
`charFrob_map_of_adicCompletionHom` expects and no `Subsingleton.elim`
bridge is needed at the join. Do not "simplify" it back.

CLASSICAL PROOF (Serre, *Abelian ℓ-adic Representations*, I.2): let `q`
be unramified in `F` and `σ = Frob_q ∈ Gal(F/ℚ)`. Evaluating the virtual
identity `Σᵢ cᵢ · Ind_{Hᵢ}^{Gal(F/ℚ)} φᵢ = 1` at `σ` — which is exactly
`hbrauer σ` — gives `1 = Σᵢ cᵢ |Hᵢ|⁻¹ Σₓ φᵢ(x⁻¹ σ x)`. Since `φᵢ`
VANISHES off `Hᵢ` (`hφ0`), not every term can be zero, so
`x⁻¹ σ x ∈ Hᵢ` for some `i` and some `x ∈ Gal(F/ℚ)`. Under the
double-coset description of the primes of `Kᵢ = F^{Hᵢ}` above `q` —
they are indexed by `Hᵢ \ Gal(F/ℚ) / ⟨σ⟩`, the residue degree of the
prime attached to `Hᵢ x ⟨σ⟩` being the least `d ≥ 1` with
`x σᵈ x⁻¹ ∈ Hᵢ` — that says precisely that the prime attached to
`Hᵢ x ⟨σ⟩` has residue degree `1`. Finally `S₀` collects the rational
primes ramified in `F` (a finite set) together with the rational primes
lying under an element of some `S i` (finitely many, each `S i` being a
`Finset`), which is what makes the produced `w` avoid `S i`.

FORMALISED PROOF (2026-07-25), which is the classical one with two
simplifications that remove all four pieces of machinery the sorry node
was originally cut against.

* SIMPLIFICATION 1 — no unramifiedness, hence no ramified-prime set. The
  argument never needs `Frob_Q` to GENERATE the decomposition group, only
  to induce `x ↦ x ^ #(𝓞_ℚ/q)` on `𝓞_F/Q`; such an element exists at
  EVERY prime `Q` (mathlib's `arithFrobAt` for a finite group acting on a
  ring with fixed subring, `Algebra.IsInvariant` being supplied for
  `𝓞_F/𝓞_ℚ` by `Algebra.isInvariant_of_isGalois'` and transported to
  `Gal(F/ℚ)` along `galRestrict`). So `S₀` collects ONLY the rational
  primes lying under an element of some `S i`, and item 2 of the old
  missing-machinery list — finiteness of the ramified set — is not needed
  at all. Note this makes `hbrauer` carry the entire arithmetic weight: it
  is applied at the Frobenius of an arbitrary prime `Q | q`.
* SIMPLIFICATION 2 — no double cosets and no `Ideal.inertiaDeg`. Write
  `g := x⁻¹ σ x ∈ Hᵢ`, which is (`IsArithFrobAt.conj`) a Frobenius at the
  conjugated prime `Q' := τ • Q`, still over `q`. Because `g` fixes
  `Kᵢ = F^{Hᵢ}` pointwise, the Frobenius congruence at `Q'` reads
  `a - a ^ #(𝓞_ℚ/q) ∈ Q'` for every `a ∈ 𝓞_{Kᵢ}`, i.e.
  `z ^ #(𝓞_ℚ/q) = z` identically on the residue ring `𝓞_{Kᵢ}/w` with
  `w := Q'.under 𝓞_{Kᵢ}`. That caps `#(𝓞_{Kᵢ}/w)` by `#(𝓞_ℚ/q)`
  (`card_le_of_pow_eq_self` above), and the injection
  `𝓞_ℚ/q ↪ 𝓞_{Kᵢ}/w` gives the reverse inequality — which is exactly the
  residue-cardinality clause of the conclusion, with no residue degree
  ever mentioned. So item 3 (the double-coset parametrisation) is not
  needed either.

Item 1 of the old list is mathlib's `arithFrobAt` (`Mathlib/RingTheory/
Frobenius.lean`, Andrew Yang) — present at this pin, and the reason the
local/global Frobenius bridge is unnecessary here: the leaf is proved with
the GLOBAL Frobenius throughout and never meets
`Field.AbsoluteGaloisGroup.adicArithFrob`. Item 4 is
`exists_adicCompletionHom_of_under` above, assembled from this project's
`IsDedekindDomain.HeightOneSpectrum.adicCompletionMap`.

SOUNDNESS AUDIT: NOT vacuous. The conclusion asserts the EXISTENCE of a
degree-one place, which fails for a fixed `i` (a rational prime inert in
`Kᵢ` has none) and is rescued only by `hbrauer` together with the
vanishing `hφ0`; both are load-bearing, as is `[IsGalois ℚ F]` (without
it there is no `Frob_q` in `F ≃ₐ[ℚ] F` and the double-coset description
fails). When `n = 0` the hypothesis `hbrauer` reads `0 = 1` in `ℂ` and
the statement is vacuously true, as it must be. No representation
theory, no `ℓ` and no modularity enter this leaf — it is pure algebraic
number theory, which is why it is cut out here.

HYPOTHESES NOT CONSUMED (2026-07-25, recorded for a cut-level owner; this
is NOT a vacuity report — the conclusion is the full existence statement
and `hφ0`, `hbrauer` and `[IsGalois ℚ F]` are all load-bearing). The proof
uses only the SUPPORT condition `hφ0` and the Brauer identity `hbrauer`:
the normalisation `_hφ1` and the multiplicativity `_hφmul` are never
needed, because all that is extracted from `hbrauer σ` is that SOME
summand `φ i (x⁻¹ σ x)` is nonzero, and `hφ0` then places `x⁻¹ σ x` in
`H i`. In other words this leaf is true for an arbitrary family of
functions `φ i` supported on `H i` satisfying the identity — being
characters of the `H i` is not used. They are underscore-prefixed so the
non-use is mechanically visible, and RETAINED rather than deleted because
the sole consumer `exists_inducedTrace_expansion_of_brauer` applies this
leaf positionally with its own hypothesis list, and because a
strengthened restatement (the actual Mackey expansion, whose weights are
the `φ i (Frob_w)`) would need them back. -/
theorem exists_degreeOnePlace_of_brauer
    {F : Type*} [Field F] [NumberField F] [IsGalois ℚ F]
    (n : ℕ) (H : Fin n → Subgroup (F ≃ₐ[ℚ] F))
    (φ : Fin n → (F ≃ₐ[ℚ] F) → ℂ) (c : Fin n → ℚ)
    (hφ0 : ∀ i, ∀ g ∉ H i, φ i g = 0)
    (_hφ1 : ∀ i, φ i 1 = 1)
    (_hφmul : ∀ i, ∀ a ∈ H i, ∀ b ∈ H i, φ i (a * b) = φ i a * φ i b)
    (hbrauer : ∀ g : F ≃ₐ[ℚ] F,
      ∑ i, (c i : ℂ) * (Nat.card (H i) : ℂ)⁻¹ *
        ∑ x : F ≃ₐ[ℚ] F, φ i (x⁻¹ * g * x) = 1)
    (S : ∀ i, Finset (HeightOneSpectrum (NumberField.RingOfIntegers
      (IntermediateField.fixedField (H i))))) :
    ∃ S₀ : Finset (HeightOneSpectrum (NumberField.RingOfIntegers ℚ)),
      ∀ (q : ℕ) (hq : q.Prime),
        hq.toHeightOneSpectrumRingOfIntegersRat ∉ S₀ →
        ∃ (i : Fin n) (w : HeightOneSpectrum (NumberField.RingOfIntegers
            (IntermediateField.fixedField (H i)))),
          w ∉ S i ∧
          Nat.card (NumberField.RingOfIntegers ℚ ⧸
              hq.toHeightOneSpectrumRingOfIntegersRat.asIdeal) =
            Nat.card (NumberField.RingOfIntegers
              (IntermediateField.fixedField (H i)) ⧸ w.asIdeal) ∧
          ∃ ε : hq.toHeightOneSpectrumRingOfIntegersRat.adicCompletion ℚ →+*
              w.adicCompletion (IntermediateField.fixedField (H i)),
            (∀ x ∈ hq.toHeightOneSpectrumRingOfIntegersRat.adicCompletionIntegers ℚ,
              ε x ∈ w.adicCompletionIntegers (IntermediateField.fixedField (H i))) ∧
            ε.comp (@algebraMap ℚ
                (hq.toHeightOneSpectrumRingOfIntegersRat.adicCompletion ℚ) _ _
                (HeightOneSpectrum.instAlgebraAdicCompletion
                  (NumberField.RingOfIntegers ℚ) ℚ
                  hq.toHeightOneSpectrumRingOfIntegersRat)) =
              (algebraMap (IntermediateField.fixedField (H i))
                  (w.adicCompletion (IntermediateField.fixedField (H i)))).comp
                (algebraMap ℚ (IntermediateField.fixedField (H i))) := by
  classical
  -- `Gal(F/ℚ)` acts on `𝓞 F` with fixed subring `𝓞 ℚ`, through `galRestrict`
  haveI : Algebra.IsInvariant (𝓞 ℚ) (𝓞 F) (𝓞 F ≃ₐ[𝓞 ℚ] 𝓞 F) :=
    Algebra.isInvariant_of_isGalois' (𝓞 ℚ) ℚ F (𝓞 F)
  haveI : Finite (𝓞 F ≃ₐ[𝓞 ℚ] 𝓞 F) :=
    Finite.of_equiv _ (galRestrict (𝓞 ℚ) ℚ F (𝓞 F)).toEquiv
  -- `S₀` is exactly the set of rational primes below a bad place of some `Kᵢ`
  refine ⟨Finset.univ.biUnion
    (fun i => (S i).image (fun w => w.under (𝓞 ℚ))), ?_⟩
  intro q hq hqS₀
  set qv := hq.toHeightOneSpectrumRingOfIntegersRat with hqv
  -- a maximal ideal `Q` of `𝓞 F` over `q`
  haveI : qv.asIdeal.IsMaximal := qv.isPrime.isMaximal qv.ne_bot
  obtain ⟨Q, hQmax, hQunder⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral
    (R := 𝓞 ℚ) (S := 𝓞 F) qv.asIdeal
    (by simp [(RingHom.injective_iff_ker_eq_bot _).mp
      (FaithfulSMul.algebraMap_injective (𝓞 ℚ) (𝓞 F))])
  haveI : Q.IsMaximal := hQmax
  haveI : Q.IsPrime := hQmax.isPrime
  -- the arithmetic Frobenius at `Q`, as an element of `Gal(F/ℚ)`
  set e := galRestrict (𝓞 ℚ) ℚ F (𝓞 F) with he
  set σ₀ : 𝓞 F ≃ₐ[𝓞 ℚ] 𝓞 F := arithFrobAt (𝓞 ℚ) (𝓞 F ≃ₐ[𝓞 ℚ] 𝓞 F) Q with hσ₀def
  have hσ₀ : IsArithFrobAt (𝓞 ℚ) σ₀ Q := IsArithFrobAt.arithFrobAt _ _ _
  set σ : F ≃ₐ[ℚ] F := e.symm σ₀ with hσdef
  -- the Brauer identity at `σ`: some piece is supported at some conjugate of `σ`
  have hex : ∃ (i : Fin n) (x : F ≃ₐ[ℚ] F), x⁻¹ * σ * x ∈ H i := by
    by_contra hcon
    push Not at hcon
    have h1 := hbrauer σ
    rw [Finset.sum_eq_zero (fun i _ => by
      rw [Finset.sum_eq_zero (fun x _ => hφ0 i _ (hcon i x)), mul_zero])] at h1
    exact zero_ne_one h1
  obtain ⟨i, x, hxH⟩ := hex
  set g : F ≃ₐ[ℚ] F := x⁻¹ * σ * x with hgdef
  set τ₀ : 𝓞 F ≃ₐ[𝓞 ℚ] 𝓞 F := e x⁻¹ with hτ₀def
  have hgconj : e g = τ₀ * σ₀ * τ₀⁻¹ := by
    rw [hgdef, hτ₀def, map_mul, map_mul, hσdef, MulEquiv.apply_symm_apply, map_inv, inv_inv]
  -- `g ∈ Hᵢ` is a Frobenius at the conjugated prime `Q'`, still over `q`
  set Q' : Ideal (𝓞 F) := τ₀ • Q with hQ'def
  have hfrobQ' : IsArithFrobAt (𝓞 ℚ) (e g) Q' := by
    rw [hgconj]; exact hσ₀.conj τ₀
  haveI : Q'.IsPrime := Ideal.IsPrime.smul τ₀
  have hQ'under : Q'.under (𝓞 ℚ) = qv.asIdeal := by
    rw [← hQunder]
    ext a
    rw [Ideal.under, Ideal.mem_comap, Ideal.mem_comap, hQ'def,
      Ideal.mem_pointwise_smul_iff_inv_smul_mem,
      show τ₀⁻¹ • (algebraMap (𝓞 ℚ) (𝓞 F) a) = algebraMap (𝓞 ℚ) (𝓞 F) a from
        (τ₀⁻¹ : 𝓞 F ≃ₐ[𝓞 ℚ] 𝓞 F).commutes a]
  have hQ'ne : Q' ≠ ⊥ := by
    intro h
    rw [h] at hQ'under
    rw [Ideal.under, Ideal.comap_bot_of_injective _
      (FaithfulSMul.algebraMap_injective (𝓞 ℚ) (𝓞 F))] at hQ'under
    exact qv.ne_bot hQ'under.symm
  -- the place `w` of `Kᵢ` below `Q'`
  set QH : HeightOneSpectrum (𝓞 F) := ⟨Q', inferInstance, hQ'ne⟩ with hQHdef
  set w : HeightOneSpectrum (𝓞 (IntermediateField.fixedField (H i))) :=
    QH.under (𝓞 (IntermediateField.fixedField (H i))) with hwdef
  have hwq : w.under (𝓞 ℚ) = qv := by
    apply HeightOneSpectrum.ext
    show (Q'.under (𝓞 (IntermediateField.fixedField (H i)))).under (𝓞 ℚ) = qv.asIdeal
    rw [Ideal.under_under]
    exact hQ'under
  -- `w` avoids the bad set, since `q` was taken outside `S₀`
  have hwS : w ∉ S i := by
    intro hmem
    exact hqS₀ (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i,
      Finset.mem_image.mpr ⟨w, hmem, hwq⟩⟩)
  -- `g ∈ Hᵢ` fixes `Kᵢ = F^{Hᵢ}`, hence fixes `𝓞_{Kᵢ}` inside `𝓞 F`
  have hfix : ∀ a : 𝓞 (IntermediateField.fixedField (H i)),
      (e g) (algebraMap (𝓞 (IntermediateField.fixedField (H i))) (𝓞 F) a)
        = algebraMap (𝓞 (IntermediateField.fixedField (H i))) (𝓞 F) a := by
    intro a
    apply FaithfulSMul.algebraMap_injective (𝓞 F) F
    rw [algebraMap_galRestrict_apply (𝓞 ℚ) g]
    rw [← IsScalarTower.algebraMap_apply (𝓞 (IntermediateField.fixedField (H i))) (𝓞 F) F,
      IsScalarTower.algebraMap_apply (𝓞 (IntermediateField.fixedField (H i)))
        (IntermediateField.fixedField (H i)) F]
    exact ((IntermediateField.mem_fixedField_iff (H i) _).mp
      (algebraMap (𝓞 (IntermediateField.fixedField (H i)))
        (IntermediateField.fixedField (H i)) a).2 g hxH)
  -- so the Frobenius congruence at `Q'` becomes `z ^ #(𝓞_ℚ/q) = z` on `𝓞_{Kᵢ}/w`
  have hpow : ∀ z : 𝓞 (IntermediateField.fixedField (H i)) ⧸ w.asIdeal,
      z ^ (Nat.card (𝓞 ℚ ⧸ qv.asIdeal)) = z := by
    intro z
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective z
    rw [← map_pow, Ideal.Quotient.eq]
    show a ^ _ - a ∈ Q'.under (𝓞 (IntermediateField.fixedField (H i)))
    rw [Ideal.under, Ideal.mem_comap, map_sub, map_pow]
    have h1 := hfrobQ' (algebraMap (𝓞 (IntermediateField.fixedField (H i))) (𝓞 F) a)
    rw [hQ'under] at h1
    have h2 : (MulSemiringAction.toAlgHom (𝓞 ℚ) (𝓞 F) (e g))
        (algebraMap (𝓞 (IntermediateField.fixedField (H i))) (𝓞 F) a)
        = algebraMap (𝓞 (IntermediateField.fixedField (H i))) (𝓞 F) a := hfix a
    rw [h2] at h1
    have h3 := (Ideal.neg_mem_iff Q').mpr h1
    rwa [neg_sub] at h3
  have hNge : 2 ≤ Nat.card (𝓞 ℚ ⧸ qv.asIdeal) := by
    haveI : Field (𝓞 ℚ ⧸ qv.asIdeal) := Ideal.Quotient.field _
    exact Finite.one_lt_card
  -- the two inequalities give the residue-cardinality equality
  have hcard : Nat.card (𝓞 ℚ ⧸ qv.asIdeal)
      = Nat.card (𝓞 (IntermediateField.fixedField (H i)) ⧸ w.asIdeal) := by
    refine le_antisymm ?_ (card_le_of_pow_eq_self hNge hpow)
    refine Nat.card_le_card_of_injective
      (Ideal.quotientMap w.asIdeal
        (algebraMap (𝓞 ℚ) (𝓞 (IntermediateField.fixedField (H i))))
        (le_of_eq (congrArg HeightOneSpectrum.asIdeal hwq).symm))
      (Ideal.quotientMap_injective' (le_of_eq (congrArg HeightOneSpectrum.asIdeal hwq)))
  obtain ⟨ε, hεint, hεcomm⟩ := exists_adicCompletionHom_of_under w qv hwq
  exact ⟨i, w, hwS, hcard, ε, hεint, hεcomm⟩

end DegreeOnePlaces

/-- **The induced-trace expansion at a rational Frobenius** (PROVEN
2026-07-25 from the arithmetic leaf `exists_degreeOnePlace_of_brauer`
above; the Mackey/degree-one-places content of the `ℓ`-adic Brauer
descent, and the ONLY remaining arithmetic input of the whole descent):
given a Brauer decomposition of the trivial character of `Gal(F/ℚ)`
into one-dimensional pieces `φ i` supported on subgroups `H i`
(`hbrauer`, `hφ0`, `hφ1`, `hφmul`) and, for each piece, a finite bad set
`S i` of places of the fixed field `Kᵢ = F^{H i}`, the trace coefficient
of `ρ` at almost every rational Frobenius is a finite `E`-weighted sum
of the trace coefficients of the RESTRICTIONS `ρ|_{G_{Kᵢ}}` at good
places of the `Kᵢ`.

Classically (Serre, *Abelian ℓ-adic Representations*, I.2; BLGGT §5.3):
tensoring the virtual identity
`Σᵢ cᵢ · Ind_{Hᵢ}^{Gal(F/ℚ)} χᵢ = 1` with `ρ` and applying the
projection formula gives
`Σᵢ cᵢ · Ind_{G_{Kᵢ}}^{G_ℚ} (ρ|_{G_{Kᵢ}} ⊗ χᵢ) = ρ` as virtual
representations of `G_ℚ`. Evaluating traces at `Frob_q` for `q`
unramified in `F` and away from all bad data, the Mackey/Frobenius
formula for induced characters evaluates each induced trace as the sum
over the DEGREE-ONE places `w | q` of `Kᵢ` of
`χᵢ(Frob_w) · tr ρ|_{G_{Kᵢ}}(Frob_w)`. So the index family
`(idx j, pl j)` of the conclusion enumerates the pairs `(i, w)` with
`w | q` of degree one, and the weight `e j` is `c_{idx j} · χ_{idx j}(Frob_w)`
— a rational multiple of a root of unity, hence an element of the Hecke
field `E` by the carrier's normalization (`E` is a number field, so a
`ℚ`-algebra: the rational Artin coefficients `cᵢ` need no integrality,
see the RATIONAL COEFFICIENTS note on the consumer below). The places
`w` occurring avoid `S (idx j)` because `S₀` collects, besides the
primes ramified in `F`, every rational prime lying under a place of some
`S i`.

Note the shape of the cut: this leaf mentions NEITHER the descended
polynomial families `P i` NOR `ψℓ`; it is purely the identity between
`ℓ`-adic Frobenius traces of `ρ` and of its restrictions to the fixed
fields. Feeding the descended systems `hP` back in — i.e. replacing
each restricted trace by `ψℓ((P i w).coeff 1)` — is the formal
bookkeeping done in `heckeField_trace_mem_range_of_pieces` below.

Literature: Barnet-Lamb–Gee–Geraghty–Taylor, *Potential automorphy and
change of weight*, Ann. of Math. 179 (2014), §5.3; Khare–Wintenberger,
*Serre's modularity conjecture (I)*, Invent. Math. 178 (2009), §5;
Dieulefait, J. reine angew. Math. 577 (2004); Serre, *Abelian ℓ-adic
Representations*, I.2 (induced traces via degree-one places).

SOUNDNESS AUDIT (both ways, inherited verbatim from the consumer, whose
hypothesis list this leaf reproduces): (i) direct — for a carrier and
pieces produced by their own leaves this is BLGGT §5.3; for abstract
data the abstract-quantification caveat of pillar β applies (in
particular nothing formal ties the `φ i`-values into `E` — that
identification is part of the citation, discharged by the carrier's
normalization, and is exactly why the weights `e` are existentially
quantified in `E` here), and (ii) collapse — the hypothesis set already
contains an irreducible hardly ramified mod-`ℓ` representation with
`ℓ ≥ 5` (`hρbar`, `hirr`, `hℓ5`), which the headline
`not_isIrreducible_of_isHardlyRamified_of_five_le` of this module shows
is classically unsatisfiable, so the statement is classically true for
every package.

CIRCULARITY GUARD (inherited from pillar β, load-bearing): no discharge
through `Family.lean`, `Lift.lean`, or `Modularity/Interface.lean`.

ASSEMBLY (2026-07-25). The arithmetic content is now isolated ONE level
up, in `exists_degreeOnePlace_of_brauer`, and the whole of what remains
here is PROVEN. The route is `charFrob_map_of_adicCompletionHom`: a
place `w` of `Kᵢ` of residue degree ONE over `q` sees the same Frobenius
conjugacy class as `q` itself, so
`(ρ|_{G_{Kᵢ}}).charFrob w = ρ.charFrob q` on the nose, and the expansion
holds with the SINGLE term `m = 1`, `e = 1`. `hρ.isUnramified` supplies
the unramifiedness of `ρ` at `q` that this needs (`q ≠ 2, ℓ`).

FORMAL-CONTENT AUDIT (2026-07-25 — report to a cut-level owner, this is
NOT vacuity but it is weaker than the headline suggests). The statement
existentially quantifies `m`, `idx`, `pl` and the weights `e` with no
constraint tying them to the Mackey/Frobenius formula, so it does NOT
assert the induced-character expansion over ALL degree-one places `w | q`
with weights `cᵢ · χᵢ(Frob_w)`; a single degree-one place with weight `1`
discharges it. What it does assert, and all it asserts, is:

* SOME Brauer piece `Kᵢ` has a good place of residue degree one over
  almost every rational prime (the `exists_degreeOnePlace_of_brauer`
  leaf — genuinely the Brauer content, and false without `hbrauer`), and
* the trace coefficient of `ρ` at `q` is recovered from the restriction
  `ρ|_{G_{Kᵢ}}` at that place.

That is sufficient for the sole consumer,
`heckeField_trace_mem_range_of_pieces`, whose conclusion is only the
membership `ιO(tr ρ(Frob_q)) ∈ ψℓ(E)` — so no downstream statement is
weakened, and nothing here needs repair. It is recorded because a reader
of the docstring above would reasonably expect the full projection
formula, and because a future consumer wanting the actual weights
`cᵢ · χᵢ(Frob_w)` must strengthen the STATEMENT rather than reuse this
one. The hypotheses the present proof does not consume are
underscore-prefixed so the emptiness is mechanically visible rather than
merely asserted: `_hℓ5`, `_hZinj`, `_hρbar`, `_hirr`, `_hπsurj`, `_hπ`
(`hrank` and `hW` survive only inside the types of `hρ` and `_hρbar`).
They are RETAINED rather than deleted because the consumer applies this
leaf positionally with its own hypothesis list, and because a
strengthened restatement — the actual projection formula, with weights
`cᵢ · χᵢ(Frob_w)` over all degree-one `w | q` — would need the residual
data back. -/
theorem exists_inducedTrace_expansion_of_brauer
    {ℓ : ℕ} (hℓodd : Odd ℓ) [Fact ℓ.Prime] (_hℓ5 : 5 ≤ ℓ)
    {O : Type u} [CommRing O] [IsDomain O] [TopologicalSpace O]
    [IsTopologicalRing O] [Algebra ℤ_[ℓ] O] [IsLocalRing O]
    [Module.Finite ℤ_[ℓ] O] [IsModuleTopology ℤ_[ℓ] O]
    (_hZinj : Function.Injective (algebraMap ℤ_[ℓ] O))
    {ρ : GaloisRep ℚ O (Fin 2 → O)}
    (hrank : Module.rank O (Fin 2 → O) = 2)
    (hρ : IsHardlyRamified hℓodd hrank ρ)
    {k : Type u} [Field k] [Finite k] [Algebra ℤ_[ℓ] k]
    [TopologicalSpace k] [DiscreteTopology k]
    {W : Type v} [AddCommGroup W] [Module k W] [Module.Finite k W]
    [Module.Free k W]
    (hW : Module.rank k W = 2) {ρbar : GaloisRep ℚ k W}
    (_hρbar : IsHardlyRamified hℓodd hW ρbar)
    (_hirr : ρbar.IsIrreducible)
    (π : O →+* k) (_hπsurj : Function.Surjective π)
    (_hπ : ∀ (q : ℕ) (hq : q.Prime), q ≠ 2 → q ≠ ℓ →
      (ρ.charFrob hq.toHeightOneSpectrumRingOfIntegersRat).map π =
        ρbar.charFrob hq.toHeightOneSpectrumRingOfIntegersRat)
    (Wit : PotentialModularityWitness ℓ O ρ)
    (n : ℕ) (H : Fin n → Subgroup (Wit.F ≃ₐ[ℚ] Wit.F))
    (φ : Fin n → (Wit.F ≃ₐ[ℚ] Wit.F) → ℂ) (c : Fin n → ℚ)
    (hφ0 : ∀ i, ∀ g ∉ H i, φ i g = 0)
    (hφ1 : ∀ i, φ i 1 = 1)
    (hφmul : ∀ i, ∀ a ∈ H i, ∀ b ∈ H i, φ i (a * b) = φ i a * φ i b)
    (hbrauer : ∀ g : Wit.F ≃ₐ[ℚ] Wit.F,
      ∑ i, (c i : ℂ) * (Nat.card (H i) : ℂ)⁻¹ *
        ∑ x : Wit.F ≃ₐ[ℚ] Wit.F, φ i (x⁻¹ * g * x) = 1)
    (S : ∀ i, Finset (HeightOneSpectrum (NumberField.RingOfIntegers
      (IntermediateField.fixedField (H i))))) :
    ∃ S₀ : Finset (HeightOneSpectrum (NumberField.RingOfIntegers ℚ)),
      ∀ (q : ℕ) (hq : q.Prime),
        hq.toHeightOneSpectrumRingOfIntegersRat ∉ S₀ →
        q ≠ 2 → q ≠ 3 → q ≠ ℓ →
        ∃ (m : ℕ) (idx : Fin m → Fin n)
          (pl : ∀ j : Fin m, HeightOneSpectrum (NumberField.RingOfIntegers
            (IntermediateField.fixedField (H (idx j)))))
          (e : Fin m → Wit.E),
          (∀ j, pl j ∉ S (idx j)) ∧
          Wit.ιO ((ρ.charFrob
              hq.toHeightOneSpectrumRingOfIntegersRat).coeff 1) =
            ∑ j, Wit.ψℓ (e j) *
              Wit.ιO (((ρ.map (algebraMap ℚ (IntermediateField.fixedField
                (H (idx j))))).charFrob (pl j)).coeff 1) := by
  classical
  haveI := Wit.galoisF
  -- the arithmetic input: some piece has a good degree-one place over `q`
  obtain ⟨S₀, hS₀⟩ := exists_degreeOnePlace_of_brauer (F := Wit.F) n H φ c
    hφ0 hφ1 hφmul hbrauer S
  refine ⟨S₀, ?_⟩
  intro q hq hqS hq2 hq3 hqℓ
  obtain ⟨i, w, hwS, hcard, ε, hεint, hεcomm⟩ := hS₀ q hq hqS
  -- a degree-one place sees the same Frobenius conjugacy class as `q`
  have hchar : (ρ.map (algebraMap ℚ (IntermediateField.fixedField (H i)))).charFrob w
      = ρ.charFrob hq.toHeightOneSpectrumRingOfIntegersRat :=
    charFrob_map_of_adicCompletionHom ρ
      (algebraMap ℚ (IntermediateField.fixedField (H i)))
      hq.toHeightOneSpectrumRingOfIntegersRat w
      (hρ.isUnramified q hq ⟨hq2, hqℓ⟩) ε hεint hcard hεcomm
  -- so the expansion holds with the single term `m = 1`, weight `1`
  refine ⟨1, fun _ => i, fun _ => w, fun _ => 1, fun _ => hwS, ?_⟩
  rw [Fin.sum_univ_one, map_one, one_mul, hchar]

/-- **Brauer gluing, trace coefficient — the induced-character
expansion** (PROVEN 2026-07-25 from the induced-trace expansion leaf
`exists_inducedTrace_expansion_of_brauer` above; the arithmetic HALF of
the Brauer gluing below, and the only coefficient carrying automorphy
content): given a Brauer decomposition of the trivial character of
`Gal(F/ℚ)` into solvable-induced one-dimensional pieces
(`hbrauer`) and, for each
piece, a descended Hecke system over the fixed field `Kᵢ = F^{H i}`
(`hP`), the TRACE of Frobenius of `ρ` itself at almost all rational
primes lies in `ψℓ(E)` through `ιO` — equivalently, so does the linear
coefficient `coeff 1 = −tr` of the Frobenius characteristic polynomial.

Classically (Serre, *Abelian ℓ-adic Representations*, I.2; BLGGT §5.3):
tensoring the virtual identity
`Σᵢ cᵢ · Ind_{Hᵢ}^{Gal(F/ℚ)} χᵢ = 1` with `ρ` and applying the
projection formula gives
`Σᵢ cᵢ · Ind_{G_{Kᵢ}}^{G_ℚ} (ρ|_{G_{Kᵢ}} ⊗ χᵢ) = ρ` as virtual
representations of `G_ℚ`. Taking traces at `Frob_q` for `q` unramified
in `F` and away from all bad data, the Mackey/Frobenius formula for
induced traces evaluates each induced trace as the sum over the
DEGREE-ONE places `w | q` of `Kᵢ` of `χᵢ(Frob_w) · a_w`, where `a_w` is
the trace coefficient of the descended piece at `w` — an element of
`ψℓ(E)` by `hP` — and `χᵢ(Frob_w)` is a root of unity lying in `E` by
the carrier's normalization (`E` is the Hecke field OF THE DESCENDED
system). Hence `ιO(tr ρ(Frob_q)) ∈ ψℓ(E)`. The exceptional set `S₀`
collects the primes ramified in `F` and the primes below the pieces'
bad sets `S i`.

Literature: Barnet-Lamb–Gee–Geraghty–Taylor, *Potential automorphy and
change of weight*, Ann. of Math. 179 (2014), §5.3; Khare–Wintenberger,
*Serre's modularity conjecture (I)*, Invent. Math. 178 (2009), §5;
Dieulefait, J. reine angew. Math. 577 (2004); Serre, *Abelian ℓ-adic
Representations*, I.2 (induced traces via degree-one places).

SOUNDNESS AUDIT (both ways, 2026-07-24): (i) direct — for a carrier and
pieces produced by their own leaves this is BLGGT §5.3; for abstract
data the abstract-quantification caveat of pillar β applies (in
particular nothing formal ties the `φ i`-values into `E` — that
identification is part of the citation, discharged by the carrier's
normalization), and (ii) collapse — the hypothesis set (an irreducible
hardly ramified mod-`ℓ` representation, `ℓ ≥ 5`) is classically
unsatisfiable (headline below), so the statement is classically true
for every package.

CIRCULARITY GUARD (inherited from pillar β, load-bearing): no discharge
through `Family.lean`, `Lift.lean`, or `Modularity/Interface.lean`.

ASSEMBLY (2026-07-25): the arithmetic content is now isolated ONE level
down, in `exists_inducedTrace_expansion_of_brauer` above, which consumes
the Brauer data (`hbrauer`, `hφ0`, `hφ1`, `hφmul`) and the pieces' bad
sets `S` and returns the Mackey expansion of the trace coefficient of
`ρ` as a finite `E`-weighted sum of the trace coefficients of the
restrictions `ρ|_{G_{Kᵢ}}` at good places `w ∉ S i`. What remains here
is pure bookkeeping and IS proven: each restricted trace coefficient is
`ψℓ((P i w).coeff 1)` by `hP` read off in degree `1`
(`Polynomial.coeff_map`), so the whole expansion is the `ψℓ`-image of
the single element `Σⱼ eⱼ · (P (idx j) (pl j)).coeff 1` of `E` — using
only that `ψℓ` is a ring homomorphism (`map_sum`, `map_mul`). No
integrality, and no property of the weights beyond membership in `E`,
is used. -/
theorem heckeField_trace_mem_range_of_pieces
    {ℓ : ℕ} (hℓodd : Odd ℓ) [Fact ℓ.Prime] (hℓ5 : 5 ≤ ℓ)
    {O : Type u} [CommRing O] [IsDomain O] [TopologicalSpace O]
    [IsTopologicalRing O] [Algebra ℤ_[ℓ] O] [IsLocalRing O]
    [Module.Finite ℤ_[ℓ] O] [IsModuleTopology ℤ_[ℓ] O]
    (hZinj : Function.Injective (algebraMap ℤ_[ℓ] O))
    {ρ : GaloisRep ℚ O (Fin 2 → O)}
    (hrank : Module.rank O (Fin 2 → O) = 2)
    (hρ : IsHardlyRamified hℓodd hrank ρ)
    {k : Type u} [Field k] [Finite k] [Algebra ℤ_[ℓ] k]
    [TopologicalSpace k] [DiscreteTopology k]
    {W : Type v} [AddCommGroup W] [Module k W] [Module.Finite k W]
    [Module.Free k W]
    (hW : Module.rank k W = 2) {ρbar : GaloisRep ℚ k W}
    (hρbar : IsHardlyRamified hℓodd hW ρbar)
    (hirr : ρbar.IsIrreducible)
    (π : O →+* k) (hπsurj : Function.Surjective π)
    (hπ : ∀ (q : ℕ) (hq : q.Prime), q ≠ 2 → q ≠ ℓ →
      (ρ.charFrob hq.toHeightOneSpectrumRingOfIntegersRat).map π =
        ρbar.charFrob hq.toHeightOneSpectrumRingOfIntegersRat)
    (Wit : PotentialModularityWitness ℓ O ρ)
    (n : ℕ) (H : Fin n → Subgroup (Wit.F ≃ₐ[ℚ] Wit.F))
    (φ : Fin n → (Wit.F ≃ₐ[ℚ] Wit.F) → ℂ) (c : Fin n → ℚ)
    (hφ0 : ∀ i, ∀ g ∉ H i, φ i g = 0)
    (hφ1 : ∀ i, φ i 1 = 1)
    (hφmul : ∀ i, ∀ a ∈ H i, ∀ b ∈ H i, φ i (a * b) = φ i a * φ i b)
    (hbrauer : ∀ g : Wit.F ≃ₐ[ℚ] Wit.F,
      ∑ i, (c i : ℂ) * (Nat.card (H i) : ℂ)⁻¹ *
        ∑ x : Wit.F ≃ₐ[ℚ] Wit.F, φ i (x⁻¹ * g * x) = 1)
    (S : ∀ i, Finset (HeightOneSpectrum (NumberField.RingOfIntegers
      (IntermediateField.fixedField (H i)))))
    (P : ∀ i, HeightOneSpectrum (NumberField.RingOfIntegers
      (IntermediateField.fixedField (H i))) → Polynomial Wit.E)
    (hP : ∀ i, ∀ w ∉ S i,
      ((ρ.map (algebraMap ℚ (IntermediateField.fixedField
          (H i)))).charFrob w).map Wit.ιO = (P i w).map Wit.ψℓ) :
    ∃ S₀ : Finset (HeightOneSpectrum (NumberField.RingOfIntegers ℚ)),
      ∀ (q : ℕ) (hq : q.Prime),
        hq.toHeightOneSpectrumRingOfIntegersRat ∉ S₀ →
        q ≠ 2 → q ≠ 3 → q ≠ ℓ →
        Wit.ιO ((ρ.charFrob
            hq.toHeightOneSpectrumRingOfIntegersRat).coeff 1)
          ∈ Set.range Wit.ψℓ := by
  classical
  -- the arithmetic input: the Mackey expansion of the rational trace
  -- coefficient over the pieces' good places
  obtain ⟨S₀, hexp⟩ := exists_inducedTrace_expansion_of_brauer hℓodd hℓ5 hZinj
    hrank hρ hW hρbar hirr π hπsurj hπ Wit n H φ c hφ0 hφ1 hφmul hbrauer S
  refine ⟨S₀, ?_⟩
  intro q hq hqS hq2 hq3 hqℓ
  obtain ⟨m, idx, pl, e, hpl, hid⟩ := hexp q hq hqS hq2 hq3 hqℓ
  -- each restricted trace coefficient is the `ψℓ`-image of the descended
  -- piece's own trace coefficient: read `hP` off in degree `1`
  have hcoeff : ∀ j : Fin m,
      Wit.ιO (((ρ.map (algebraMap ℚ (IntermediateField.fixedField
          (H (idx j))))).charFrob (pl j)).coeff 1) =
        Wit.ψℓ ((P (idx j) (pl j)).coeff 1) := fun j => by
    simpa only [Polynomial.coeff_map] using
      congrArg (fun p => Polynomial.coeff p 1) (hP (idx j) (pl j) (hpl j))
  -- so the whole expansion is the `ψℓ`-image of one element of `E`
  refine ⟨∑ j, e j * (P (idx j) (pl j)).coeff 1, ?_⟩
  rw [hid, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_mul, hcoeff j]

/-- **Brauer gluing — reconstruction of the rational eigensystem from
the descended pieces** (PROVEN; the induced-character unwinding of
the `ℓ`-adic Brauer descent): given a Brauer decomposition of the
trivial character of `Gal(F/ℚ)` into solvable-induced one-dimensional
pieces (`hbrauer`, as produced by `brauer_induction_trivial_character`)
and, for each piece, a descended Hecke system over the fixed field
`Kᵢ = F^{H i}` (`hP`, as produced by
`exists_descended_heckeSystem_of_solvable`), the Frobenius
characteristic polynomials of `ρ` itself at almost all RATIONAL primes
are `E`-coefficient polynomials through `ιO`/`ψℓ`.

Classically: tensoring the virtual identity
`Σᵢ cᵢ · Ind_{Hᵢ}^{Gal(F/ℚ)} χᵢ = 1` with `ρ` and applying the
projection formula gives
`Σᵢ cᵢ · Ind_{G_{Kᵢ}}^{G_ℚ} (ρ|_{G_{Kᵢ}} ⊗ χᵢ) = ρ` as virtual
representations of `G_ℚ`. Taking traces at `Frob_q` for `q` unramified
in `F` and away from all bad data, the Mackey/Frobenius formula for
induced traces (Serre, *Abelian ℓ-adic Representations*, I.2)
evaluates each induced trace as the sum over the DEGREE-ONE places
`w | q` of `Kᵢ` of `χᵢ(Frob_w) · a_w`, where `a_w` is the trace
coefficient of the descended piece at `w` — an element of `ψℓ(E)` by
`hP` — and `χᵢ(Frob_w)` is a root of unity lying in `E` by the
carrier's normalization (`E` is the Hecke field of the descended
system; the consumer docstring's parenthetical). Hence
`ιO(tr ρ(Frob_q)) ∈ ψℓ(E)`. The determinant coefficient of the
charpoly is the image of `q` itself (cyclotomic determinant,
`hρ.det`), rational hence in `ψℓ(E)`; the charpoly is monic of degree
`2`; so the full polynomial is the `ψℓ`-image of an `E`-polynomial.
The exceptional set `S₀` collects the primes ramified in `F` and the
primes below the pieces' bad sets `S i`.

RATIONAL COEFFICIENTS (2026-07-24): the Brauer/Artin coefficients `c i`
are `ℚ`-valued, not `ℤ`-valued — this is the shape in which the
group-theoretic node `brauer_induction_trivial_character` is PROVEN
(Artin induction over cyclic subgroups; see its RESTATEMENT note). The
gluing above is insensitive to the difference: it only ever forms the
combination `Σᵢ cᵢ · aᵢ` of trace coefficients `aᵢ` lying in the Hecke
field `E`, and `E` is a number field, hence a `ℚ`-algebra, so a
rational combination of elements of `E` is again an element of `E`.
Integrality of the `cᵢ` is nowhere used.

Literature: Barnet-Lamb–Gee–Geraghty–Taylor, *Potential automorphy
and change of weight*, Ann. of Math. 179 (2014), §5.3 (gluing the
descended systems through Brauer's theorem into a weakly compatible
system over the base — verbatim this step); Khare–Wintenberger,
*Serre's modularity conjecture (I)*, Invent. Math. 178 (2009), §5;
Dieulefait, J. reine angew. Math. 577 (2004); Serre, *Abelian ℓ-adic
Representations*, I.2 (induced traces via degree-one places).

SOUNDNESS AUDIT (both ways, 2026-07-24): (i) direct — for a carrier
and pieces produced by their own leaves this is BLGGT §5.3; for
abstract data the abstract-quantification caveat of pillar β applies
(in particular nothing formal ties the `φ i`-values into `E` — that
identification is part of the citation, discharged by the carrier's
normalization), and (ii) collapse — the hypothesis set is classically
unsatisfiable (headline below), so the statement is classically true
for every package.

CIRCULARITY GUARD (inherited from pillar β, load-bearing): no
discharge through `Family.lean`, `Lift.lean`, or
`Modularity/Interface.lean`.

ASSEMBLY (2026-07-24, PROVEN over a coefficientwise split): the monic
quadratic `charFrob` has exactly three coefficients to place inside
`ψℓ(E)`, and only ONE of them is arithmetic.

* `coeff 1` (the TRACE, the induced-character unwinding proper) is the
  residual arithmetic leaf `heckeField_trace_mem_range_of_pieces`,
  which consumes the Brauer data (`hbrauer`, `hφ0`, `hφ1`, `hφmul`) and
  the descended piece systems (`hP`) exactly as this statement received
  them, and produces the exceptional set `S₀`;
* `coeff 0` (the DETERMINANT) is `q` by
  `charFrob_coeff_zero_eq_natCast_of_isHardlyRamified` — PROVEN above
  from the cyclotomic-determinant field of `IsHardlyRamified` over the
  equally PROVEN `cyclotomicCharacter_adicArithFrob_eq_natCast` (ported
  into this module because the circularity guard forbids importing
  `Family.lean`, where the same statement is already proven) — and
  `ψℓ`/`ιO` agree on `ℕ`-casts, so it lands in `ψℓ(E)` formally;
* `coeff 2 = 1` and `coeff (m+3) = 0` are monicity and degree
  (`charFrob_monic_of_free`, `charFrob_natDegree_of_rank_two`), hence
  in `ψℓ(E)` formally.

The polynomial family `Pv` itself is then produced with NO further
arithmetic input by `exists_polynomial_family_of_coeff_mem_range`
(`Polynomial.lifts_iff_coeff_lifts` made uniform in the place). So the
depth of this node now lives ENTIRELY in the single trace leaf
`heckeField_trace_mem_range_of_pieces`, which the guard above binds. -/
theorem exists_heckeField_system_of_witness_of_pieces
    {ℓ : ℕ} (hℓodd : Odd ℓ) [Fact ℓ.Prime] (hℓ5 : 5 ≤ ℓ)
    {O : Type u} [CommRing O] [IsDomain O] [TopologicalSpace O]
    [IsTopologicalRing O] [Algebra ℤ_[ℓ] O] [IsLocalRing O]
    [Module.Finite ℤ_[ℓ] O] [IsModuleTopology ℤ_[ℓ] O]
    (hZinj : Function.Injective (algebraMap ℤ_[ℓ] O))
    {ρ : GaloisRep ℚ O (Fin 2 → O)}
    (hrank : Module.rank O (Fin 2 → O) = 2)
    (hρ : IsHardlyRamified hℓodd hrank ρ)
    {k : Type u} [Field k] [Finite k] [Algebra ℤ_[ℓ] k]
    [TopologicalSpace k] [DiscreteTopology k]
    {W : Type v} [AddCommGroup W] [Module k W] [Module.Finite k W]
    [Module.Free k W]
    (hW : Module.rank k W = 2) {ρbar : GaloisRep ℚ k W}
    (hρbar : IsHardlyRamified hℓodd hW ρbar)
    (hirr : ρbar.IsIrreducible)
    (π : O →+* k) (hπsurj : Function.Surjective π)
    (hπ : ∀ (q : ℕ) (hq : q.Prime), q ≠ 2 → q ≠ ℓ →
      (ρ.charFrob hq.toHeightOneSpectrumRingOfIntegersRat).map π =
        ρbar.charFrob hq.toHeightOneSpectrumRingOfIntegersRat)
    (Wit : PotentialModularityWitness ℓ O ρ)
    (n : ℕ) (H : Fin n → Subgroup (Wit.F ≃ₐ[ℚ] Wit.F))
    (φ : Fin n → (Wit.F ≃ₐ[ℚ] Wit.F) → ℂ) (c : Fin n → ℚ)
    (hφ0 : ∀ i, ∀ g ∉ H i, φ i g = 0)
    (hφ1 : ∀ i, φ i 1 = 1)
    (hφmul : ∀ i, ∀ a ∈ H i, ∀ b ∈ H i, φ i (a * b) = φ i a * φ i b)
    (hbrauer : ∀ g : Wit.F ≃ₐ[ℚ] Wit.F,
      ∑ i, (c i : ℂ) * (Nat.card (H i) : ℂ)⁻¹ *
        ∑ x : Wit.F ≃ₐ[ℚ] Wit.F, φ i (x⁻¹ * g * x) = 1)
    (S : ∀ i, Finset (HeightOneSpectrum (NumberField.RingOfIntegers
      (IntermediateField.fixedField (H i)))))
    (P : ∀ i, HeightOneSpectrum (NumberField.RingOfIntegers
      (IntermediateField.fixedField (H i))) → Polynomial Wit.E)
    (hP : ∀ i, ∀ w ∉ S i,
      ((ρ.map (algebraMap ℚ (IntermediateField.fixedField
          (H i)))).charFrob w).map Wit.ιO = (P i w).map Wit.ψℓ) :
    ∃ (S₀ : Finset (HeightOneSpectrum (NumberField.RingOfIntegers ℚ)))
      (Pv : HeightOneSpectrum (NumberField.RingOfIntegers ℚ) →
        Polynomial Wit.E),
      ∀ (q : ℕ) (hq : q.Prime),
        hq.toHeightOneSpectrumRingOfIntegersRat ∉ S₀ →
        q ≠ 2 → q ≠ 3 → q ≠ ℓ →
        (ρ.charFrob hq.toHeightOneSpectrumRingOfIntegersRat).map Wit.ιO =
          (Pv hq.toHeightOneSpectrumRingOfIntegersRat).map Wit.ψℓ := by
  classical
  -- (i) the arithmetic half: the induced-character expansion puts the
  -- TRACE coefficient into `ψℓ(E)` away from a finite set of primes
  obtain ⟨S₀, htr⟩ := heckeField_trace_mem_range_of_pieces hℓodd hℓ5 hZinj
    hrank hρ hW hρbar hirr π hπsurj hπ Wit n H φ c hφ0 hφ1 hφmul hbrauer S P hP
  -- (ii) the formal half: a coefficientwise lift of the whole family
  obtain ⟨Pv, hPv⟩ := exists_polynomial_family_of_coeff_mem_range Wit.ψℓ
    (fun v => (ρ.charFrob v).map Wit.ιO)
  refine ⟨S₀, Pv, ?_⟩
  intro q hq hqS h2 h3 hℓq
  refine hPv _ ?_
  intro m
  simp only [Polynomial.coeff_map]
  match m with
  | 0 =>
    -- the determinant coefficient is the rational integer `q`
    refine ⟨(q : Wit.E), ?_⟩
    rw [charFrob_coeff_zero_eq_natCast_of_isHardlyRamified hℓodd hrank hρ hq
      hℓq, map_natCast, map_natCast]
  | 1 =>
    -- the trace coefficient: the arithmetic leaf
    exact htr q hq hqS h2 h3 hℓq
  | 2 =>
    -- the leading coefficient of a monic quadratic
    refine ⟨1, ?_⟩
    have hmon := (charFrob_monic_of_free
      hq.toHeightOneSpectrumRingOfIntegersRat ρ).coeff_natDegree
    rw [charFrob_natDegree_of_rank_two hq.toHeightOneSpectrumRingOfIntegersRat
      ρ hrank] at hmon
    rw [hmon, map_one, map_one]
  | (m + 3) =>
    -- above the degree everything vanishes
    refine ⟨0, ?_⟩
    have hz : (ρ.charFrob hq.toHeightOneSpectrumRingOfIntegersRat).coeff
        (m + 3) = 0 := by
      refine Polynomial.coeff_eq_zero_of_natDegree_lt ?_
      rw [charFrob_natDegree_of_rank_two hq.toHeightOneSpectrumRingOfIntegersRat
        ρ hrank]
      omega
    rw [hz, map_zero, map_zero]

/-- **Brauer descent, `ℓ`-adic side — the Hecke-field polynomial
system over `ℚ`** (PROVEN 2026-07-24 as an assembly over the three
Brauer-descent nodes above, of which the group-theoretic one
(`brauer_induction_trivial_character`) is itself now PROVEN; the
residual depth lives in `exists_descended_heckeSystem_of_solvable` and
`exists_heckeField_system_of_witness_of_pieces` — see the ASSEMBLY
note at the end of this docstring): given a potential-modularity
carrier for the lift `ρ`, the Frobenius characteristic polynomials of `ρ` at
almost all rational primes descend to the Hecke field `E`: there is a
family `Pv` of `E`-coefficient polynomials with
`charFrob ρ (Frob_q) = Pv(q)` inside `ℚ̄_ℓ` through `ιO`/`ψℓ`, away
from a finite exceptional set.

Classically: `F/ℚ` is Galois (`Wit.galoisF`); Brauer's induction
theorem writes the trivial character of `Gal(F/ℚ)` as a virtual sum
`1 = Σ nᵢ · Ind_{Hᵢ}^{Gal(F/ℚ)} χᵢ` with `Hᵢ` solvable and `χᵢ`
one-dimensional; solvable base change (Langlands) descends the
Hilbert newform to each intermediate field `Fᵢ = F^{Hᵢ}`, so each
`Ind_{G_{Fᵢ}}^{G_ℚ} (ρ|_{G_{Fᵢ}} ⊗ χᵢ)` has Frobenius data with
coefficients in the Hecke field; the virtual sum reconstructs `ρ`,
so its Frobenius characteristic polynomials at primes unramified in
`F` and away from the bad set have coefficients in `E` through `ψℓ`.
(The classical construction may enlarge the Hecke field by the values
of the `χᵢ`; that enlargement happens inside the carrier's `E`, which
is the Hecke field OF THE DESCENDED system.)

Literature: Barnet-Lamb–Gee–Geraghty–Taylor, *Potential automorphy
and change of weight*, Ann. of Math. 179 (2014), §5.3 (the Brauer
trick; rationality of the descended eigensystem);
Khare–Wintenberger, *Serre's modularity conjecture (I)*, Invent.
Math. 178 (2009), §5; Dieulefait, *Existence of families of Galois
representations and new cases of the Fontaine–Mazur conjecture*, J.
reine angew. Math. 577 (2004).

SOUNDNESS AUDIT (both ways, 2026-07-24): (i) direct — for the carrier
produced by the inhabitation leaf this is BLGGT §5.3; for an abstract
carrier the abstract-quantification caveat of pillar β applies, and
(ii) collapse — the hypothesis set is classically unsatisfiable
(headline below), so the statement is classically true for every
package.

CIRCULARITY GUARD (inherited from pillar β, load-bearing): no
discharge through `Family.lean`, `Lift.lean`, or
`Modularity/Interface.lean`.

ASSEMBLY (2026-07-24, PROVEN): Brauer's induction theorem applied to
the finite group `Gal(F/ℚ)` (`brauer_induction_trivial_character` —
`F/ℚ` is Galois by `Wit.galoisF`, and the group is finite since `F`
is a number field) + per Brauer piece the solvable base change
descent (`exists_descended_heckeSystem_of_solvable`, applied to each
solvable subgroup `H i` via `choose`) + the induced-character gluing
(`exists_heckeField_system_of_witness_of_pieces`), consuming the
Brauer data and the chosen piece systems. UPDATE (2026-07-24): the
group-theoretic leaf is now PROVEN (Artin induction, rational
coefficients — see its RESTATEMENT note), so the residual sorries of
this node are the two ARITHMETIC leaves, both bound by the circularity
guard above. -/
theorem exists_heckeField_system_of_witness
    {ℓ : ℕ} (hℓodd : Odd ℓ) [Fact ℓ.Prime] (hℓ5 : 5 ≤ ℓ)
    {O : Type u} [CommRing O] [IsDomain O] [TopologicalSpace O]
    [IsTopologicalRing O] [Algebra ℤ_[ℓ] O] [IsLocalRing O]
    [Module.Finite ℤ_[ℓ] O] [IsModuleTopology ℤ_[ℓ] O]
    (hZinj : Function.Injective (algebraMap ℤ_[ℓ] O))
    {ρ : GaloisRep ℚ O (Fin 2 → O)}
    (hrank : Module.rank O (Fin 2 → O) = 2)
    (hρ : IsHardlyRamified hℓodd hrank ρ)
    {k : Type u} [Field k] [Finite k] [Algebra ℤ_[ℓ] k]
    [TopologicalSpace k] [DiscreteTopology k]
    {W : Type v} [AddCommGroup W] [Module k W] [Module.Finite k W]
    [Module.Free k W]
    (hW : Module.rank k W = 2) {ρbar : GaloisRep ℚ k W}
    (hρbar : IsHardlyRamified hℓodd hW ρbar)
    (hirr : ρbar.IsIrreducible)
    (π : O →+* k) (hπsurj : Function.Surjective π)
    (hπ : ∀ (q : ℕ) (hq : q.Prime), q ≠ 2 → q ≠ ℓ →
      (ρ.charFrob hq.toHeightOneSpectrumRingOfIntegersRat).map π =
        ρbar.charFrob hq.toHeightOneSpectrumRingOfIntegersRat)
    (Wit : PotentialModularityWitness ℓ O ρ) :
    ∃ (S₀ : Finset (HeightOneSpectrum (NumberField.RingOfIntegers ℚ)))
      (Pv : HeightOneSpectrum (NumberField.RingOfIntegers ℚ) →
        Polynomial Wit.E),
      ∀ (q : ℕ) (hq : q.Prime),
        hq.toHeightOneSpectrumRingOfIntegersRat ∉ S₀ →
        q ≠ 2 → q ≠ 3 → q ≠ ℓ →
        (ρ.charFrob hq.toHeightOneSpectrumRingOfIntegersRat).map Wit.ιO =
          (Pv hq.toHeightOneSpectrumRingOfIntegersRat).map Wit.ψℓ := by
  -- Brauer's induction theorem on the finite group `Gal(F/ℚ)`
  obtain ⟨n, H, φ, c, hsolv, hφ0, hφ1, hφmul, hbrauer⟩ :=
    brauer_induction_trivial_character (Wit.F ≃ₐ[ℚ] Wit.F)
  -- per Brauer piece: solvable base change descends the eigensystem
  -- to the fixed field of `H i`
  choose S P hP using fun i : Fin n =>
    exists_descended_heckeSystem_of_solvable hℓodd hℓ5 hZinj hrank hρ hW
      hρbar hirr π hπsurj hπ Wit (H i) (hsolv i)
  -- glue: the induced-character unwinding reconstructs the rational
  -- eigensystem from the descended pieces
  exact exists_heckeField_system_of_witness_of_pieces hℓodd hℓ5 hZinj
    hrank hρ hW hρbar hirr π hπsurj hπ Wit n H φ c hφ0 hφ1 hφmul hbrauer
    S P hP

/-- **The `3`-adic realization carrier** (interface structure): the
raw Brauer-descended `3`-adic member over `ℚ` attached to the
potential-modularity carrier `Wit` of the lift `ρ` — the coefficient
package `A` (a local ring, finite FREE over `ℤ_3` with its module
topology — the shape the proven `3`-adic classification consumes;
classically the integers of the completion `E_λ`, `λ | 3`, of the
Hecke field), the representation `τ` of `G_ℚ` on `Fin 2 → A`
(classically the Brauer virtual sum
`Σ nᵢ · Ind_{G_{Fᵢ}}^{G_ℚ} (τ_{fᵢ,λ} ⊗ χᵢ)` at the place `λ | 3`, a
TRUE representation by BLGGT §5.3, integrally normalized on a stable
lattice), the injective coefficient embedding `ιA` into `ℚ̄_3`, the
finite exceptional set `S₁`, and the Frobenius compatibility clause
`compat` transporting characteristic polynomials from the `ℓ`-adic
side to the `3`-adic side through the Hecke field: whenever `P ∈ E[X]`
interpolates `charFrob ρ` at `q` through `ψℓ` (such a `P` is unique,
`ψℓ` being injective on the field `E`), then `τ`'s characteristic
polynomial at `q` is `P` through `ψ₃`.

The four hardly ramified conditions on `τ` are deliberately NOT
fields: they are the four condition-transfer leaves below
(`threeadicRealization_det_cyclotomic_of_witness`,
`threeadicRealization_isUnramified_of_witness`,
`threeadicRealization_isFlat_of_witness`,
`threeadicRealization_isTameAtTwo_of_witness`), consumed together with
the construction leaf (`exists_threeadicRealization_of_witness`) by
the PROVEN assembly `exists_threeadic_member_of_witness` — the
per-condition cut of BLGGT Theorem 5.5.1's compatibility transfer.

The two LOCAL-SHAPE clauses — `flatAtThreePow` at `3` and
`stableLineAtTwo` at `2` — ARE fields, and the asymmetry with the
list above is deliberate and load-bearing (CUT-LEVEL REPAIR,
2026-07-25).

`compat` constrains `τ` only through characteristic polynomials of
Frobenius at almost all `q ∉ {2, 3, ℓ}`, hence pins `τ` at most up to
SEMISIMPLIFICATION. The determinant clause survives that — it IS a
Frobenius determinant, which is why
`threeadicRealization_det_cyclotomic_of_witness` is a PROVEN leaf over
`compat` and stays out of the structure. The local shapes at `3` and
at `2` do NOT: finite flatness at `3` is a property of the EXTENSION
CLASS, invisible to semisimplification (the two extensions of `ℤ/3` by
`μ_3` over `ℚ_3` classified by `1` and by `3` in `ℚ_3^×/(ℚ_3^×)^3`
have the same semisimplification and the same Frobenius data, and
exactly one is finite flat over `ℤ_3`), and the local type at `2` is
likewise inertia data at a place where `compat` says nothing at all.
So the two former leaves
(`threeadicRealization_hasFlatProlongationAt_threePow`,
`threeadicRealization_stableLineAtTwo_of_witness`) were
UNDISCHARGEABLE as quantified — over EVERY realization — and no amount
of Fontaine–Laffaille or Weil–Deligne formalization would have changed
that. Carrying them as fields moves the obligation to the ONE place
that can honestly meet it, the construction
`exists_threeadicRealization_of_witness`, where `τ` is the actual
Brauer-descended member; the two former leaves are now short PROVEN
projections of these fields, so every downstream consumer is
unchanged.

ABSORPTION (2026-07-26 — the repair completed). The two fields were
briefly supplied by a pair of dedicated citation leaves
(`blggt_threeadicMember_flatAtThreePow`,
`blggt_threeadicMember_stableLineAtTwo`), each quantified over a package
satisfying only the Frobenius match — so, as their own HONESTY AUDIT
said, the counterexample above applied to them verbatim and they were no
more derivable than the leaves they replaced. Both are now DELETED: their
conclusions are clauses (2) and (3) of the existential of
`blggt_threeadicBrauerSum_of_witness`, which is the one declaration in
the tree that CHOOSES `τ` and can therefore honestly assert its local
shape. That is deduplication rather than a larger citation — BLGGT's
compatible systems already assert crystallinity at the places over the
residue characteristic, so the construction leaf had been UNDER-asserting
relative to its own source. Read that docstring for the mathematics of
both local shapes.

CIRCULARITY GUARD (inherited from pillar β, load-bearing): this
interface may only be inhabited by the independent Brauer-descent
construction — never through `Family.lean`, `Lift.lean`, or
`Modularity/Interface.lean`. -/
structure ThreeadicRealization (ℓ : ℕ) [Fact ℓ.Prime]
    (O : Type u) [CommRing O] [TopologicalSpace O] [IsTopologicalRing O]
    (ρ : GaloisRep ℚ O (Fin 2 → O))
    (Wit : PotentialModularityWitness ℓ O ρ) : Type (u + 1) where
  /-- The finite exceptional set of the descent (the primes ramified
  in `F` and those below the bad places of the newform). -/
  S₁ : Finset (HeightOneSpectrum (NumberField.RingOfIntegers ℚ))
  /-- The `3`-adic coefficient ring: classically the integers of
  `E_λ`, `λ | 3`. -/
  A : Type u
  [commRingA : CommRing A]
  [topologicalSpaceA : TopologicalSpace A]
  [isTopologicalRingA : IsTopologicalRing A]
  [algebraA : Algebra ℤ_[3] A]
  [isLocalRingA : IsLocalRing A]
  [moduleFiniteA : Module.Finite ℤ_[3] A]
  [moduleFreeA : Module.Free ℤ_[3] A]
  [isModuleTopologyA : IsModuleTopology ℤ_[3] A]
  /-- The Brauer-descended `3`-adic representation of `G_ℚ`, on a
  stable lattice. -/
  τ : GaloisRep ℚ A (Fin 2 → A)
  /-- The coefficient embedding of the `3`-adic member into `ℚ̄_3`. -/
  ιA : A →+* AlgebraicClosure ℚ_[3]
  ιA_injective : Function.Injective ιA
  /-- Frobenius compatibility with `ρ` through the Hecke field:
  `ℓ`-adic interpolants are `3`-adic interpolants (Carayol
  local-global compatibility at unramified places, on both sides of
  the descent). -/
  compat : ∀ (q : ℕ) (hq : q.Prime),
    hq.toHeightOneSpectrumRingOfIntegersRat ∉ S₁ →
    q ≠ 2 → q ≠ 3 → q ≠ ℓ →
    ∀ P : Polynomial Wit.E,
      (ρ.charFrob hq.toHeightOneSpectrumRingOfIntegersRat).map Wit.ιO =
        P.map Wit.ψℓ →
      (τ.charFrob hq.toHeightOneSpectrumRingOfIntegersRat).map ιA =
        P.map Wit.ψ₃
  /-- **The local shape at `3` — Fontaine–Laffaille, on the `3`-power
  levels of the stable lattice.** For every `m ≥ 1` the level
  `(A ⧸ 3^m) ⊗_A (Fin 2 → A)` — i.e. `T/3^m T` for `T = Fin 2 → A` —
  is the group of `ℚ̄_3`-points of the generic fibre of a finite flat
  group scheme over `ℤ_3`.

  LEVEL AUDIT (2026-07-25): asserted on the `3`-POWER levels only,
  which are the levels of the `3`-divisible group. The
  arbitrary-finite-quotient form is PROVEN glue over this cofinal
  subtower (`threeadicRealization_hasFlatProlongationAt_of_finite_quotient`,
  through Raynaud's closure of finite flat group schemes under
  quotients, `hasFlatProlongationAt_of_surjective`), so demanding it
  here would re-obligate something the tree already has. Only positive
  levels are asserted: at `m = 0` the level is a single point and the
  transport discharges it outright.

  WHY A FIELD: see the CUT-LEVEL REPAIR paragraph of this structure's
  docstring — flatness at `3` is an extension-class property, hence not
  implied by `compat`. -/
  flatAtThreePow : ∀ m : ℕ, 1 ≤ m →
    (τ.baseChange (A ⧸ Ideal.span {(3 : A) ^ m})).HasFlatProlongationAt
      (Nat.Prime.toHeightOneSpectrumRingOfIntegersRat
        (Fact.out : Nat.Prime 3))
  /-- **The local shape at `2` — the Weil–Deligne type across the
  system, as a stable line with unramified quadratic quotient.** There
  are an `A`-basis `b` of the stable lattice `Fin 2 → A` and an
  unramified square-trivial character `δ` of `G_{ℚ_2}` with

    `τ g v ≡ δ g 1 • v  (mod A · b 0)`  for all `g` and all `v`.

  Taking `v = b 0` shows the line `A · b 0` is `G_{ℚ_2}`-stable, so the
  shape "extension of the unramified quadratic `δ` by something, in a
  basis adapted to the lattice" is stated with no matrix in it; the
  matrix reading is PROVEN from this clause in
  `threeadicRealization_weilDeligneType_two_of_witness`.

  WHY A FIELD: same reason as `flatAtThreePow` — this is inertia data
  at `2`, and `compat` carries no information at `2` whatsoever. -/
  stableLineAtTwo :
    ∃ (b : Module.Basis (Fin 2) A (Fin 2 → A))
      (δ : GaloisRep ℚ_[2] A A),
      (AddSubgroup.inertia
          ((IsLocalRing.maximalIdeal Z2bar).toAddSubgroup :
            AddSubgroup Z2bar)
          (Field.absoluteGaloisGroup ℚ_[2]) ≤ δ.ker) ∧
      (∀ g : Field.absoluteGaloisGroup ℚ_[2], δ g * δ g = 1) ∧
      ∀ (g : Field.absoluteGaloisGroup ℚ_[2]) (v : Fin 2 → A),
        τ.map (algebraMap ℚ ℚ_[2]) g v - δ g 1 • v ∈
          Submodule.span A {b 0}
  /-- **Unramifiedness at `ℓ` — the level of the eigensystem is prime to
  `ℓ`** (Fontaine–Laffaille on the `ℓ`-adic member, carried across the
  compatible system): the Brauer-descended `3`-adic member `τ` is
  unramified at `ℓ`.

  WHY A FIELD (2026-07-26 seam change, third of its kind in this
  structure): this is inertia data at `ℓ`, and none of the three clauses
  above touches it — `compat` equates Frobenius characteristic
  polynomials at unramified places away from `S₁` and therefore carries
  no inertia information at all, while `flatAtThreePow` and
  `stableLineAtTwo` are local data at `3` and at `2` respectively. The
  sharper reason it cannot be a derived lemma is recorded in the ROUTE
  AUDIT of `threeadicRealization_isUnramifiedAtEll_of_witness` below:
  Frobenius data pins at most the SEMISIMPLIFICATION of `τ`, and over
  `ℚ` the non-split extensions of `1` by the `3`-adic cyclotomic
  character given by Kummer classes of nonzero valuation are ramified
  while having, at every prime, the same Frobenius characteristic
  polynomials as the split extension. So the datum has to be chosen
  together with `τ`, i.e. by the construction citation.

  LITERATURE ATTRIBUTION, kept deliberately SEPARATE from the field
  below so that the 2026-07-25 split of the two inputs survives the seam
  change: this clause is the FONTAINE–LAFFAILLE input at the `ℓ`-adic
  member's own residue characteristic — `ρ` is flat at `ℓ` (`hρ.isFlat`
  at the construction site), hence the Hilbert newform's level is prime
  to `ℓ`, hence every member of the compatible system attached to it is
  unramified at `ℓ`. It is NOT a consequence of strict compatibility
  alone, which says nothing about the parameter at `ℓ` being
  unramified. -/
  unramifiedAtEll : τ.IsUnramifiedAt
    (Nat.Prime.toHeightOneSpectrumRingOfIntegersRat (Fact.out : ℓ.Prime))
  /-- **Member-independence of the ramification locus away from `3` and
  `ℓ`** (Carayol / BLGGT strict compatibility): at a prime `p ∉ {3, ℓ}`
  at which the `ℓ`-adic member `ρ` is unramified, the Brauer-descended
  `3`-adic member `τ` is unramified too.

  WHY A FIELD: same reason as `unramifiedAtEll` — inertia data at a
  prime `p ∉ {2, 3}`, invisible to all three of `compat`,
  `flatAtThreePow` and `stableLineAtTwo`, and destroyed by
  semisimplification. See the ROUTE AUDIT and the HYPOTHESIS
  LOAD-BEARING AUDIT of
  `threeadicRealization_unramifiedTransfer_of_witness` below, which also
  records why the PIECEWISE route (prove the transfer on the Brauer
  pieces and induce) is unsound: the ramification of the individual
  induced pieces cancels only in the virtual SUM.

  LITERATURE ATTRIBUTION: this clause is the CARAYOL member-independence
  input, and it is DEDUPLICATION rather than hiding — the construction
  citation `blggt_threeadicBrauerSum_of_witness` already cites BLGGT
  §5.3 / Theorem 5.5.1, and that theorem produces a member of a STRICTLY
  compatible system, i.e. it already asserts the local parameters at
  every `p ∤ 3`. Before this seam change the construction leaf
  UNDER-ASSERTED relative to its own source and the derived leaf paid
  for the difference by citing the same theorem a second time. -/
  unramifiedTransfer : ∀ p (hp : p.Prime), p ≠ 3 → p ≠ ℓ →
    ρ.IsUnramifiedAt hp.toHeightOneSpectrumRingOfIntegersRat →
    τ.IsUnramifiedAt hp.toHeightOneSpectrumRingOfIntegersRat

attribute [instance] ThreeadicRealization.commRingA
  ThreeadicRealization.topologicalSpaceA
  ThreeadicRealization.isTopologicalRingA
  ThreeadicRealization.algebraA
  ThreeadicRealization.isLocalRingA
  ThreeadicRealization.moduleFiniteA
  ThreeadicRealization.moduleFreeA
  ThreeadicRealization.isModuleTopologyA

/-- **Freeness normalization of a `3`-adic coefficient lattice**
(PROVEN 2026-07-24; pure commutative algebra — the formal half of the
classical "stable lattice" step): a coefficient ring `A` which is a
DOMAIN, module-finite over `ℤ_[p]` and receives `ℤ_[p]` injectively is
FREE as a `ℤ_[p]`-module. `ℤ_[p]` is a discrete valuation ring, hence a
principal ideal domain; injectivity of `ℤ_[p] → A` between domains makes
`A` torsion-free (`Module.isTorsionFree_iff_algebraMap_injective`), and a
module-finite torsion-free module over a PID is free
(`Module.free_of_finite_type_torsion_free'`).

PIN AUDIT (2026-07-24, hard search): mathlib has NO stable-lattice
material for continuous representations of compact groups (a search over
`Mathlib/` for stable/invariant lattices returns nothing, and there is no
`GL_n(K)`-conjugation/orbit-lattice development), so the EXISTENCE of the
Galois-stable lattice cannot be split off as an in-tree formal step: it
stays inside the citation leaf `blggt_threeadicBrauerSum_of_witness`
below (re-audited 2026-07-25, finding confirmed), which produces the
Brauer sum already in coefficient-ring (lattice) form — classically the
integers `O_{E_λ}` of the completion.
What IS formal, and is discharged here, is the freeness normalization
that the proven `3`-adic classification consumes downstream. -/
theorem module_free_padicInt_of_algebraMap_injective (p : ℕ)
    [Fact p.Prime] (A : Type*) [CommRing A] [IsDomain A] [Algebra ℤ_[p] A]
    [Module.Finite ℤ_[p] A]
    (hinj : Function.Injective (algebraMap ℤ_[p] A)) :
    Module.Free ℤ_[p] A :=
  haveI : Module.IsTorsionFree ℤ_[p] A :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr hinj
  Module.free_of_finite_type_torsion_free'

/-- **Locality from a henselian pair with artinian quotient, over a
domain** (PROVEN 2026-07-25; pure commutative algebra): if `A` is a
DOMAIN, henselian at an ideal `J` whose quotient `A ⧸ J` is artinian,
then `A` is a local ring.

The argument is the standard idempotent one, assembled from the bricks
of `Fermat.FLT.Mathlib.RingTheory.AdicCompletion.Finite`: `J` lies in
the Jacobson radical (`HenselianRing.jac`), so units lift along
`A → A ⧸ J` and `J` is proper; every idempotent of `A ⧸ J` lifts to an
idempotent of `A` (`HenselianRing.exists_isIdempotentElem_mk_eq`),
which in a DOMAIN is `0` or `1`; an artinian ring with only trivial
idempotents is local
(`IsLocalRing.of_isArtinianRing_isIdempotentElem`); and locality
transfers back through the quotient because units lift. -/
-- `_root_.` is LOAD-BEARING (2026-07-26): without it this declaration is
-- `GaloisRepresentation.Modularity.IsLocalRing.of_henselianRing_of_isDomain`,
-- which creates a namespace `GaloisRepresentation.Modularity.IsLocalRing`.
-- `Modularity/Patching.lean` lives in that same namespace and says
-- `open IsLocalRing` in four sections; those then resolve to the new,
-- nearly-empty namespace instead of mathlib's, and 95 references to
-- `maximalIdeal` and friends fail with `Unknown identifier`.  The lemma is
-- general commutative algebra about `IsLocalRing`, so the root namespace is
-- also its correct home.
theorem _root_.IsLocalRing.of_henselianRing_of_isDomain {A : Type*} [CommRing A]
    [IsDomain A] (J : Ideal A) [hHen : HenselianRing A J]
    [IsArtinianRing (A ⧸ J)] :
    IsLocalRing A := by
  classical
  have hjac : J ≤ Ideal.jacobson (⊥ : Ideal A) := hHen.jac
  -- units lift along `A → A ⧸ J`, because `J` is inside the Jacobson radical
  have hlift : ∀ a : A, IsUnit (Ideal.Quotient.mk J a) → IsUnit a := by
    intro a ha
    obtain ⟨u, hu⟩ := ha
    obtain ⟨b, hb⟩ := Ideal.Quotient.mk_surjective (↑u⁻¹ : A ⧸ J)
    have hab : Ideal.Quotient.mk J (a * b) = 1 := by
      rw [map_mul, ← hu, hb, Units.mul_inv]
    have hmem : a * b - 1 ∈ J := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, hab, map_one, sub_self]
    have hunit : IsUnit (a * b) := by
      simpa using Ideal.mem_jacobson_bot.mp (hjac hmem) 1
    exact isUnit_of_mul_isUnit_left hunit
  -- `J` is proper
  have hJne : J ≠ ⊤ := by
    intro htop
    have h1 : (1 : A) ∈ J := htop ▸ Submodule.mem_top
    simpa using Ideal.mem_jacobson_bot.mp (hjac h1) (-1)
  haveI : Nontrivial (A ⧸ J) := Ideal.Quotient.nontrivial_iff.mpr hJne
  -- idempotents of the quotient lift to idempotents of the domain `A`
  have hidem : ∀ x : A ⧸ J, IsIdempotentElem x → x = 0 ∨ x = 1 := by
    intro x hx
    obtain ⟨y, hy, hymk⟩ := HenselianRing.exists_isIdempotentElem_mk_eq hx
    rcases hy.eq_zero_or_eq_one_of_isDomain with h | h
    · exact Or.inl (by rw [← hymk, h, map_zero])
    · exact Or.inr (by rw [← hymk, h, map_one])
  haveI : IsLocalRing (A ⧸ J) :=
    IsLocalRing.of_isArtinianRing_isIdempotentElem hidem
  refine IsLocalRing.of_isUnit_or_isUnit_one_sub_self ?_
  intro a
  rcases IsLocalRing.isUnit_or_isUnit_one_sub_self (Ideal.Quotient.mk J a) with h | h
  · exact Or.inl (hlift a h)
  · refine Or.inr (hlift (1 - a) ?_)
    simpa using h

/-- **A domain module-finite over `ℤ_[p]` is a local ring** (PROVEN
2026-07-25; pure commutative algebra — the coefficient-ring brick that
removes `IsLocalRing` from the `3`-adic citations).

This is the step the twin Carayol node's docstring recorded as
"RESIDUAL BOOKKEEPING NOT YET PULLED OUT … a self-contained
commutative-algebra project": the maximal ideals of such a ring all lie
over `(p)` (formal), but their UNIQUENESS needs a Henselian input. That
input now exists in-tree — `HenselianRing.of_finite_algebra` makes
`(A, 𝔪_{ℤ_p}·A)` a henselian pair by adic completeness of the finite
module `A` over the complete local `ℤ_[p]` — so the bridge is built:
`A ⧸ 𝔪_{ℤ_p}·A` is a finite algebra over the residue FIELD of `ℤ_[p]`
(`Ideal.Quotient.algebraQuotientMapQuotient` plus
`module_finite_of_liesOver`), hence artinian, and
`IsLocalRing.of_henselianRing_of_isDomain` applies.

Note no injectivity of `algebraMap ℤ_[p] A` is needed: if `p` dies in
`A` then `A` is a finite domain, i.e. a finite field, which is local
too, and the proof is uniform in both cases.

REDUNDANCY NOTE (2026-07-26): this SUBSUMES
`isLocalRing_of_finite_padicInt_domain` about four thousand lines
above, which carries an extra `hinj` hypothesis and is used there only
because declaration order puts this lemma out of its reach. See that
lemma's docstring; the intended eventual fix is to hoist this one and
`IsLocalRing.of_henselianRing_of_isDomain` above it and delete the
weaker version. -/
theorem isLocalRing_of_finite_padicInt (p : ℕ) [Fact p.Prime] (A : Type*)
    [CommRing A] [IsDomain A] [Algebra ℤ_[p] A] [Module.Finite ℤ_[p] A] :
    IsLocalRing A := by
  classical
  haveI hHen : HenselianRing A
      ((IsLocalRing.maximalIdeal ℤ_[p]).map (algebraMap ℤ_[p] A)) :=
    HenselianRing.of_finite_algebra ℤ_[p] A
  haveI hlies : ((IsLocalRing.maximalIdeal ℤ_[p]).map
      (algebraMap ℤ_[p] A)).LiesOver (IsLocalRing.maximalIdeal ℤ_[p]) := by
    constructor
    refine le_antisymm Ideal.le_comap_map (IsLocalRing.le_maximalIdeal ?_)
    intro htop
    have h1 : (1 : ℤ_[p]) ∈ Ideal.under ℤ_[p]
        ((IsLocalRing.maximalIdeal ℤ_[p]).map (algebraMap ℤ_[p] A)) := by
      rw [htop]; trivial
    have h2 : (1 : A) ∈ (IsLocalRing.maximalIdeal ℤ_[p]).map
        (algebraMap ℤ_[p] A) := by
      simpa using h1
    simpa using Ideal.mem_jacobson_bot.mp (hHen.jac h2) (-1)
  letI : Field (ℤ_[p] ⧸ IsLocalRing.maximalIdeal ℤ_[p]) :=
    Ideal.Quotient.field _
  haveI : IsArtinianRing
      (A ⧸ (IsLocalRing.maximalIdeal ℤ_[p]).map (algebraMap ℤ_[p] A)) :=
    IsArtinianRing.of_finite (ℤ_[p] ⧸ IsLocalRing.maximalIdeal ℤ_[p])
      (A ⧸ (IsLocalRing.maximalIdeal ℤ_[p]).map (algebraMap ℤ_[p] A))
  exact IsLocalRing.of_henselianRing_of_isDomain
    ((IsLocalRing.maximalIdeal ℤ_[p]).map (algebraMap ℤ_[p] A))

/-- **Hecke-field interpolant transport** (PROVEN 2026-07-24; formal —
the uniqueness half of the compatibility clause): a `3`-adic
characteristic polynomial which is the `ψ₃`-image of ONE interpolant
`Pv ∈ E[X]` of the `ℓ`-adic characteristic polynomial is the `ψ₃`-image
of EVERY `E`-polynomial `P` interpolating that same `ℓ`-adic polynomial
through `ψℓ`: `ψℓ` is a ring homomorphism out of a FIELD, hence
injective, so `P.map ψℓ = Pv.map ψℓ` forces `P = Pv`
(`Polynomial.map_injective`). This is exactly what turns the citation
leaf's match against the single descended family `Pv` into the
universally quantified `compat` field of `ThreeadicRealization`. -/
theorem heckePoly_transport {E : Type*} [Field E] {Lℓ : Type*}
    [Semiring Lℓ] [Nontrivial Lℓ] {L₃ : Type*} [Semiring L₃]
    (ψℓ : E →+* Lℓ) (ψ₃ : E →+* L₃) {cρ : Polynomial Lℓ}
    {cτ : Polynomial L₃} {Pv P : Polynomial E}
    (hPv : cρ = Pv.map ψℓ) (hτ : cτ = Pv.map ψ₃) (hP : cρ = P.map ψℓ) :
    cτ = P.map ψ₃ := by
  have hEq : Pv = P :=
    Polynomial.map_injective ψℓ ψℓ.injective (hPv.symm.trans hP)
  rw [hτ, hEq]

/-- **Splitting a surjection `A² ↠ A` over a local ring** (PROVEN
2026-07-27; pure commutative algebra): if `πq : A² →ₗ[A] A` is
surjective and `A` is local, there is an `A`-basis `b` of `A²` whose
FIRST vector spans `ker πq`.

Concretely: writing `πq v = v 0 * a + v 1 * c` with `a = πq (1,0)` and
`c = πq (0,1)`, surjectivity forces the ideal `(a, c)` to be everything,
so — `A` being local — one of `a`, `c` is a unit. In either case an
explicit `2 × 2` matrix of determinant `1` has first column in the
kernel and second column mapping to `1`; its columns are the basis, and
membership of the kernel is read off from the second coordinate.

This is the formal half of the "stable line" reading of the local shape
at `2`: it converts the FUNCTIONAL form of tameness at `2` — a
surjective `Γ_{ℚ_2}`-equivariant quotient functional, which is the form
`IsHardlyRamified.isTameAtTwo` uses and the form the literature
produces — into the BASIS form that
`blggt_threeadicBrauerSum_of_witness`'s clause (3) asks for. The
converse direction (basis form ⟹ functional form) is
`threeadicRealization_isTameAtTwo_of_witness` below, so after this lemma
the two forms are interderivable and the citation is free to state
whichever is closer to its source. -/
theorem exists_basis_finTwo_span_eq_ker
    {A : Type*} [CommRing A] [IsLocalRing A]
    (πq : (Fin 2 → A) →ₗ[A] A) (hsurj : Function.Surjective πq) :
    ∃ b : Module.Basis (Fin 2) A (Fin 2 → A),
      Submodule.span A {b 0} = LinearMap.ker πq := by
  classical
  set a : A := πq ![1, 0] with ha
  set c : A := πq ![0, 1] with hc
  have hexp : ∀ v : Fin 2 → A, πq v = v 0 * a + v 1 * c := by
    intro v
    have hv : v = v 0 • ![(1 : A), 0] + v 1 • ![(0 : A), 1] := by
      ext i; fin_cases i <;> simp
    conv_lhs => rw [hv]
    rw [map_add, map_smul, map_smul, ← ha, ← hc, smul_eq_mul, smul_eq_mul]
  -- one of the two coordinates of `πq` is a unit
  have hunit : IsUnit a ∨ IsUnit c := by
    by_contra hcon
    push Not at hcon
    obtain ⟨w, hw⟩ := hsurj 1
    have h1 : (1 : A) ∈ IsLocalRing.maximalIdeal A := by
      rw [← hw, hexp]
      exact Ideal.add_mem _
        (Ideal.mul_mem_left _ _
          ((IsLocalRing.mem_maximalIdeal _).mpr (mem_nonunits_iff.mpr hcon.1)))
        (Ideal.mul_mem_left _ _
          ((IsLocalRing.mem_maximalIdeal _).mpr (mem_nonunits_iff.mpr hcon.2)))
    exact (IsLocalRing.maximalIdeal.isMaximal A).ne_top
      ((Ideal.eq_top_iff_one _).mpr h1)
  -- the transition matrix: unit determinant, first column spanning the kernel
  obtain ⟨M, hdet, hM0, hM1⟩ :
      ∃ M : Matrix (Fin 2) (Fin 2) A, M.det = 1 ∧
        πq (fun j => M j 0) = 0 ∧ πq (fun j => M j 1) = 1 := by
    rcases hunit with h | h
    · obtain ⟨u, hu⟩ := h
      refine ⟨!![c, ↑u⁻¹; -a, 0], ?_, ?_, ?_⟩
      · rw [Matrix.det_fin_two_of, ← hu]; simp
      · rw [hexp]; simp; ring
      · rw [hexp]; simp; exact hu
    · obtain ⟨u, hu⟩ := h
      refine ⟨!![c, 0; -a, ↑u⁻¹], ?_, ?_, ?_⟩
      · rw [Matrix.det_fin_two_of, ← hu]; simp
      · rw [hexp]; simp; ring
      · rw [hexp]; simp; exact hu
  haveI : Invertible M.det := hdet ▸ invertibleOne
  haveI : Invertible M := Matrix.invertibleOfDetInvertible M
  set b : Module.Basis (Fin 2) A (Fin 2 → A) :=
    (Pi.basisFun A (Fin 2)).map (M.toLinearEquiv' inferInstance) with hbdef
  have hb : ∀ i : Fin 2, b i = fun j => M j i := by
    intro i
    ext j
    fin_cases i <;>
      simp [hbdef, Module.Basis.map_apply, Matrix.toLinearEquiv', Matrix.mulVec,
        dotProduct, Pi.basisFun_apply, Pi.single_apply]
  refine ⟨b, le_antisymm ?_ ?_⟩
  · rw [Submodule.span_le, Set.singleton_subset_iff]
    simp only [SetLike.mem_coe, LinearMap.mem_ker, hb 0]
    exact hM0
  · intro v hv
    have hrepr : v = b.repr v 0 • b 0 + b.repr v 1 • b 1 := by
      have h := b.sum_repr v
      rw [Fin.sum_univ_two] at h
      exact h.symm
    have h1 : b.repr v 1 = 0 := by
      have hker := LinearMap.mem_ker.mp hv
      conv_lhs at hker => rw [hrepr]
      rw [map_add, map_smul, map_smul, hb 0, hb 1, hM0, hM1, smul_zero,
        zero_add, smul_eq_mul, mul_one] at hker
      exact hker
    rw [hrepr, h1, zero_smul, add_zero]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)

/-- **Brauer descent, `3`-adic side — the geometric core of the Brauer
sum, in the tree's CANONICAL local vocabulary** (sorry node — BLGGT
§5.3; DECOMPOSITION 2026-07-27 of
`blggt_threeadicBrauerSum_of_witness` below, which is now a PROVEN
assembly over this node).

Same hypotheses, same package `(S₁, A, τ, ιA)`, same clauses (1) and
(2). What changes is the *shape* in which the local data at `2` and the
ramification locus are asserted, and the change is in the direction of
what the SOURCE actually produces:

* clause (3') — tameness at `2` is asserted in the FUNCTIONAL form
  (a surjective `Γ_{ℚ_2}`-equivariant quotient functional `πq` onto `A`
  with unramified square-trivial character `δ`) rather than in the
  basis/stable-line form. This is verbatim the shape of
  `IsHardlyRamified.isTameAtTwo` (`HardlyRamified/Defs.lean`), i.e. the
  shape the whole rest of this development speaks, and it is the shape
  the literature states ("a one-dimensional unramified quotient of
  order dividing 2"). The basis form is recovered by the PROVEN
  local-ring splitting `exists_basis_finTwo_span_eq_ker` above;
* clauses (4) and (5) are replaced by (4') `τ` is unramified OUTSIDE
  `{2, 3}` — the canonical conductor statement, again verbatim
  `IsHardlyRamified.isUnramified` at `3` — together with (5') the
  single residual strict-compatibility transfer AT `2`.

**Equivalence audit (2026-07-27, both directions, so this is a
faithful cut and not a weakening).** Write (4), (5) for the old clauses
and (4'), (5') for the new ones, under the standing hypothesis `hρ`.

* (4') ⟹ (4): `ℓ ≠ 2` (from `hℓodd`) and `ℓ ≠ 3` (from `hℓ5`), so
  (4') applies at `ℓ` directly.
* (4') ∧ (5') ⟹ (5): given `p ≠ 3`, `p ≠ ℓ` with `ρ` unramified at
  `p`, either `p = 2` — and then (5') is exactly the conclusion — or
  `p ∉ {2, 3}` and (4') gives it outright, with the hypothesis on `ρ`
  unused. This is the assembly proven below.
* (4) ∧ (5) ⟹ (4'): at `p ∉ {2, 3}`, either `p = ℓ` and (4) applies,
  or `p ∉ {2, 3, ℓ}`, in which case `hρ.isUnramified p` supplies the
  hypothesis of (5) — a hardly ramified `ρ` is unramified away from
  `{2, ℓ}` — and (5) concludes.
* (5) ⟹ (5') trivially (`2 ≠ 3` and `2 ≠ ℓ`, the latter from
  `hℓodd`).

So the two statements carry exactly the same information, and nothing
here is proven that was previously assumed: what the cut buys is that
the citation now asserts its clauses in the same vocabulary as
`IsHardlyRamified`, which is what the assemblies downstream
(`exists_threeadic_member_of_witness`) ultimately rebuild — the four
`threeadicRealization_*` condition transfers are re-deriving, from the
old shapes, exactly what the source hands over in the new ones.

**What this does NOT buy** (so nobody re-scopes it as cheap): this is
still ONE citation of BLGGT §5.3 / Theorem 5.5.1, and the four theories
audited absent at the parent node — Weil–Deligne representations, the
higher-ramification filtration, `B_cris`/Fontaine–Laffaille, and
smooth/admissible `GL₂` — are still absent from `Mathlib/`, from
`~/cs/FLT/FLT` and from `Fermat/`. Clauses (1) and (2) are untouched.
The decomposition moves the basis-construction and the
ramification-locus bookkeeping out of the citation and into proven
Lean; it does not shorten the literature input.

Literature: Barnet-Lamb–Gee–Geraghty–Taylor, *Potential automorphy and
change of weight*, Ann. of Math. 179 (2014), §5.3 and Theorem 5.5.1;
Khare–Wintenberger, *Serre's modularity conjecture (I)*, Invent. Math.
178 (2009), §5; Carayol, Ann. Sci. ÉNS 19 (1986); Fontaine–Laffaille,
Ann. Sci. ÉNS 15 (1982); Serre, *Abelian ℓ-adic Representations*, I.1
(stable lattices for continuous representations of compact groups).

ATOMICITY AUDIT (2026-07-27, run by a successor dispatched specifically
to cut this node further. **No further cut exists at this pin**; the
axes searched are named below, each with the check that would refute
the verdict, so the next owner starts somewhere new rather than
re-running this survey.)

THE GENERAL OBSTRUCTION, which closes the whole cut space at once:
every clause of the conclusion is a property of the EXISTENTIALLY BOUND
`τ`, and no in-tree predicate pins `τ` to its automorphic source. A
split therefore has to do one of exactly two things, and both are shut:

* (a) *re-quantify a clause over an abstract package* constrained only
  by the clauses before it. Refuted, and already REVERTED once in this
  file: `blggt_threeadicMember_flatAtThreePow` and
  `blggt_threeadicMember_stableLineAtTwo` had precisely that shape
  between 2026-07-25 and 2026-07-26 and were deleted INTO the citation,
  because `compat` pins `τ` only up to semisimplification while every
  local shape is invisible to semisimplification. Refuting check: read
  the ABSORPTION note and its two Kummer-class counterexamples in
  `blggt_threeadicBrauerSum_of_witness` below;
* (b) *introduce a predicate that DOES pin `τ`* — "crystalline at `3`
  with Hodge–Tate weights `{0,1}`", "`WD_2(τ) ≅ WD_2(ρ)`", "automorphic
  of level `N`". Each needs a theory re-verified absent on 2026-07-27
  from `Mathlib/`, from `~/cs/FLT/FLT` AND from `Fermat/`
  (`B_cris`/Fontaine–Laffaille, the Weil group, the automorphy
  predicate over a quaternionic Hecke algebra). Writing any of them as
  an `opaque` placeholder would manufacture a leaf INDEPENDENT of the
  theory — neither provable nor refutable — which is strictly worse
  than the present honest citation.

AXES SEARCHED, and why each is closed:

1. *Clause axis* — exhausted by the 2026-07-27 cut that produced this
   node; no bookkeeping-shaped clause is left. In particular the
   ramification locus must **NOT** be un-fused: replacing (4') ∧ (5')
   by "`τ` unramified at `ℓ`" ∧ "the transfer at every `p ∉ {3, ℓ}`" is
   literally the pair (4), (5) that this node was cut to remove, and
   the four-way equivalence audit above shows the two shapes carry the
   same information. Refuting check: compare with the `unramifiedAtEll`
   and `unramifiedTransfer` fields of `ThreeadicRealization`.
2. *Coefficient-ring axis* — nothing is left to strip. The citation
   asserts NEITHER `Module.Free ℤ_[3] A`, NOR `IsLocalRing A`, NOR
   injectivity of `algebraMap ℤ_[3] A`, NOR injectivity of `ιA`; all
   four are proven outside it (`module_free_padicInt_of_algebraMap_
   injective`, `isLocalRing_of_finite_padicInt`,
   `injective_algebraMap_of_ringHom_charZero`,
   `injective_of_finite_padicInt_charZero`). Refuting check: read the
   `obtain` pattern of `exists_threeadicBrauerSum_of_witness`.
3. *`τF`-descent axis* (NOT previously recorded anywhere in this file).
   One could ask the citation to carry `τ|_{G_F} ≅ Wit.τF` — which IS
   statable in-tree, `GaloisRep.map` restricting `ℚ`-reps to `F` — and
   then derive `τ`'s local shapes from `τF`'s, using that inertia at a
   prime unramified in `F` already lies in `G_F`. Closed because
   `PotentialModularityWitness` asserts NOTHING local about `τF`: its
   only `3`-adic clause is `matchF₃`, a Frobenius match outside `badF`.
   The route needs new local fields on ANOTHER owner's structure in
   `MoretBailly.lean`, i.e. it RELOCATES the citation instead of
   reducing it. Refuting check: read the field list of
   `PotentialModularityWitness` (`MoretBailly.lean`).
4. *Ingredient axis* — the classical ingredients of the Brauer trick.
   **CORRECTED AGAIN 2026-07-27 (second pass): the ingredient axis is
   EMPTY. It is ZERO missing ingredients, not three and not four, and
   the verdict must therefore rest on obstruction (a), never on
   ingredient absence.** The inherited PIN AUDIT listed four; the
   previous pass corrected it to three; every one of the three is in
   fact present in THIS FILE, and two of them are PROVEN and already
   consumed:

   * *Brauer induction* — `brauer_induction_trivial_character`
     (PROVEN, this module; Artin induction with `ℚ` coefficients over
     `cyclicIndicator` / `indTrivCyclic` / `sum_indTrivCyclic_mul` /
     `sum_eq_zero_of_cyclic_sums`), and it is already applied to
     `Gal(F/ℚ)` inside `exists_heckeField_system_of_witness`;
   * *induced-character traces* — `exists_inducedTrace_expansion_of_
     brauer` (PROVEN, this module), which IS the Mackey/Frobenius
     expansion of the trace coefficient over degree-one places, over
     `exists_degreeOnePlace_of_brauer` (PROVEN);
   * *the stable lattice* (Serre I §1) — `exists_stableLattice_galois
     Rep_of_finiteDimensional_padic`, STATED in this module with a
     six-step in-tree work plan and ALREADY CONSUMED by
     `carayol_threeadic_of_totallyDefinite_heckeCharacter`. It is an
     open leaf with its own owner, not an absent theory, and per the
     standing rule that *stating* a theory is what a cut needs, its
     openness cannot support an atomicity verdict.

   Refuting checks: `grep -n "theorem brauer_induction_trivial_
   character\|theorem exists_inducedTrace_expansion_of_brauer\|theorem
   exists_stableLattice_galoisRep_of_finiteDimensional_padic"` on this
   file; and `grep -n exists_conj_of_charFrob_eq_away_of_charZero
   Fermat/FLT/GaloisRepresentation/BrauerNesbittConjugacy.lean` for the
   Brauer–Nesbitt half of the earlier correction.

   **Why the verdict nevertheless survives, stated so that it is
   checkable rather than inherited.** The whole Brauer apparatus above
   is already run, in-tree and to completion, on the `ℓ`-adic side: it
   is exactly what `exists_heckeField_system_of_witness` does, and its
   output `(S₀, Pv)` is a HYPOTHESIS of this node. What the apparatus
   transports is TRACE data — `coeff 1` of a Frobenius characteristic
   polynomial at good places — so re-running it `3`-adically could at
   best produce clause (1), and clause (1) is precisely what
   obstruction (a) shows to be blind to clauses (2), (3'), (4') and
   (5'). So the ingredient axis does not merely fail to shorten the
   citation; it cannot touch the four clauses that make it one.
5. *Integrality / field-level-split axis* (NEW 2026-07-27; this is the
   cut that WAS taken one level up in this very file, so it is the
   first thing a reader should expect to work here). One level up,
   `carayol_threeadic_of_totallyDefinite_heckeCharacter` was split into
   a FIELD-level citation
   (`exists_threeadicField_realization_of_totallyDefinite_heckeCharacter`,
   over a finite extension `L/ℚ_3`, which is what Carayol's Théorème
   (A) literally produces) plus the elementary integral descent
   (`exists_stableLattice_galoisRep_of_finiteDimensional_padic`). The
   same split does NOT transfer to this node, and the obstruction is
   clause (2) alone: `GaloisRep.HasFlatProlongationAt`
   (`Deformations/RepresentationTheory/GaloisRep.lean`) quantifies over
   finite flat Hopf algebras over `𝒪ᵥ` matching the geometric points of
   the LOCAL module, and so is only meaningful for a coefficient ring
   with finite quotients — it has no field-level shadow whatsoever.
   Clauses (1), (3'), (4') and (5') would all descend along a lattice
   (`charFrob` is conjugation-invariant; a stable line intersects a
   lattice in a saturated stable line), but (2) has to be asserted
   integrally, so the citation must still produce `A` and the split
   buys nothing. Refuting check: try to STATE clause (2) for a
   `ℚ_[3]`-algebra coefficient ring — read the definition of
   `GaloisRep.HasFlatProlongationAt` and note that it is applied to
   `τ.baseChange (A ⧸ Ideal.span {(3 : A) ^ m})`, a finite quotient
   that does not exist on the field side.
6. *Collapse-discharge axis* (NEW 2026-07-27). The hypothesis set of
   this node is classically UNSATISFIABLE — an irreducible hardly
   ramified `ρbar` with `ℓ ≥ 5` does not exist, which is the headline
   `not_isIrreducible_of_isHardlyRamified_of_five_le` at the end of
   this module — so one might hope to discharge the node, or at least
   clause (5'), from `False`. CLOSED BY CIRCULARITY, twice over: the
   headline is DOWNSTREAM of this leaf (its proof runs through
   `exists_threeadic_member_of_witness`, which is an assembly over
   `exists_threeadicBrauerSum_of_witness`, which is an assembly over
   THIS node), so using it here would close a cycle; and the
   clause-(5')-only version — `ρ` hardly ramified, unramified at `2`,
   with `ρbar` irreducible, is empty by Fontaine/Abrashkin — is not
   available either, since Fontaine/Abrashkin appears nowhere in the
   tree as mathematics. Refuting checks: `grep -n
   not_isIrreducible_of_isHardlyRamified_of_five_le` on this file and
   confirm its line number EXCEEDS this one; and `grep -rn Abrashkin
   Fermat/ --include=*.lean`, which returns only two prose mentions,
   one of them this docstring's own.

FAITHFULNESS RE-CHECK (same pass, since a leaf that resists is a leaf
to suspect). The statement is TRUE as stated. The only clause worth
re-deriving is (4'): `ρ` is unramified outside `{2, ℓ}` (`hρ.isUnramified`)
and flat at `ℓ` (`hρ.isFlat`), so the eigensystem's conductor is
supported at `2` alone, and the `3`-adic member of the system is
unramified at every `p ∉ {2, 3}` — including at `p = ℓ`, which is
exactly the Fontaine–Laffaille-at-`ℓ` input kept separate from the
strict-compatibility input elsewhere in this cluster. Clause (5') is
NOT vacuous-by-construction: `ρ.IsUnramifiedAt 2` is consistent with
`IsHardlyRamified`, and its classical emptiness (Fontaine/Abrashkin —
no irreducible flat `ρbar` unramified outside `ℓ`) is exactly the
headline collapse argument of this module, not an in-tree proof.
Sharpened 2026-07-27: the module's headline
`not_isIrreducible_of_isHardlyRamified_of_five_le` IS in-tree and
proven, but it is downstream of this leaf, so it is unusable here —
see axis 6 of the ATOMICITY AUDIT above for the two-way check.

CIRCULARITY GUARD (inherited, load-bearing): no discharge through
`Family.lean`, `Lift.lean`, or `Modularity/Interface.lean`. Note in
particular that `Family.lean`'s `IsInHardlyRamifiedFamily` asserts, for
every odd prime and every coefficient embedding, a hardly ramified
member with exactly these local shapes — this node is deliberately its
`Family`-free twin, and `Family.lean` `public import`s
`Modularity/Interface.lean`, which imports THIS module, so the
duplication cannot be removed by importing it. -/
theorem blggt_threeadicHardlyRamifiedMember_of_witness
    {ℓ : ℕ} (hℓodd : Odd ℓ) [Fact ℓ.Prime] (hℓ5 : 5 ≤ ℓ)
    {O : Type u} [CommRing O] [IsDomain O] [TopologicalSpace O]
    [IsTopologicalRing O] [Algebra ℤ_[ℓ] O] [IsLocalRing O]
    [Module.Finite ℤ_[ℓ] O] [IsModuleTopology ℤ_[ℓ] O]
    (hZinj : Function.Injective (algebraMap ℤ_[ℓ] O))
    {ρ : GaloisRep ℚ O (Fin 2 → O)}
    (hrank : Module.rank O (Fin 2 → O) = 2)
    (hρ : IsHardlyRamified hℓodd hrank ρ)
    {k : Type u} [Field k] [Finite k] [Algebra ℤ_[ℓ] k]
    [TopologicalSpace k] [DiscreteTopology k]
    {W : Type v} [AddCommGroup W] [Module k W] [Module.Finite k W]
    [Module.Free k W]
    (hW : Module.rank k W = 2) {ρbar : GaloisRep ℚ k W}
    (hρbar : IsHardlyRamified hℓodd hW ρbar)
    (hirr : ρbar.IsIrreducible)
    (π : O →+* k) (hπsurj : Function.Surjective π)
    (hπ : ∀ (q : ℕ) (hq : q.Prime), q ≠ 2 → q ≠ ℓ →
      (ρ.charFrob hq.toHeightOneSpectrumRingOfIntegersRat).map π =
        ρbar.charFrob hq.toHeightOneSpectrumRingOfIntegersRat)
    (Wit : PotentialModularityWitness ℓ O ρ)
    (S₀ : Finset (HeightOneSpectrum (NumberField.RingOfIntegers ℚ)))
    (Pv : HeightOneSpectrum (NumberField.RingOfIntegers ℚ) →
      Polynomial Wit.E)
    (hPv : ∀ (q : ℕ) (hq : q.Prime),
      hq.toHeightOneSpectrumRingOfIntegersRat ∉ S₀ →
      q ≠ 2 → q ≠ 3 → q ≠ ℓ →
      (ρ.charFrob hq.toHeightOneSpectrumRingOfIntegersRat).map Wit.ιO =
        (Pv hq.toHeightOneSpectrumRingOfIntegersRat).map Wit.ψℓ) :
    ∃ (S₁ : Finset (HeightOneSpectrum (NumberField.RingOfIntegers ℚ)))
      (A : Type u) (_ : CommRing A) (_ : IsDomain A)
      (_ : Algebra ℤ_[3] A) (_ : Module.Finite ℤ_[3] A),
      letI : TopologicalSpace A := moduleTopology ℤ_[3] A
      letI : IsTopologicalRing A :=
        isTopologicalRing_moduleTopology_of_finite 3 A
      ∃ (τ : GaloisRep ℚ A (Fin 2 → A))
        (ιA : A →+* AlgebraicClosure ℚ_[3]),
        -- (1) Frobenius compatibility away from `S₁` (Carayol)
        (∀ (q : ℕ) (hq : q.Prime),
          hq.toHeightOneSpectrumRingOfIntegersRat ∉ S₁ →
          q ≠ 2 → q ≠ 3 → q ≠ ℓ →
          (τ.charFrob hq.toHeightOneSpectrumRingOfIntegersRat).map ιA =
            (Pv hq.toHeightOneSpectrumRingOfIntegersRat).map Wit.ψ₃) ∧
        -- (2) the local shape at `3`: Fontaine–Laffaille on the
        -- `3`-power levels of the stable lattice
        (∀ m : ℕ, 1 ≤ m →
          (τ.baseChange (A ⧸ Ideal.span {(3 : A) ^ m})).HasFlatProlongationAt
            (Nat.Prime.toHeightOneSpectrumRingOfIntegersRat
              (Fact.out : Nat.Prime 3))) ∧
        -- (3') the local shape at `2`, in the FUNCTIONAL form of
        -- `IsHardlyRamified.isTameAtTwo`
        (∃ (πq : (Fin 2 → A) →ₗ[A] A) (_ : Function.Surjective πq)
          (δ : GaloisRep ℚ_[2] A A),
          (AddSubgroup.inertia
              ((IsLocalRing.maximalIdeal Z2bar).toAddSubgroup :
                AddSubgroup Z2bar)
              (Field.absoluteGaloisGroup ℚ_[2]) ≤ δ.ker) ∧
          (∀ g : Field.absoluteGaloisGroup ℚ_[2], δ g * δ g = 1) ∧
          ∀ (g : Field.absoluteGaloisGroup ℚ_[2]) (v : Fin 2 → A),
            πq (τ.map (algebraMap ℚ ℚ_[2]) g v) = δ g (πq v)) ∧
        -- (4') the conductor statement: unramified outside `{2, 3}`
        (∀ p (hp : p.Prime), p ≠ 2 → p ≠ 3 →
          τ.IsUnramifiedAt hp.toHeightOneSpectrumRingOfIntegersRat) ∧
        -- (5') the residual strict-compatibility transfer, at `2` only
        (∀ hp2 : Nat.Prime 2,
          ρ.IsUnramifiedAt hp2.toHeightOneSpectrumRingOfIntegersRat →
          τ.IsUnramifiedAt hp2.toHeightOneSpectrumRingOfIntegersRat) :=
  sorry

/-- **Brauer descent, `3`-adic side — the geometric core of the Brauer
sum** (PROVEN assembly since 2026-07-27 over
`blggt_threeadicHardlyRamifiedMember_of_witness` immediately above,
which is now THE single citation sub-leaf of the `3`-adic realization;
see the DECOMPOSITION note at the very end of this docstring — the rest
of the docstring describes the mathematics of the citation and is
unchanged): given the descended
rational Hecke system `(S₀, Pv)` produced on the `ℓ`-adic side
(`exists_heckeField_system_of_witness`), the SAME system is realized
`3`-adically — there are a finite exceptional set `S₁`, a coefficient
ring `A` which is a local DOMAIN module-finite over `ℤ_3` (classically
the integers `O_{E_λ}` of the completion of the Hecke field at a place
`λ | 3`), a representation `τ` of `G_ℚ` on `Fin 2 → A`, and a
comparison embedding `ιA : A → ℚ̄_3`, such that

1. `τ`'s Frobenius characteristic polynomials away from `S₁` are the
   `ψ₃`-images of `Pv` (Carayol, at the unramified places);
2. `τ` has the Fontaine–Laffaille local shape at `3`: every `3`-power
   level of the stable lattice is finite flat over `ℤ_3`;
3. `τ` has the expected Weil–Deligne type at `2`: a stable line with
   unramified quadratic quotient.

Clauses (2) and (3) were ABSORBED here on 2026-07-26 from two separate
sorried leaves; see the ABSORPTION section at the end of this docstring
for why they belong to this citation and nowhere else, and for the full
mathematics of both local shapes. All three clauses are parts of one
BLGGT compatible system, so this is a single citation, not three.

CITATION-SHRINKING CUT (2026-07-25, extended the same day). This leaf
replaces the earlier `exists_threeadicBrauerSum_of_witness` citation,
which is now a PROVEN assembly over it. Six components of that
statement were pulled out of
the citation, using the coefficient-ring bricks proven above for the
twin Carayol node (`carayol_threeadic_realization_of_heckePackage`);
the citation now asserts strictly less:

* `TopologicalSpace A`, `IsTopologicalRing A`, `IsModuleTopology ℤ_3 A`
  — GONE. The coefficient ring's topology is not a choice: those three
  components together pin it to be the `ℤ_3`-module topology, so the
  statement below simply USES that topology and
  `isTopologicalRing_moduleTopology_of_finite` supplies the rest;
* `Function.Injective ιA` — GONE, by
  `injective_of_finite_padicInt_charZero`: a domain module-finite over
  `ℤ_3` admits no nonzero prime over `(0)`, so ANY ring map of it into
  the characteristic-zero field `ℚ̄_3` is injective;
* `Function.Injective (algebraMap ℤ_3 A)` — GONE, by
  `injective_algebraMap_of_ringHom_charZero`: the mere EXISTENCE of the
  comparison embedding forces it. This is what feeds the downstream
  free-lattice normalization
  (`module_free_padicInt_of_algebraMap_injective`), so `ℤ_3`-freeness
  of `A` is now two formal steps away from the citation rather than an
  assumption plus a step;
* `IsLocalRing A` — GONE (2026-07-25), by
  `isLocalRing_of_finite_padicInt`: a DOMAIN module-finite over `ℤ_3`
  is automatically local. The twin's docstring recorded this as
  "RESIDUAL BOOKKEEPING NOT YET PULLED OUT", needing a Henselian input
  that the pin did not supply. It does now, in-tree: the bricks of
  `Fermat.FLT.Mathlib.RingTheory.AdicCompletion.Finite` make
  `(A, 𝔪_{ℤ_3}·A)` a henselian pair, idempotents lift into the domain
  `A` where they are `0` or `1`, and an artinian ring with only trivial
  idempotents is local. **The twin node
  `carayol_threeadic_realization_of_heckePackage` can drop its own
  `IsLocalRing B` the same way — its audit is now stale — as can
  `ThreeadicRealization.isLocalRingA` and
  `PotentialModularityWitness.isLocalRingB`; those are other owners'
  declarations and are deliberately untouched here.**

What remains is the genuinely automorphic/geometric core. Classically
this is the Brauer trick at the place `λ | 3`: Brauer's induction
theorem on `Gal(F/ℚ)` (`Wit.galoisF`) writes
`1 = Σ cᵢ · Ind_{Hᵢ}^{Gal(F/ℚ)} χᵢ` with `Hᵢ` solvable and `χᵢ`
one-dimensional; solvable base change descends the Hilbert newform to
each `Fᵢ = F^{Hᵢ}`, and Carayol/Taylor attach to each descended form
its `3`-adic realization (the carrier's `τF` at the base level,
`Wit.matchF₃`). The virtual sum
`Σ cᵢ · Ind_{G_{Fᵢ}}^{G_ℚ} (τ_{fᵢ,λ} ⊗ χᵢ)` has, by construction, the
same trace function as the `ψ₃`-transport of the Hecke system, hence
Frobenius characteristic polynomials `Pv` through `ψ₃`; it is a TRUE
(not merely virtual) representation because at the place over `ℓ` the
corresponding sum is the character of `ρ` — a genuine `2`-dimensional
representation — and Brauer–Nesbitt pins the semisimple representation
at every place of `E`. Finally the resulting `2`-dimensional
`E_λ`-representation of the COMPACT group `G_ℚ` admits a stable lattice
(the `O_{E_λ}`-span of the orbit of any lattice under the compact image
is finitely generated and stable), which is the coefficient ring `A`
together with `τ` and the embedding `ιA : O_{E_λ} → ℚ̄_3`. The
exceptional set `S₁` collects `S₀`, the primes ramified in `F`, and the
primes below the bad places of the descended forms.

Literature: Barnet-Lamb–Gee–Geraghty–Taylor, *Potential automorphy and
change of weight*, Ann. of Math. 179 (2014), §5.3 (the Brauer trick:
the virtual sum is a true representation, and the constructed system is
weakly compatible) and Theorem 5.5.1; Khare–Wintenberger, *Serre's
modularity conjecture (I)*, Invent. Math. 178 (2009), §5; Taylor, *On
Galois representations associated to Hilbert modular forms*, Invent.
Math. 98 (1989) (the `3`-adic realizations of the descended Hilbert
forms); Taylor, *Remarks on a conjecture of Fontaine and Mazur*, J.
Inst. Math. Jussieu 1 (2002), §6; Carayol, Ann. Sci. ÉNS 19 (1986)
(local-global compatibility at unramified places, fixing the Frobenius
data); Serre, *Abelian ℓ-adic Representations*, I.1 (stable lattices
for continuous representations of compact groups), I.2 (induced traces
via degree-one places).

PIN AUDIT (2026-07-25, RE-AUDITED from scratch — the 2026-07-24 finding
is CONFIRMED). The stable-lattice step is still NOT separable into an
in-tree formal lemma at this pin:

* searching the pin for stable/invariant lattices of compact-group
  representations returns only `Module.End.span_orbit_mem_invtSubmodule`
  (`Mathlib/Algebra/Module/Submodule/Invariant.lean`) — the EASY half,
  invariance of the span of an orbit. The hard half, FINITE GENERATION
  of that span, needs "a compact subgroup of `GL₂(E_λ)` is bounded", and
  the pin has no boundedness theory of that shape (no `IsCompact →
  IsBounded` for matrix algebras over a valued field, no Bruhat–Tits or
  maximal-order material, no `GL_n(K)`-conjugation/orbit lattice
  development); `Mathlib/RepresentationTheory/Continuous/` carries the
  category `TopRep` of continuous representations but no
  integral-structure results at all;
* the reference project `~/cs/FLT` has NOTHING vendorable here: its
  Brauer-trick step exists only as blueprint prose
  (`blueprint/src/chapter/ch04overview.tex`, "the Brauer's theorem trick
  in [BLGGT]"), with no Lean development of stable lattices, of Brauer
  induction for Galois representations, or of Hilbert-modular `3`-adic
  realizations;
* WIDENED 2026-07-25 (the earlier audit searched only the lattice step;
  this one swept every ingredient of the classical argument). The pin
  ALSO has no Brauer induction and no Artin induction — the only
  `Brauer` in `Mathlib/` is the Brauer GROUP of central simple algebras
  — no `p`-elementary or hyperelementary subgroups, no representation
  ring or virtual characters, no character formula for induction (the
  algebraic `Representation.ind` and `Rep.indResAdjunction` exist, but
  no `χ_Ind` trace formula), no INDUCTION at all for continuous
  representations (`RepresentationTheory/Continuous/` has `coind` only),
  and no Brauer–Nesbitt (only the forward `char_iso`; the pin has no
  charpoly of a group element acting on a representation). So all four
  ingredients — Brauer induction, induced-character traces, stable
  lattices, Brauer–Nesbitt — are absent, and the leaf is irreducibly a
  citation at this pin rather than merely lacking one step.

So the leaf stays in lattice (coefficient-ring) form — the same
conclusion, for the same reason, that the twin node reached ("that cut
would trade one citation for two"). Also audited and deliberately NOT
done, for the reason recorded at the twin: restating the matching clause
as the trace/determinant pair. Both sides here are monic of degree `2`
(`hPv` forces `Pv v` to be, through the injective `Wit.ψℓ`), so that
form is EQUIVALENT, not weaker — it would relocate polynomial
bookkeeping into this file without removing anything from the citation.
(`IsLocalRing A` used to stay here for the Henselian-input reason
recorded at the twin; as of 2026-07-25 it is GONE — see the
citation-shrinking bullet above.)

VACUITY AUDIT (2026-07-25, done before any proof effort — this family
has a bad record, so the leaf was attacked as junk BEFORE being
attacked as a theorem). **Result: NOT vacuous.** The three routes that
killed sibling leaves all fail here, for reasons worth recording so
nobody re-runs them:

* *Satisfy it from the witness's own data.* `Wit` already carries a
  `3`-adic representation `τF` with the right Hecke polynomials — but
  over `G_F`, and the only transport available (`GaloisRep.map`) goes
  from `Γ K` to `Γ L` along `K →+* L`, i.e. RESTRICTS `ℚ`-reps to `F`.
  There is no formal operation carrying `τF` back to `G_ℚ`; that
  operation IS the Brauer trick. So the leaf is not satisfiable by its
  own inputs.
* *Kill the conclusion with the exceptional set.* `S₁` is chosen by
  the prover, but it is a `Finset`, and
  `toHeightOneSpectrumRingOfIntegersRat_injective` (PROVEN, in
  `Chebotarev.lean`) makes distinct primes distinct places, so the
  matching clause still binds at cofinitely many `q`. `S₁ ⊇ S₀` is
  allowed, which is exactly what keeps the statement WELL-POSED: `Pv`
  is unconstrained by `hPv` inside `S₀`, and the conclusion never
  reaches there.
* *Degenerate Frobenius, or the trivial representation.* `charFrob`
  evaluates `ρ` at `adicArithFrob v`, which is mathlib's honest
  `arithFrobAt'` (`IsArithFrobAt`, so it is `x ↦ x^q` on the residue
  field), not a junk choice; and the trivial `τ` is refuted
  numerically: `hPv` plus the PROVEN
  `charFrob_coeff_zero_eq_natCast_of_isHardlyRamified` forces
  `(Pv q).coeff 0 = (q : E)` through the injective `ψℓ`, whereas the
  trivial representation has `charFrob = (X − 1)²` with constant
  coefficient `1 ≠ q`.

SOUNDNESS AUDIT (both ways, 2026-07-25, inherited from the node this
leaf replaces): (i) direct — for the carrier produced by the
inhabitation leaf and the system produced by the `ℓ`-adic descent this
is BLGGT §5.3 verbatim; for an abstract carrier or an abstract family
`Pv` the abstract-quantification caveat of pillar β applies (nothing
formal ties an arbitrary `Pv` to a Hilbert eigensystem — that
identification is part of the citation), and (ii) collapse — the
hypothesis set (an irreducible hardly ramified mod-`ℓ` representation,
`ℓ ≥ 5`) is classically unsatisfiable (headline below), so the
statement is classically true for every package. ROUTE AUDIT
(dichotomy, 2026-07-24; unchanged): the alternative route — realizing
the `3`-adic member directly from the base-level carrier data `Wit.τF`
by inducing from `G_F` to `G_ℚ` without Brauer — is strictly deeper:
`Ind_{G_F}^{G_ℚ} τF` has dimension `[F : ℚ] · 2`, so recovering a
`2`-dimensional member from it requires precisely the Brauer virtual
identity that this leaf cites; there is no shallower in-tree route, and
no route through the forbidden modules.

CIRCULARITY GUARD (inherited from pillar β, load-bearing): no discharge
through `Family.lean`, `Lift.lean`, or `Modularity/Interface.lean`.

------------------------------------------------------------------
## ABSORPTION OF THE TWO LOCAL SHAPES (2026-07-26): clauses (2) and (3)

The existential now asserts, besides the Frobenius match (1), the local
shape of `τ` at `3` (2) and at `2` (3). These were two separate sorried
leaves between 2026-07-25 and 2026-07-26
(`blggt_threeadicMember_flatAtThreePow`,
`blggt_threeadicMember_stableLineAtTwo`), each quantified over a package
satisfying only the Frobenius match; their own HONESTY AUDIT recorded
that they were therefore no more derivable than the interface-level
leaves they had replaced. Both are DELETED and folded in here.

**Why this is deduplication, not a larger citation.** A compatible
system in the sense of BLGGT §5.1 is by DEFINITION de Rham (crystalline
at the good places) at the places over its own residue characteristic,
and strictly compatible at every finite place of different residue
characteristic. So the source being cited already contains both local
shapes; asserting only the Frobenius match was UNDER-asserting relative
to BLGGT. Precedent: the independent 2026-07-26 audits at
`threeadicRealization_unramifiedTransfer_of_witness` and at the
conductor node reached the same verdict for a `level` field ("it is
DEDUPLICATION, not hiding — the construction leaf currently
under-asserts relative to its own source").

**Why it must be HERE and nowhere else.** This is the one declaration in
the tree that CHOOSES `τ`. Any statement quantified over an abstract
package constrained only by `compat` cannot carry either local shape:
`compat` pins `τ` at most up to semisimplification, and both shapes are
invisible to semisimplification — see the two counterexample analyses
below.

### Clause (2), the local shape at `3` — Fontaine–Laffaille

For every `m ≥ 1` the `3`-power level `T/3^m T` of the stable lattice
`T = Fin 2 → A` is the group of `ℚ̄_3`-points of the generic fibre of a
finite flat group scheme over `ℤ_3` (`GaloisRep.HasFlatProlongationAt`).

Classically: the compatible system attached to the descended eigensystem
has parallel weight `2` and conductor prime to `3`, so `τ` is
crystalline at `3` with Hodge–Tate weights `{0, 1}` (Carayol/Taylor
local-global compatibility at `p = ℓ` for `p` prime to the level). Over
`ℤ_3` the absolute ramification index is `e = 1 < 2 = p - 1`, exactly the
Fontaine–Laffaille range: `T` is the Tate module of a `3`-divisible group
`𝒢` over `ℤ_3`, and the levels `T/3^m T` are the `ℚ̄_3`-points of the
generic fibres of `𝒢[3^m]`.

LEVEL AUDIT: asserted on the `3`-POWER levels only — those are the
levels of the `3`-divisible group. Arbitrary congruence quotients are
reached from these by Raynaud's closure of finite flat group schemes
under quotients (`hasFlatProlongationAt_of_surjective`), consumed by
`threeadicRealization_hasFlatProlongationAt_of_finite_quotient`, so
demanding them here would re-obligate something the tree already has.
Only `1 ≤ m` is asserted: at `m = 0` the ideal `3^0` is the unit ideal,
the level is a single point, and the transport discharges it outright.

WHY `compat` CANNOT GIVE IT (the counterexample, load-bearing): flatness
at `3` is a property of the EXTENSION CLASS, invisible to
semisimplification. The two extensions of `ℤ/3` by `μ_3` over `ℚ_3`
corresponding to `1` and to `3` in `ℚ_3^×/(ℚ_3^×)^3` have the same
semisimplification and the same Frobenius characteristic polynomials, and
exactly one of them is finite flat over `ℤ_3` (Kummer).

ROUTE AUDIT (2026-07-25, carried over verbatim — FIVE candidate
discharges and cuts, all five refuted or found empty; read this before
spending a worker on a "cheaper route"):

* *no subsingleton collapse*. `A ⧸ 3^m` is a NONZERO finite ring for
  every `m ≥ 1`: `A` is a nonzero `ℤ_3`-module-finite FREE algebra, so
  `3` cannot be a unit in `A` (else `A` would be a `ℚ_3`-algebra and a
  finitely generated free `ℤ_3`-module at once, forcing `A = 0`), i.e.
  `3 ∈ 𝔪_A`. Hence the level is `(A ⧸ 3^m)^2 ≠ 0` and
  `hasFlatProlongationAt_of_subsingleton` is unavailable;
* *no junk witness*. `GaloisRep.HasFlatProlongationAt` is a genuinely
  RESTRICTIVE condition on a finite `Γ ℚ_3`-module, not a shape
  condition: every finite `Γ ℚ_3`-module is the point group of a finite
  étale `ℚ_3`-Hopf algebra, but only some admit a finite FLAT `𝒪ᵥ`-model.
  Over `ℤ_3` (`e = 1 < p - 1 = 2`) Raynaud/Oort–Tate classify the
  order-`3` group schemes: the generic fibre of one is `ℤ/3(ω^i · ψ)`
  with `0 ≤ i ≤ e = 1` and `ψ` UNRAMIFIED. Explicit non-example: the
  quadratic characters of `G_{ℚ_3}` are the unramified one, the one
  cutting out `ℚ_3(√-3) = ℚ_3(ζ_3)` — which IS `ω` — and the one cutting
  out `ℚ_3(√3)`; the last is ramified and is not `ω`, so `ℤ/3` with that
  character has NO finite flat model over `ℤ_3`;
* *the reduction to level `1` is FALSE* (the shortcut most worth
  refuting explicitly). One is tempted to run
  `0 → T/3^m → T/3^{m+1} → T/3 → 0` and induct, using "an extension of
  flat by flat is flat". That is FALSE for GALOIS MODULES: over an
  absolutely unramified base with `e < p - 1` the comparison
  `Ext¹_fl → Ext¹_Γ` is INJECTIVE (Fontaine's uniqueness of
  prolongations) but NOT surjective. Witness: `Ext¹(ℤ/p, μ_p)`, where
  the flat classes are `ℤ_p^× / (ℤ_p^×)^p` inside the Galois classes
  `ℚ_p^× / (ℚ_p^×)^p` (Kummer) — index `p`, the missing class being that
  of the uniformizer `p` itself, i.e. the Tate-curve/multiplicative-
  reduction extension `ℚ_p(p^{1/p})`. Same phenomenon as the classical
  criterion that a multiplicative-reduction curve has `E[p]` finite flat
  at `p` iff `p ∣ v(Δ)`. So flatness of ALL levels is strictly more than
  flatness of the first, and the induction cannot be repaired;
* *the `p`-divisible-group cut is EQUIVALENT, not a reduction*.
  Replacing this clause by "`T` is the Tate module of a `3`-divisible
  group over `ℤ_3`" relocates the same sorry: the easy direction is the
  present statement, and the converse is a theorem (Tate; via Fontaine's
  `e < p - 1` uniqueness). Worse, the cut STRENGTHENS it, since a
  `PDivisibleGroup` interface also carries transition maps this statement
  does not need. Deliberately NOT done;
* *the `ℤ_3`-native restatement is cosmetic*. `𝒪ᵥ ≅ ℤ_3` at `v = (3)`
  (`Rat.HeightOneSpectrum.adicCompletionIntegers.padicIntEquiv`, with
  `Rat.HeightOneSpectrum.adicCompletion.padicEquiv` on the generic
  fibre), so a finite flat Hopf `ℤ_3`-algebra base-changes to an
  `𝒪ᵥ`-one; restating over `ℤ_3` makes it strictly stronger at zero
  gain. The bridge, worth recording for whoever DOES formalize the
  input: `(primesEquiv v₃ : ℕ) = 3` is available from
  `Rat.HeightOneSpectrum.natGenerator_dvd_iff` /
  `Rat.HeightOneSpectrum.span_natGenerator` (both stated through
  `IsIntegralClosure.intEquiv`) together with
  `asIdeal_toHeightOneSpectrum_eq_span` of
  `GroupScheme/ConnectedEtale.lean`, and the `ℤ_[a] ≃+* ℤ_[b]` transport
  along `a = b` is a one-line `subst` (`Fact` is a `Prop`, so the
  instance argument is proof-irrelevant).

CONSUMPTION NOTE for whoever formalizes the input (a non-obvious finding
of the same pass): `GaloisRep.hasFlatProlongationAt_of_hopf_package` of
`Deformations/RepresentationTheory/FlatProlongation.lean` — the tree's
only general producer of a flat-prolongation package — is UNUSABLE here.
It requires a base ring `R` with `Algebra R ℚ` (its points comparison
runs through `ℚ̄` and `algHomEquivOfFinite`), i.e. a group scheme over
the LOCALIZATION `ℤ_(3)`, whereas Fontaine–Laffaille produces one over
the COMPLETION `ℤ_3`, which does not map to `ℚ`. The input must be fed
either through the `padicIntEquiv` bridge above or straight into the
definition of `GaloisRep.HasFlatProlongationAt` (which is purely local).

MISSING-MACHINERY AUDIT (2026-07-25, dependency order — none of this
exists in mathlib or in this tree; each item named as the statement an
owner would be dispatched at):

1. *`p`-divisible groups over a complete DVR*: a structure carrying a
   system of finite flat Hopf `𝒪`-algebras `H m` with the `p^m`-torsion
   inclusions, its generic-fibre point functor, and its Tate module.
   (Everything needed to STATE this is present — `HopfAlgebra`,
   `Module.Flat`, `Module.Finite`, and the convolution monoid on points
   — so this is the first buildable item, but on its own it buys no
   reduction.)
2. *Filtered `φ`-modules / strongly divisible `ℤ_p`-lattices in
   Hodge–Tate weights `[0, p-2]` (Fontaine–Laffaille modules)*, and the
   FL functor to finite `Γ ℚ_p`-modules.
3. *The Fontaine–Laffaille equivalence*: the FL functor of (2) is an
   equivalence onto the finite flat models of (1) in the range
   `e < p - 1`. Stating the crystalline side needs the period ring
   `B_cris` (mathlib has `WittVector` and nothing above it), the deepest
   missing prerequisite of the whole chain.
4. *Local-global compatibility at `p = ℓ`* (Carayol, Taylor): the
   `3`-adic member of a parallel-weight-`2` compatible system of
   conductor prime to `3` is crystalline at `3` with Hodge–Tate weights
   `{0, 1}`. Not stateable before (3).

Item 4 composed with items 3–1 IS clause (2); there is no intermediate
at which that sorry can honestly be split.

RE-VERIFIED MECHANICALLY 2026-07-26 (a later owner): item 3's "deepest
missing prerequisite", the period ring `B_cris`, is still absent —
`BCris|B_cris|crystallineRep|HodgeTate` matches NO file in `Mathlib/`,
and `RingTheory/Perfectoid/` still contains exactly `BDeRham.lean`,
`FontaineTheta.lean` and `Untilt.lean`. Nor is there any Hilbert
modular form or Shimura curve development to state item 4 over. So the
"no intermediate" verdict above is not merely inherited; it has been
re-checked against the pin as it stands today.

Literature for (2): Fontaine–Laffaille, *Construction de représentations
p-adiques*, Ann. Sci. ÉNS 15 (1982); Raynaud, *Schémas en groupes de
type (p, …, p)*, Bull. SMF 102 (1974); Carayol, Ann. Sci. ÉNS 19 (1986)
and Taylor, Invent. Math. 98 (1989) (the weight-2 local shape at primes
over `p` prime to the level); Breuil, *Groupes p-divisibles, groupes
finis et modules filtrés*, Ann. of Math. 152 (2000) (the range-free
refinement); BLGGT §5.5. FLT blueprint ch. 4: "flat at 3".

### Clause (3), the local shape at `2` — the Weil–Deligne type

There are an `A`-basis `b` of the stable lattice and an unramified
square-trivial character `δ` of `G_{ℚ_2}` with

  `τ g v ≡ δ g 1 • v  (mod A · b 0)`  for all `g` and all `v`.

That single clause is the whole classical content. It already forces the
line `A · b 0` to be `G_{ℚ_2}`-STABLE (take `v = b 0`: both
`τ g (b 0) - δ g 1 • b 0` and `δ g 1 • b 0` lie in the line), so the
shape "extension of the unramified quadratic `δ` by something, in a basis
adapted to the lattice" is stated without ever mentioning a matrix. The
matrix reading — upper-triangularity with `δ g 1` on the diagonal — is
PROVEN from it in `threeadicRealization_weilDeligneType_two_of_witness`.

WHY THIS IS PART OF THE CITATION. `ρ`'s type at `2` is an extension of an
unramified square-trivial character by its cyclotomic twist
(`hρ.isTameAtTwo` with the cyclotomic determinant). The type is carried
across the compatible system by STRICT COMPATIBILITY: a single
Weil–Deligne representation `WD_v(R)` over the coefficient field
reproduces `WD(r_λ|G_{F_v})^{F-ss}` for every `λ` of residue
characteristic differing from that of `v` (BLGGT §5.1, the display
`ς WD_v(R) ≅ WD(r_λ|G_{F_v})^{F-ss}`; here `v = 2` and the places
compared are `λ | ℓ` and `λ | 3`, legitimate because `2 ∉ {ℓ, 3}`).
Strict compatibility of the system through which the descent runs is
Carayol's theorem for Hilbert newforms — the local constituent is pinned
at EVERY finite place, not merely almost all — and membership of `ρ` in
such a system is BLGGT Theorem 5.5.1. The stable-lattice normalization of
the descent turns the `E_λ`-rational stable line into a saturated
`A`-line, i.e. the first vector of an `A`-basis, which is why a basis may
be demanded. `δ` is handed over as a `GaloisRep` because it IS the
quotient character of the constant type — in particular continuous, being
the local component of the compatible system's unramified twist.

DISCHARGE-ROUTE AUDIT (2026-07-25, carried over; all three closed, and
the FIRST is what forced the cut-level repair):

* *From the carrier's own fields* — impossible. `compat` pins
  characteristic polynomials only at primes `q ∉ S₁` with `q ∉ {2,3,ℓ}`;
  nothing mentions the decomposition group at `2`, and no formal argument
  recovers a local type at `2` from Frobenius data away from `2` — that
  recovery IS strict compatibility, i.e. the citation itself.
* *The odd-prime dichotomy* (collapse) — closed by the circularity guard,
  and independently by declaration order: the only two in-tree
  dichotomies are `Modularity/Interface.lean`'s
  `not_isIrreducible_of_isHardlyRamified_of_odd` (banned) and this
  module's own headline `not_isIrreducible_of_isHardlyRamified_of_five_le`,
  declared BELOW.
* *The `3`-adic classification* — closed by circularity, and this is the
  route that looks promising: `τ`'s determinant, unramifiedness and
  flatness are established elsewhere, so three of the four hardly ramified
  conditions are in hand. But every theorem in that chain
  (`ModThree.lean`'s `mod_three`, `mod_three_reducible`,
  `mod_three_of_stable_line`; `Threeadic.lean`'s
  `exists_global_triangular_of_residual_trivial_quotient`,
  `exists_frobenius_triangular`, `three_adic`) takes the WHOLE
  `IsHardlyRamified` structure as a single hypothesis — none takes the
  four conditions separately — and the tame-at-`2` field is genuinely
  consumed (`quotCharacter_unramified_at_two`, on the path
  `mod_three → mod_three_of_stable_line`). Supplying it would require
  `threeadicRealization_isTameAtTwo_of_witness`, which is proven THROUGH
  this clause.

FAITHFULNESS RE-CHECK (2026-07-25, carried over): neither vacuous nor
inertia-widened. NOT VACUOUS — `A` is a local ring, hence nontrivial, so
`Submodule.span A {b 0}` is a PROPER submodule for every basis `b`; the
congruence clause therefore carries real content (the rank-`1` quotient
by that line is the character `δ`), and no junk witness can be assembled
from the hypotheses alone. NOT WIDENED — `δ`'s unramifiedness is
quantified over `AddSubgroup.inertia` only, while the congruence is
quantified over the whole decomposition group `Γ ℚ_[2]`; that is the
correct shape and it matches `IsHardlyRamified.isTameAtTwo` verbatim.

PACKAGING NOTE (2026-07-25, carried over): demanding a BASIS rather than
a bare surjection adds no literature content — over the local ring `A`
the two forms are equivalent. A surjection `πq : A² ↠ A` has one of
`πq e₀`, `πq e₁` a unit (the non-units of a local ring form an ideal),
and the triangular change of basis this determines is invertible,
yielding a basis `b` with `πq (b 0) = 0`, `πq (b 1) = 1`, hence
`ker πq = A · b 0`. So restating in quotient form would shrink nothing.

Literature for (3) (page-level checks 2026-07-25 against the downloaded
sources): BLGGT, Ann. of Math. 179 (2014) — §5.1 for the definition of a
strictly compatible system (the display quoted above) and Theorem 5.5.1;
Carayol, *Sur les représentations `l`-adiques associées aux formes
modulaires de Hilbert*, Ann. Sci. ÉNS (4) 19 (1986) 409–468, Théorème (A)
p. 410: a strictly compatible system `{σ_λ}` with `σ_λ|W_p ≅ σ_λ(π_p)` at
EVERY finite place `p` of residue characteristic different from that of
`λ`, `σ(π_p)` being the `F`-semisimple degree-`2` Weil–Deligne
representation of the Hecke correspondence (§0.5). Khare–Wintenberger,
Invent. Math. 178 (2009) 485–504, for the same constancy inside the
minimal-lifting induction (paywalled; NOT page-verified — the two
references above are the load-bearing ones). FLT blueprint ch. 4: "tame
at 2".

### Scope of the absorption

What it buys: the automorphic citation now asserts what its source
actually proves, and the sorry count drops by two with no mathematics
hidden. What it does NOT buy: clauses (2) and (3) remain CITED, not
proven — the missing-machinery chain above is untouched, and this leaf is
still the single residual citation of the whole `3`-adic construction.

## ABSORPTION OF THE TWO RAMIFICATION CLAUSES (2026-07-26): (4) and (5)

The same repair, run a second time at the same seam, and predicted
verbatim by the ABSORPTION section above ("Precedent: the independent
2026-07-26 audits at `threeadicRealization_unramifiedTransfer_of_witness`
and at the conductor node reached the same verdict for a `level` field").
The existential now also asserts that `τ` is unramified at `ℓ` (4) and
that `τ` is unramified at every `p ∉ {3, ℓ}` where `ρ` is unramified (5).
These were the two sorried leaves
`threeadicRealization_isUnramifiedAtEll_of_witness` and
`threeadicRealization_unramifiedTransfer_of_witness`; both are now
one-line projections of the corresponding new `ThreeadicRealization`
fields `unramifiedAtEll` and `unramifiedTransfer`, discharged here.

**Why it must be HERE and nowhere else** — identical to the argument for
(2) and (3), and independently re-derived by three separate audits at the
two leaves: inertia data is invisible to `compat`, which pins `τ` at most
up to SEMISIMPLIFICATION. The counterexample those audits record is
sharp and is worth keeping in view: over `ℚ` the extensions of `1` by the
`3`-adic cyclotomic character are classified by `H¹(G_ℚ, ℤ_3(1))`, i.e.
by `(ℚ^×)^∧_3` (Kummer), and a class of nonzero valuation at `p` is
RAMIFIED at `p` while having the same Frobenius characteristic polynomial
as the split extension at EVERY prime. So no clause of the old interface
could distinguish them, and the datum must be chosen with `τ`.

**Why clause (5) is deduplication.** BLGGT Theorem 5.5.1 produces a
member of a STRICTLY compatible system, which by §5.1 already fixes the
local parameters at every finite place of residue characteristic `≠ 3`.
Asserting only the Frobenius match was again UNDER-asserting relative to
the source, and the derived leaf was paying for the difference by citing
the same theorem a second time.

**Why clause (4) is a genuinely distinct input, and is kept separate.**
Strict compatibility does NOT say the parameter at `ℓ` is unramified; it
says the members agree there. Unramifiedness at `ℓ` comes from the
newform's level being prime to `ℓ`, which is FONTAINE–LAFFAILLE applied
to `ρ` — flat at `ℓ` by `hρ.isFlat` — exactly as clause (2) is
Fontaine–Laffaille at `3`. Bundling (4) into (5) would have destroyed the
2026-07-25 separation of the two literature inputs, which is why they are
two clauses with two attributions rather than one. This answers, rather
than overrides, the objection recorded in the NARROWING AUDIT at
`threeadicRealization_unramifiedTransfer_of_witness` that a seam change
would hide two inputs inside one citation.

### Scope of this second absorption

What it buys: the frontier drops by two more leaves, a duplicated
citation of BLGGT Theorem 5.5.1 is removed, and the interface stops
quantifying over packages its own source excludes. What it does NOT buy:
clauses (4) and (5) remain CITED, not proven. In particular the
Weil–Deligne / higher-ramification machinery audited as absent at those
two leaves is still absent, and nothing here brings a formal
Fontaine–Laffaille functor or a formal strict-compatibility theorem into
the tree. This leaf remains the single residual citation of the whole
`3`-adic construction, now carrying five clauses instead of three.

## MACHINERY RE-AUDIT 2026-07-27: four absences CONFIRMED, one REFUTED

Re-run against the pin as it stands, because a "still absent" claim is a
DATED claim. Each item below names the check that would refute it.

CONFIRMED ABSENT — all four, so the prerequisite chain for clauses (2)–(5)
is unchanged and this leaf is not closable by any restatement:

* no Weil group and no Weil–Deligne representations:
  `grep -rl 'WeilDeligne\|weilGroup\|WeilGroup'` is EMPTY over `Mathlib/`,
  over `~/cs/FLT/FLT`, and over `Fermat/`;
* `Mathlib/RingTheory/Valuation/RamificationGroup.lean` is STILL exactly
  54 lines — `decompositionSubgroup`, `inertiaSubgroup`, and the
  `TODO: Define higher ramification groups in lower numbering` on line 16.
  So there is no ramification filtration, no tame quotient, and no tame
  character `t_ℓ : I_p ↠ ℤ_ℓ(1)`;
* no `B_cris`, no crystalline/Hodge–Tate machinery, hence no
  Fontaine–Laffaille functor: `grep -rl 'BCris\|B_cris\|HodgeTate\|
  crystallineRep'` over `Mathlib/` is EMPTY and `RingTheory/Perfectoid/`
  still contains exactly `BDeRham.lean`, `FontaineTheta.lean`, `Untilt.lean`;
* no smooth/admissible `GL₂` representations and no local Langlands:
  `grep -rl 'SmoothRep\|AdmissibleRep\|LocalLanglands'` over `Mathlib/`
  is EMPTY.

REFUTED — and this one had become load-bearing, because it is quoted as a
reason not to pursue the automorphic route at the twin Carayol node and
again in the MACHINERY AUDIT further down this file (search
`is NOT vendorable`): the claim that the reference project's automorphy
predicate `GaloisRep.IsAutomorphicOfLevel` "is NOT vendorable, being
defined over that project's quaternionic Hecke-algebra development, which
our pin does not have". **It IS vendorable, and it has been vendored.**
That development's import closure — 109 modules, 20,688 lines, covering
adele rings, restricted products, Haar characters, totally definite
quaternion algebras and their Hecke algebras — now lives under
`Fermat/FLT/{AutomorphicForm,QuaternionAlgebra,DivisionAlgebra,HaarMeasure,
NumberField,DedekindDomain,Hacks,Mathlib}/…` and builds green against our
pin, at a measured cost of one sorried leaf (`isFiniteRelIndex_Δ`, Voight
17.7.13, which the reference discharged with its `axiom knownin1980s`) and
two pin-drift repairs. Refuting check:
`lake build Fermat.FLT.AutomorphicForm.QuaternionAlgebra.HeckeOperators.Concrete`.

What that does NOT buy for THIS leaf, so nobody re-scopes it as cheap: the
vendored theory is automorphic-side machinery, and every one of clauses
(2)–(5) is a GALOIS-side local statement. Clause (2) and clause (4) need
Fontaine–Laffaille; clauses (3) and (5) need strict compatibility, i.e.
`WD_v(−)`. Both are in the CONFIRMED-ABSENT list above and neither is
reachable from Hecke algebras. The vendoring changes the twin Carayol
node's outlook (see the block on that leaf), not this one's.

## DECOMPOSITION 2026-07-27: this node is now PROVEN

The five clauses are no longer all cited. This node is a PROVEN
assembly over `blggt_threeadicHardlyRamifiedMember_of_witness` (above),
which states the SAME package with clauses (1) and (2) verbatim and
with the local data at `2` and the ramification locus written in the
tree's canonical vocabulary — the functional form of
`IsHardlyRamified.isTameAtTwo`, "unramified outside `{2, 3}`", and the
single residual transfer at `2`. Two things are now proven here that
used to sit inside the citation:

* clause (3), the STABLE LINE at `2`, is derived from the functional
  form by `exists_basis_finTwo_span_eq_ker` (PROVEN, above): over the
  local ring `A` a surjection `A² ↠ A` splits, so `ker πq` is a free
  rank-one direct summand, and `Γ_{ℚ_2}`-equivariance of `πq` says
  precisely that `τ g v − δ g 1 • v` lies in it. Nothing about the
  representation is used; this is the commutative algebra that the
  citation used to be asked to supply along with the mathematics;
* clauses (4) and (5), the RAMIFICATION LOCUS, are derived from the
  conductor clause together with the transfer at `2` — the case split
  is `p = 2` versus `p ∉ {2, 3}`, and in the second case the
  hypothesis "`ρ` unramified at `p`" is not used at all. The reverse
  derivation is recorded in the equivalence audit on the new node, so
  the cut is information-preserving in both directions.

What did NOT change: clause (1) (Carayol Frobenius compatibility) and
clause (2) (Fontaine–Laffaille at `3`) are carried through verbatim,
and the four theories audited absent above are still absent. The
MACHINERY RE-AUDIT of 2026-07-27 recorded immediately above applies
unchanged to the new node, which is where the literature input now
lives. -/
theorem blggt_threeadicBrauerSum_of_witness
    {ℓ : ℕ} (hℓodd : Odd ℓ) [Fact ℓ.Prime] (hℓ5 : 5 ≤ ℓ)
    {O : Type u} [CommRing O] [IsDomain O] [TopologicalSpace O]
    [IsTopologicalRing O] [Algebra ℤ_[ℓ] O] [IsLocalRing O]
    [Module.Finite ℤ_[ℓ] O] [IsModuleTopology ℤ_[ℓ] O]
    (hZinj : Function.Injective (algebraMap ℤ_[ℓ] O))
    {ρ : GaloisRep ℚ O (Fin 2 → O)}
    (hrank : Module.rank O (Fin 2 → O) = 2)
    (hρ : IsHardlyRamified hℓodd hrank ρ)
    {k : Type u} [Field k] [Finite k] [Algebra ℤ_[ℓ] k]
    [TopologicalSpace k] [DiscreteTopology k]
    {W : Type v} [AddCommGroup W] [Module k W] [Module.Finite k W]
    [Module.Free k W]
    (hW : Module.rank k W = 2) {ρbar : GaloisRep ℚ k W}
    (hρbar : IsHardlyRamified hℓodd hW ρbar)
    (hirr : ρbar.IsIrreducible)
    (π : O →+* k) (hπsurj : Function.Surjective π)
    (hπ : ∀ (q : ℕ) (hq : q.Prime), q ≠ 2 → q ≠ ℓ →
      (ρ.charFrob hq.toHeightOneSpectrumRingOfIntegersRat).map π =
        ρbar.charFrob hq.toHeightOneSpectrumRingOfIntegersRat)
    (Wit : PotentialModularityWitness ℓ O ρ)
    (S₀ : Finset (HeightOneSpectrum (NumberField.RingOfIntegers ℚ)))
    (Pv : HeightOneSpectrum (NumberField.RingOfIntegers ℚ) →
      Polynomial Wit.E)
    (hPv : ∀ (q : ℕ) (hq : q.Prime),
      hq.toHeightOneSpectrumRingOfIntegersRat ∉ S₀ →
      q ≠ 2 → q ≠ 3 → q ≠ ℓ →
      (ρ.charFrob hq.toHeightOneSpectrumRingOfIntegersRat).map Wit.ιO =
        (Pv hq.toHeightOneSpectrumRingOfIntegersRat).map Wit.ψℓ) :
    ∃ (S₁ : Finset (HeightOneSpectrum (NumberField.RingOfIntegers ℚ)))
      (A : Type u) (_ : CommRing A) (_ : IsDomain A)
      (_ : Algebra ℤ_[3] A) (_ : Module.Finite ℤ_[3] A),
      letI : TopologicalSpace A := moduleTopology ℤ_[3] A
      letI : IsTopologicalRing A :=
        isTopologicalRing_moduleTopology_of_finite 3 A
      ∃ (τ : GaloisRep ℚ A (Fin 2 → A))
        (ιA : A →+* AlgebraicClosure ℚ_[3]),
        -- (1) Frobenius compatibility away from `S₁` (Carayol)
        (∀ (q : ℕ) (hq : q.Prime),
          hq.toHeightOneSpectrumRingOfIntegersRat ∉ S₁ →
          q ≠ 2 → q ≠ 3 → q ≠ ℓ →
          (τ.charFrob hq.toHeightOneSpectrumRingOfIntegersRat).map ιA =
            (Pv hq.toHeightOneSpectrumRingOfIntegersRat).map Wit.ψ₃) ∧
        -- (2) the local shape at `3`: Fontaine–Laffaille on the
        -- `3`-power levels of the stable lattice
        (∀ m : ℕ, 1 ≤ m →
          (τ.baseChange (A ⧸ Ideal.span {(3 : A) ^ m})).HasFlatProlongationAt
            (Nat.Prime.toHeightOneSpectrumRingOfIntegersRat
              (Fact.out : Nat.Prime 3))) ∧
        -- (3) the local shape at `2`: the Weil–Deligne type, as a
        -- stable line with unramified quadratic quotient
        (∃ (b : Module.Basis (Fin 2) A (Fin 2 → A))
          (δ : GaloisRep ℚ_[2] A A),
          (AddSubgroup.inertia
              ((IsLocalRing.maximalIdeal Z2bar).toAddSubgroup :
                AddSubgroup Z2bar)
              (Field.absoluteGaloisGroup ℚ_[2]) ≤ δ.ker) ∧
          (∀ g : Field.absoluteGaloisGroup ℚ_[2], δ g * δ g = 1) ∧
          ∀ (g : Field.absoluteGaloisGroup ℚ_[2]) (v : Fin 2 → A),
            τ.map (algebraMap ℚ ℚ_[2]) g v - δ g 1 • v ∈
              Submodule.span A {b 0}) ∧
        -- (4) unramifiedness at `ℓ`: the newform's level is prime to
        -- `ℓ` because `ρ` is flat there (Fontaine–Laffaille at the
        -- `ℓ`-adic member's own residue characteristic — a SECOND and
        -- distinct literature input, kept in its own clause so the
        -- 2026-07-25 separation of the two inputs is preserved)
        (τ.IsUnramifiedAt
          (Nat.Prime.toHeightOneSpectrumRingOfIntegersRat
            (Fact.out : ℓ.Prime))) ∧
        -- (5) member-independence of the ramification locus away from
        -- `3` and `ℓ` (Carayol / BLGGT Theorem 5.5.1: the constructed
        -- system is STRICTLY compatible, hence its local parameters at
        -- every `p ∤ 3` agree with those of the `ℓ`-adic member)
        (∀ p (hp : p.Prime), p ≠ 3 → p ≠ ℓ →
          ρ.IsUnramifiedAt hp.toHeightOneSpectrumRingOfIntegersRat →
          τ.IsUnramifiedAt hp.toHeightOneSpectrumRingOfIntegersRat) := by
  classical
  -- the citation, in the canonical vocabulary
  obtain ⟨S₁, A, hCR, hDom, hAlg, hFin, τ, ιA, hmatch, hflat, htame,
      hunrOut, htwo⟩ :=
    blggt_threeadicHardlyRamifiedMember_of_witness hℓodd hℓ5 hZinj hrank hρ
      hW hρbar hirr π hπsurj hπ Wit S₀ Pv hPv
  haveI hLR : IsLocalRing A := isLocalRing_of_finite_padicInt 3 A
  have hℓ2 : ℓ ≠ 2 := by rintro rfl; simp [Nat.odd_iff] at hℓodd
  have hℓ3 : ℓ ≠ 3 := by omega
  refine ⟨S₁, A, hCR, hDom, hAlg, hFin, τ, ιA, hmatch, hflat, ?_,
    hunrOut ℓ Fact.out hℓ2 hℓ3, ?_⟩
  · -- (3): the stable line, from the surjective quotient functional.
    -- The kernel of `πq` is a free rank-one direct summand of the
    -- lattice (`exists_basis_finTwo_span_eq_ker`), and equivariance of
    -- `πq` says exactly that `τ g v - δ g 1 • v` lies in it.
    obtain ⟨πq, hsurj, δ, hδur, hδsq, hcomm⟩ := htame
    obtain ⟨b, hspan⟩ := exists_basis_finTwo_span_eq_ker πq hsurj
    refine ⟨b, δ, hδur, hδsq, fun g v => ?_⟩
    rw [hspan, LinearMap.mem_ker, map_sub, hcomm g v, map_smul, smul_eq_mul]
    -- an `A`-endomorphism of `A` is multiplication by its value at `1`
    have hscal : δ g (πq v) = πq v * δ g 1 := by
      conv_lhs => rw [show (πq v : A) = πq v • (1 : A) by
        rw [smul_eq_mul, mul_one]]
      rw [map_smul, smul_eq_mul]
    rw [hscal, mul_comm, sub_self]
  · -- (5): the ramification-locus transfer — the conductor clause
    -- covers every `p ∉ {2, 3}`, and `p = 2` is the residual transfer
    intro p hp hp3 hpℓ hρp
    by_cases hp2 : p = 2
    · subst hp2
      exact htwo hp hρp
    · exact hunrOut p hp hp2 hp3

/-- **Brauer descent, `3`-adic side — the virtual sum is a true
representation on a stable lattice** (PROVEN assembly, 2026-07-25 —
BLGGT §5.3 at one remove; see the ASSEMBLY note at the end of this
docstring): given the descended
rational Hecke system `(S₀, Pv)` produced on the `ℓ`-adic side
(`exists_heckeField_system_of_witness` — the family of `E`-coefficient
polynomials interpolating `charFrob ρ` through `ιO`/`ψℓ`), the SAME
system is realized `3`-adically: there are a finite exceptional set
`S₁`, a coefficient ring `A` — a local DOMAIN, module-finite over
`ℤ_3` with its module topology and `ℤ_3 ↪ A` (classically the integers
`O_{E_λ}` of the completion of the Hecke field at a place `λ | 3`) — a
representation `τ` of `G_ℚ` on `Fin 2 → A`, and an injective
coefficient embedding `ιA : A ↪ ℚ̄_3` such that `τ`'s Frobenius
characteristic polynomials away from `S₁` are the `ψ₃`-images of `Pv`.

Classically this is the Brauer trick at the place `λ | 3`. Brauer's
induction theorem on `Gal(F/ℚ)` (`Wit.galoisF`) writes
`1 = Σ cᵢ · Ind_{Hᵢ}^{Gal(F/ℚ)} χᵢ` with `Hᵢ` solvable and `χᵢ`
one-dimensional; solvable base change descends the Hilbert newform to
each `Fᵢ = F^{Hᵢ}`, and Carayol/Taylor attach to each descended form
its `3`-adic realization (the carrier's `τF` at the base level,
`Wit.matchF₃`). The virtual sum
`Σ cᵢ · Ind_{G_{Fᵢ}}^{G_ℚ} (τ_{fᵢ,λ} ⊗ χᵢ)` has, by construction, the
same trace function as the `ψ₃`-transport of the Hecke system, hence
Frobenius characteristic polynomials `Pv` through `ψ₃`; it is a TRUE
(not merely virtual) representation because at the place over `ℓ` the
corresponding sum is the character of `ρ` — a genuine `2`-dimensional
representation — and Brauer–Nesbitt pins the semisimple representation
at every place of `E`. Finally the resulting `2`-dimensional
`E_λ`-representation of the COMPACT group `G_ℚ` admits a stable
lattice (the `O_{E_λ}`-span of the orbit of any lattice under the
compact image is finitely generated and stable), which is the
coefficient package `A` together with `τ` and the embedding
`ιA : O_{E_λ} ↪ ℚ̄_3`. The exceptional set `S₁` collects `S₀`, the
primes ramified in `F`, and the primes below the bad places of the
descended forms.

Literature: Barnet-Lamb–Gee–Geraghty–Taylor, *Potential automorphy and
change of weight*, Ann. of Math. 179 (2014), §5.3 (the Brauer trick:
the virtual sum is a true representation, and the constructed system
is weakly compatible) and Theorem 5.5.1; Khare–Wintenberger, *Serre's
modularity conjecture (I)*, Invent. Math. 178 (2009), §5; Taylor,
*Remarks on a conjecture of Fontaine and Mazur*, J. Inst. Math.
Jussieu 1 (2002), §6; Carayol, Ann. Sci. ÉNS 19 (1986) (local-global
compatibility at unramified places, fixing the Frobenius data);
Serre, *Abelian ℓ-adic Representations*, I.1 (stable lattices for
continuous representations of compact groups).

ASSEMBLY (2026-07-25, PROVEN): this used to BE the citation; it is now
a proven assembly over the strictly narrower geometric core
`blggt_threeadicBrauerSum_of_witness` plus the coefficient-ring bricks
proven above for the twin Carayol node — the `ℤ_3`-module topology is a
ring topology and is of course the module topology
(`isTopologicalRing_moduleTopology_of_finite`), and both injectivity
components follow from the mere existence of the comparison embedding
into the characteristic-zero field `ℚ̄_3`
(`injective_of_finite_padicInt_charZero`,
`injective_algebraMap_of_ringHom_charZero`). Nothing else changes: the
coefficient ring, the representation, the embedding `ιA`, the
exceptional set and the matching clause are carried verbatim from the
core, so there is no lattice change and no charpoly to re-compute.

PIN AUDIT (2026-07-24, RE-AUDITED 2026-07-25 — see the core's docstring
for the full search record): the stable-lattice step is NOT separable
into an in-tree formal lemma at this pin — the pin has the invariance of
an orbit span (`Module.End.span_orbit_mem_invtSubmodule`) but nothing
making it FINITELY GENERATED (no compactness/boundedness theory for
valued fields, no maximal-order material), and `~/cs/FLT` has no
vendorable Lean development of the Brauer trick at all. So the core leaf
remains stated in lattice (coefficient-ring) form, exactly the shape the
realization carrier and the proven `3`-adic classification consume. What
IS split off as formal is the coefficient-ring bookkeeping listed above,
the freeness normalization
(`module_free_padicInt_of_algebraMap_injective`) and the interpolant
uniqueness (`heckePoly_transport`).

SOUNDNESS AUDIT (both ways, 2026-07-24): (i) direct — for the carrier
produced by the inhabitation leaf and the system produced by the
`ℓ`-adic descent this is BLGGT §5.3 verbatim; for an abstract carrier
or an abstract family `Pv` the abstract-quantification caveat of
pillar β applies (nothing formal ties an arbitrary `Pv` to a
Hilbert eigensystem — that identification is part of the citation),
and (ii) collapse — the hypothesis set (an irreducible hardly ramified
mod-`ℓ` representation, `ℓ ≥ 5`) is classically unsatisfiable
(headline below), so the statement is classically true for every
package. ROUTE AUDIT (dichotomy, 2026-07-24): the alternative route —
realizing the `3`-adic member directly from the base-level carrier
data `Wit.τF` by inducing from `G_F` to `G_ℚ` without Brauer — is
strictly deeper: `Ind_{G_F}^{G_ℚ} τF` has dimension `[F : ℚ] · 2`, so
recovering a `2`-dimensional member from it requires precisely the
Brauer virtual identity that this leaf cites; there is no shallower
in-tree route, and no route through the forbidden modules.

CIRCULARITY GUARD (inherited from pillar β, load-bearing): no
discharge through `Family.lean`, `Lift.lean`, or
`Modularity/Interface.lean`. -/
theorem exists_threeadicBrauerSum_of_witness
    {ℓ : ℕ} (hℓodd : Odd ℓ) [Fact ℓ.Prime] (hℓ5 : 5 ≤ ℓ)
    {O : Type u} [CommRing O] [IsDomain O] [TopologicalSpace O]
    [IsTopologicalRing O] [Algebra ℤ_[ℓ] O] [IsLocalRing O]
    [Module.Finite ℤ_[ℓ] O] [IsModuleTopology ℤ_[ℓ] O]
    (hZinj : Function.Injective (algebraMap ℤ_[ℓ] O))
    {ρ : GaloisRep ℚ O (Fin 2 → O)}
    (hrank : Module.rank O (Fin 2 → O) = 2)
    (hρ : IsHardlyRamified hℓodd hrank ρ)
    {k : Type u} [Field k] [Finite k] [Algebra ℤ_[ℓ] k]
    [TopologicalSpace k] [DiscreteTopology k]
    {W : Type v} [AddCommGroup W] [Module k W] [Module.Finite k W]
    [Module.Free k W]
    (hW : Module.rank k W = 2) {ρbar : GaloisRep ℚ k W}
    (hρbar : IsHardlyRamified hℓodd hW ρbar)
    (hirr : ρbar.IsIrreducible)
    (π : O →+* k) (hπsurj : Function.Surjective π)
    (hπ : ∀ (q : ℕ) (hq : q.Prime), q ≠ 2 → q ≠ ℓ →
      (ρ.charFrob hq.toHeightOneSpectrumRingOfIntegersRat).map π =
        ρbar.charFrob hq.toHeightOneSpectrumRingOfIntegersRat)
    (Wit : PotentialModularityWitness ℓ O ρ)
    (S₀ : Finset (HeightOneSpectrum (NumberField.RingOfIntegers ℚ)))
    (Pv : HeightOneSpectrum (NumberField.RingOfIntegers ℚ) →
      Polynomial Wit.E)
    (hPv : ∀ (q : ℕ) (hq : q.Prime),
      hq.toHeightOneSpectrumRingOfIntegersRat ∉ S₀ →
      q ≠ 2 → q ≠ 3 → q ≠ ℓ →
      (ρ.charFrob hq.toHeightOneSpectrumRingOfIntegersRat).map Wit.ιO =
        (Pv hq.toHeightOneSpectrumRingOfIntegersRat).map Wit.ψℓ) :
    ∃ (S₁ : Finset (HeightOneSpectrum (NumberField.RingOfIntegers ℚ)))
      (A : Type u) (_ : CommRing A) (_ : IsDomain A)
      (_ : TopologicalSpace A) (_ : IsTopologicalRing A)
      (_ : Algebra ℤ_[3] A) (_ : IsLocalRing A)
      (_ : Module.Finite ℤ_[3] A) (_ : IsModuleTopology ℤ_[3] A)
      (_ : Function.Injective (algebraMap ℤ_[3] A))
      (τ : GaloisRep ℚ A (Fin 2 → A))
      (ιA : A →+* AlgebraicClosure ℚ_[3]) (_ : Function.Injective ιA),
      -- (1) Frobenius compatibility away from `S₁` (Carayol)
      (∀ (q : ℕ) (hq : q.Prime),
        hq.toHeightOneSpectrumRingOfIntegersRat ∉ S₁ →
        q ≠ 2 → q ≠ 3 → q ≠ ℓ →
        (τ.charFrob hq.toHeightOneSpectrumRingOfIntegersRat).map ιA =
          (Pv hq.toHeightOneSpectrumRingOfIntegersRat).map Wit.ψ₃) ∧
      -- (2) the local shape at `3` (Fontaine–Laffaille)
      (∀ m : ℕ, 1 ≤ m →
        (τ.baseChange (A ⧸ Ideal.span {(3 : A) ^ m})).HasFlatProlongationAt
          (Nat.Prime.toHeightOneSpectrumRingOfIntegersRat
            (Fact.out : Nat.Prime 3))) ∧
      -- (3) the local shape at `2` (the Weil–Deligne type)
      (∃ (b : Module.Basis (Fin 2) A (Fin 2 → A))
        (δ : GaloisRep ℚ_[2] A A),
        (AddSubgroup.inertia
            ((IsLocalRing.maximalIdeal Z2bar).toAddSubgroup :
              AddSubgroup Z2bar)
            (Field.absoluteGaloisGroup ℚ_[2]) ≤ δ.ker) ∧
        (∀ g : Field.absoluteGaloisGroup ℚ_[2], δ g * δ g = 1) ∧
        ∀ (g : Field.absoluteGaloisGroup ℚ_[2]) (v : Fin 2 → A),
          τ.map (algebraMap ℚ ℚ_[2]) g v - δ g 1 • v ∈
            Submodule.span A {b 0}) ∧
      -- (4) unramifiedness at `ℓ` (Fontaine–Laffaille at the `ℓ`-adic
      -- member's own residue characteristic)
      (τ.IsUnramifiedAt
        (Nat.Prime.toHeightOneSpectrumRingOfIntegersRat
          (Fact.out : ℓ.Prime))) ∧
      -- (5) member-independence of the ramification locus away from `3`
      -- and `ℓ` (Carayol / BLGGT strict compatibility)
      (∀ p (hp : p.Prime), p ≠ 3 → p ≠ ℓ →
        ρ.IsUnramifiedAt hp.toHeightOneSpectrumRingOfIntegersRat →
        τ.IsUnramifiedAt hp.toHeightOneSpectrumRingOfIntegersRat) := by
  classical
  -- (a) the NARROWED BLGGT citation: the Brauer sum comes back over a
  -- bare local domain, module-finite over `ℤ_3`, with no topology, no
  -- `ℤ_3`-injectivity and no injectivity of the comparison embedding
  -- asserted
  obtain ⟨S₁, A, hCR, hDom, hAlg, hFin, τ, ιA, hmatch, hflat, hline,
    hunrEll, hunrTransfer⟩ :=
    blggt_threeadicBrauerSum_of_witness hℓodd hℓ5 hZinj hrank hρ hW hρbar
      hirr π hπsurj hπ Wit S₀ Pv hPv
  -- (a') locality of the coefficient ring is no longer part of the
  -- citation: a DOMAIN module-finite over `ℤ_3` is local, by the
  -- henselian-pair brick proven above
  haveI hLR : IsLocalRing A := isLocalRing_of_finite_padicInt 3 A
  -- (b) the coefficient-ring bookkeeping, all of it PROVEN above (the
  -- same bricks the twin Carayol assembly uses): the canonical module
  -- topology is a ring topology and is of course the module topology,
  -- and both injectivity statements follow from the mere existence of
  -- the characteristic-zero comparison embedding `ιA`.
  --
  -- Three elaboration precautions, all forced by the fact that `p` and
  -- the coefficient ring's topology occur in these bricks only inside
  -- INSTANCE arguments, where unification against the goal cannot reach
  -- them: the ring-topology brick is elaborated with no expected type
  -- (so its `p` is fixed by the explicit `3`), `p := 3` is passed by
  -- name to the embedding-injectivity brick, and the `IsModuleTopology`
  -- component is given as a `refine` hole with its topology argument
  -- spelled out — the anonymous constructor does not propagate the
  -- topology from the positional component that supplies it
  haveI hTR := isTopologicalRing_moduleTopology_of_finite 3 A
  -- The LOCAL-SHAPE clauses (2) and (3) and the two RAMIFICATION clauses
  -- (4) and (5) are carried through verbatim: they are chosen by the
  -- citation together with `τ`, and nothing here touches the
  -- representation or the lattice.
  refine ⟨S₁, A, hCR, hDom, moduleTopology ℤ_[3] A, hTR, hAlg, hLR, hFin, ?_,
    injective_algebraMap_of_ringHom_charZero ιA, τ, ιA,
    injective_of_finite_padicInt_charZero (p := 3) ιA, hmatch, hflat, hline,
    hunrEll, hunrTransfer⟩
  exact @IsModuleTopology.mk ℤ_[3] _ A _ _ (moduleTopology ℤ_[3] A) rfl

/-- **Brauer descent, `3`-adic side — construction of the raw
realization** (DECOMPOSED 2026-07-24 — now a PROVEN assembly over the
`ℓ`-adic descended system, the Brauer-sum citation sub-leaf
`exists_threeadicBrauerSum_of_witness`, and two formal steps; see the
ASSEMBLY note at the end of this docstring — BLGGT §5.3, the
Brauer-trick
construction): a potential-modularity carrier for the lift `ρ` yields
a `3`-adic realization over `ℚ`. Classically: Brauer's induction
theorem on `Gal(F/ℚ)` (`Wit.galoisF`) writes
`1 = Σ nᵢ · Ind_{Hᵢ}^{Gal(F/ℚ)} χᵢ` with `Hᵢ` solvable and `χᵢ`
one-dimensional; solvable base change (Langlands) descends the
Hilbert newform to each `Fᵢ = F^{Hᵢ}`; the virtual sum
`Σ nᵢ · Ind_{G_{Fᵢ}}^{G_ℚ} (τ_{fᵢ,λ} ⊗ χᵢ)` at the place `λ | 3` of
the Hecke field is a TRUE representation of `G_ℚ` (BLGGT §5.3: the
virtual character is a true character because at the place over `ℓ`
it is the character of `ρ`; Brauer–Nesbitt then pins the semisimple
representation at every `λ`); a stable lattice (finite free over
`ℤ_3` inside the `E_λ`-representation) yields the coefficient package
`A` with its injective continuous embedding `ιA` into `ℚ̄_3`. The
compatibility clause `compat` is Carayol local-global compatibility
at unramified places, transported through the Hecke field exactly as
on the `ℓ`-adic side (`exists_heckeField_system_of_witness`).

Literature: Barnet-Lamb–Gee–Geraghty–Taylor, *Potential automorphy
and change of weight*, Ann. of Math. 179 (2014), §5.3 and Theorem
5.5.1; Khare–Wintenberger, *Serre's modularity conjecture (I)*,
Invent. Math. 178 (2009), §5; Taylor, *Remarks on a conjecture of
Fontaine and Mazur*, J. Inst. Math. Jussieu 1 (2002), §6.

SOUNDNESS AUDIT (both ways, 2026-07-24): (i) direct — for the carrier
produced by the inhabitation leaf this is BLGGT §5.3/§5.5; for an
abstract carrier the abstract-quantification caveat of pillar β
applies, and (ii) collapse — the hypothesis set is classically
unsatisfiable (headline below), so the statement is classically true
for every package.

ASSEMBLY (2026-07-24, PROVEN): the `ℓ`-adic Brauer descent supplies
the rational Hecke system `(S₀, Pv)` interpolating `charFrob ρ`
(`exists_heckeField_system_of_witness`, already a proven assembly over
its own three leaves) + the `3`-adic Brauer sum realizes THAT system
on a stable lattice (`exists_threeadicBrauerSum_of_witness`, itself
PROVEN 2026-07-25 over the geometric core
`blggt_threeadicBrauerSum_of_witness`, which is the single residual
citation sub-leaf of this node — BLGGT §5.3) + two
formal steps: the freeness normalization
`module_free_padicInt_of_algebraMap_injective` (a module-finite
torsion-free algebra over the PID `ℤ_3` is free — this is what turns
the lattice into the `Module.Free ℤ_[3] A` the classification
consumes) and the interpolant transport `heckePoly_transport` (`ψℓ` is
injective on the field `E`, so matching the ONE descended family `Pv`
gives the universally quantified `compat` clause). The exceptional set
of the realization is the union `S₁ ∪ S₀`, so that both matches are
available at every good prime.

LOCAL-SHAPE FIELDS (2026-07-25, the CUT-LEVEL REPAIR; ABSORBED
2026-07-26): the two local-shape components of the interface,
`flatAtThreePow` at `3` and `stableLineAtTwo` at `2`, are supplied HERE.
They used to be condition-transfer leaves quantified over EVERY
realization, in which position they were undischargeable: `compat` pins
`τ` only up to semisimplification, and both local shapes are invisible
to that. A first repair moved them to the construction site as two
dedicated citation leaves; since 2026-07-26 they are instead clauses
(2) and (3) of the existential of `blggt_threeadicBrauerSum_of_witness`
itself, and are consumed here verbatim as `hflat` and `hline`. That
removed two sorries without weakening anything: the citation is the
declaration that chooses `τ`, and BLGGT's compatible systems already
carry crystallinity at the places over the residue characteristic, so
the citation had been under-asserting relative to its own source. This
node stays PROVEN, and its single residual citation is now the Brauer-sum
leaf alone. -/
theorem exists_threeadicRealization_of_witness
    {ℓ : ℕ} (hℓodd : Odd ℓ) [Fact ℓ.Prime] (hℓ5 : 5 ≤ ℓ)
    {O : Type u} [CommRing O] [IsDomain O] [TopologicalSpace O]
    [IsTopologicalRing O] [Algebra ℤ_[ℓ] O] [IsLocalRing O]
    [Module.Finite ℤ_[ℓ] O] [IsModuleTopology ℤ_[ℓ] O]
    (hZinj : Function.Injective (algebraMap ℤ_[ℓ] O))
    {ρ : GaloisRep ℚ O (Fin 2 → O)}
    (hrank : Module.rank O (Fin 2 → O) = 2)
    (hρ : IsHardlyRamified hℓodd hrank ρ)
    {k : Type u} [Field k] [Finite k] [Algebra ℤ_[ℓ] k]
    [TopologicalSpace k] [DiscreteTopology k]
    {W : Type v} [AddCommGroup W] [Module k W] [Module.Finite k W]
    [Module.Free k W]
    (hW : Module.rank k W = 2) {ρbar : GaloisRep ℚ k W}
    (hρbar : IsHardlyRamified hℓodd hW ρbar)
    (hirr : ρbar.IsIrreducible)
    (π : O →+* k) (hπsurj : Function.Surjective π)
    (hπ : ∀ (q : ℕ) (hq : q.Prime), q ≠ 2 → q ≠ ℓ →
      (ρ.charFrob hq.toHeightOneSpectrumRingOfIntegersRat).map π =
        ρbar.charFrob hq.toHeightOneSpectrumRingOfIntegersRat)
    (Wit : PotentialModularityWitness ℓ O ρ) :
    Nonempty (ThreeadicRealization ℓ O ρ Wit) := by
  classical
  -- (i) the `ℓ`-adic Brauer descent: the rational Hecke system
  obtain ⟨S₀, Pv, hPv⟩ :=
    exists_heckeField_system_of_witness hℓodd hℓ5 hZinj hrank hρ hW hρbar
      hirr π hπsurj hπ Wit
  -- (ii) the `3`-adic Brauer sum realizing that same system on a
  -- stable lattice (BLGGT §5.3)
  obtain ⟨S₁, A, hA₁, hA₂, hA₃, hA₄, hA₅, hA₆, hA₇, hA₈, hAinj, τ, ιA,
    hιA, hmatch, hflat, hline, hunrEll, hunrTransfer⟩ :=
    exists_threeadicBrauerSum_of_witness hℓodd hℓ5 hZinj hrank hρ hW
      hρbar hirr π hπsurj hπ Wit S₀ Pv hPv
  -- (iii) freeness normalization of the lattice (formal, `ℤ_3` a PID)
  haveI : Module.Free ℤ_[3] A :=
    module_free_padicInt_of_algebraMap_injective 3 A hAinj
  -- (iv) the compatibility clause, obtained from the single descended
  -- family by interpolant uniqueness (formal, `ψℓ` injective on the
  -- field `E`), with the two exceptional sets united so that both
  -- matches are available at every good prime
  have hcompat : ∀ (q : ℕ) (hq : q.Prime),
      hq.toHeightOneSpectrumRingOfIntegersRat ∉ S₁ ∪ S₀ →
      q ≠ 2 → q ≠ 3 → q ≠ ℓ →
      ∀ P : Polynomial Wit.E,
        (ρ.charFrob hq.toHeightOneSpectrumRingOfIntegersRat).map Wit.ιO =
          P.map Wit.ψℓ →
        (τ.charFrob hq.toHeightOneSpectrumRingOfIntegersRat).map ιA =
          P.map Wit.ψ₃ := by
    intro q hq hqS hq2 hq3 hqℓ P hP
    exact heckePoly_transport Wit.ψℓ Wit.ψ₃
      (hPv q hq (fun h => hqS (Finset.mem_union_right _ h)) hq2 hq3 hqℓ)
      (hmatch q hq (fun h => hqS (Finset.mem_union_left _ h)) hq2 hq3 hqℓ)
      hP
  -- glue: the realization. The two LOCAL-SHAPE fields are the local-shape
  -- clauses of the Brauer-descent citation itself (ABSORBED 2026-07-26 —
  -- see the ABSORPTION note in `blggt_threeadicBrauerSum_of_witness`):
  -- the citation chooses `τ`, so it is the only thing in the tree that
  -- can assert `τ`'s local shape, and BLGGT's own compatible systems
  -- already carry crystallinity at the places over the residue
  -- characteristic. They are not derivable from `compat` (see the
  -- structure's CUT-LEVEL REPAIR paragraph), which is why they are fields
  exact ⟨{ S₁ := S₁ ∪ S₀, A := A, τ := τ, ιA := ιA,
           ιA_injective := hιA, compat := hcompat,
           flatAtThreePow := hflat,
           stableLineAtTwo := hline,
           unramifiedAtEll := hunrEll,
           unramifiedTransfer := hunrTransfer }⟩

/-- **Condition transfer, determinant — cyclotomic across the system**
(PROVEN): the Brauer-descended `3`-adic member has cyclotomic
determinant. Classically: the determinants of a strictly compatible
system form a compatible system of characters; `det ρ` is the
`ℓ`-adic cyclotomic character (`hρ.det`), so the shared Hecke
polynomials have constant coefficient `q` at almost every `q`
(through `compat`, their constant coefficients are the determinants
of Frobenius on both sides); `det τ` — a continuous character of
`G_ℚ` — thus agrees with the `3`-adic cyclotomic character on the
Frobenii of a cofinite set of primes, hence everywhere (Chebotarev
density: the Frobenii off a finite set are dense in the abelianized
absolute Galois group; both characters are continuous).

Literature: Khare–Wintenberger, *Serre's modularity conjecture (I)*,
Invent. Math. 178 (2009), §5 (determinants across the system); BLGGT,
*Potential automorphy and change of weight*, Ann. of Math. 179
(2014), §5.5.

SOUNDNESS AUDIT (both ways, 2026-07-24): (i) direct — for the
realization produced by the construction leaf this is the
strict-compatibility determinant transfer above; for an abstract
realization the abstract-quantification caveat of pillar β applies,
and (ii) collapse — the hypothesis set is classically unsatisfiable
(headline below), so the statement is classically true for every
package.

CIRCULARITY GUARD (inherited from pillar β, load-bearing): no
discharge through `Family.lean`, `Lift.lean`, or
`Modularity/Interface.lean`. Respected by the proof below: its
inputs are the `ℓ`-adic Hecke-field system
(`exists_heckeField_system_of_witness`, this module), the
realization's own `compat` clause, `hρ.det` (the hardly ramified
hypothesis) and `Chebotarev.lean` — no `Family`/`Lift`/`Interface`
route.

PROVEN 2026-07-25 (no residual leaf of its own — the propagation is
fully formalized; no automorphic input is consumed, because the
determinant is pinned on the `ℓ`-adic side by `hρ.det` rather than by
the Hecke eigensystem's central character). ROUTE AUDIT: two routes
were available for pinning the constant coefficients of the shared
Hecke polynomials `Pv q` — (a) the automorphic one, identifying the
central character of the descended Hilbert eigensystem with
`‖·‖·(norm)`, which would need a genuine citation sub-leaf, and (b)
the Galois-side one, reading the constant coefficient off the
`ℓ`-adic member, where `det ρ = χ_ℓ` is HYPOTHESIS (`hρ.det`).
Route (b) is strictly shallower and was taken; route (a) would have
introduced an automorphic citation leaf for no gain.

ASSEMBLY: the `ℓ`-adic system `Pv` (`exists_heckeField_system_of_witness`)
interpolates `charFrob ρ` at every prime `q` outside a finite set;
`charpoly_eq_quadratic_of_finrank_two` reads its constant coefficient
as `det ρ (Frob_q)`, which `hρ.det` and `cyclotomicCharacter_globalFrob`
evaluate to `q`; injectivity of `ψℓ` on the Hecke field `E` forces
`(Pv q).coeff 0 = q` in `E`, and the realization's `compat` clause
plus injectivity of `ιA` transports this to
`det τ (Frob_q) = q = χ_3(Frob_q)` in `A`. Both sides are continuous
and conjugation-invariant, so the agreement set is closed and contains
the dense set of Frobenius conjugates
(`dense_conjClasses_globalFrob`); `A` is Hausdorff (finite free over
`ℤ_3` with the module topology), so the agreement set is everything. -/
theorem threeadicRealization_det_cyclotomic_of_witness
    {ℓ : ℕ} (hℓodd : Odd ℓ) [Fact ℓ.Prime] (hℓ5 : 5 ≤ ℓ)
    {O : Type u} [CommRing O] [IsDomain O] [TopologicalSpace O]
    [IsTopologicalRing O] [Algebra ℤ_[ℓ] O] [IsLocalRing O]
    [Module.Finite ℤ_[ℓ] O] [IsModuleTopology ℤ_[ℓ] O]
    (hZinj : Function.Injective (algebraMap ℤ_[ℓ] O))
    {ρ : GaloisRep ℚ O (Fin 2 → O)}
    (hrank : Module.rank O (Fin 2 → O) = 2)
    (hρ : IsHardlyRamified hℓodd hrank ρ)
    {k : Type u} [Field k] [Finite k] [Algebra ℤ_[ℓ] k]
    [TopologicalSpace k] [DiscreteTopology k]
    {W : Type v} [AddCommGroup W] [Module k W] [Module.Finite k W]
    [Module.Free k W]
    (hW : Module.rank k W = 2) {ρbar : GaloisRep ℚ k W}
    (hρbar : IsHardlyRamified hℓodd hW ρbar)
    (hirr : ρbar.IsIrreducible)
    (π : O →+* k) (hπsurj : Function.Surjective π)
    (hπ : ∀ (q : ℕ) (hq : q.Prime), q ≠ 2 → q ≠ ℓ →
      (ρ.charFrob hq.toHeightOneSpectrumRingOfIntegersRat).map π =
        ρbar.charFrob hq.toHeightOneSpectrumRingOfIntegersRat)
    {Wit : PotentialModularityWitness ℓ O ρ}
    (Rlz : ThreeadicRealization ℓ O ρ Wit) :
    ∀ g : Field.absoluteGaloisGroup ℚ, Rlz.τ.det g =
      algebraMap ℤ_[3] Rlz.A
        (cyclotomicCharacter (AlgebraicClosure ℚ) 3 g.toRingEquiv) := by
  classical
  -- the `ℓ`-adic Hecke-field interpolants of `charFrob ρ`
  obtain ⟨S₀, Pv, hPv⟩ := exists_heckeField_system_of_witness hℓodd hℓ5
    hZinj hrank hρ hW hρbar hirr π hπsurj hπ Wit
  -- ranks of the two representation spaces
  have hfrO : Module.finrank O (Fin 2 → O) = 2 :=
    Module.finrank_eq_of_rank_eq (by exact_mod_cast hrank)
  have hfrA : Module.finrank Rlz.A (Fin 2 → Rlz.A) = 2 := by
    simp
  -- `Rlz.A` is Hausdorff: transport along a `ℤ_3`-basis (linear maps
  -- between module-topology modules are continuous both ways)
  haveI hT2 : T2Space Rlz.A := by
    let bA := Module.Free.chooseBasis ℤ_[3] Rlz.A
    let eA : Rlz.A ≃ₗ[ℤ_[3]] (Module.Free.ChooseBasisIndex ℤ_[3] Rlz.A → ℤ_[3]) :=
      bA.equivFun
    have hc₁ : Continuous eA :=
      IsModuleTopology.continuous_of_linearMap eA.toLinearMap
    have hc₂ : Continuous eA.symm :=
      IsModuleTopology.continuous_of_linearMap eA.symm.toLinearMap
    let hom : Rlz.A ≃ₜ (Module.Free.ChooseBasisIndex ℤ_[3] Rlz.A → ℤ_[3]) :=
      { toEquiv := eA.toEquiv
        continuous_toFun := hc₁
        continuous_invFun := hc₂ }
    exact hom.isEmbedding.t2Space
  -- the finite exceptional set: the two descent sets and the places of
  -- `2`, `3`, `ℓ`
  set S : Finset (HeightOneSpectrum (NumberField.RingOfIntegers ℚ)) :=
    insert (Nat.Prime.toHeightOneSpectrumRingOfIntegersRat Nat.prime_two)
      (insert (Nat.Prime.toHeightOneSpectrumRingOfIntegersRat Nat.prime_three)
        (insert (Nat.Prime.toHeightOneSpectrumRingOfIntegersRat
            (Fact.out : ℓ.Prime))
          (S₀ ∪ Rlz.S₁))) with hSdef
  -- the determinant of `τ` at a good Frobenius is `q`
  have hdetq : ∀ (q : ℕ) (hq : q.Prime),
      Nat.Prime.toHeightOneSpectrumRingOfIntegersRat hq ∉ S →
      Rlz.τ.det (globalFrob
        (Nat.Prime.toHeightOneSpectrumRingOfIntegersRat hq)) = (q : Rlz.A) := by
    intro q hq hvS
    have hq2 : q ≠ 2 := by
      rintro rfl; exact hvS (by rw [hSdef]; exact Finset.mem_insert_self _ _)
    have hq3 : q ≠ 3 := by
      rintro rfl
      exact hvS (by
        rw [hSdef]
        exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
    have hqℓ : q ≠ ℓ := by
      rintro rfl
      exact hvS (by
        rw [hSdef]
        exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
          (Finset.mem_insert_self _ _)))
    have hvS₀ : Nat.Prime.toHeightOneSpectrumRingOfIntegersRat hq ∉ S₀ := by
      intro hmem
      exact hvS (by
        rw [hSdef]
        exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
          (Finset.mem_insert_of_mem (Finset.mem_union_left _ hmem))))
    have hvS₁ : Nat.Prime.toHeightOneSpectrumRingOfIntegersRat hq ∉ Rlz.S₁ := by
      intro hmem
      exact hvS (by
        rw [hSdef]
        exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
          (Finset.mem_insert_of_mem (Finset.mem_union_right _ hmem))))
    -- the `ℓ`-adic interpolation and its `3`-adic transport
    have h1 := hPv q hq hvS₀ hq2 hq3 hqℓ
    have h2 := Rlz.compat q hq hvS₁ hq2 hq3 hqℓ
      (Pv (Nat.Prime.toHeightOneSpectrumRingOfIntegersRat hq)) h1
    -- constant coefficients
    have h1' : Wit.ιO ((ρ.charFrob
          (Nat.Prime.toHeightOneSpectrumRingOfIntegersRat hq)).coeff 0) =
        Wit.ψℓ ((Pv (Nat.Prime.toHeightOneSpectrumRingOfIntegersRat hq)).coeff 0) := by
      have := congrArg (fun p : Polynomial _ => p.coeff 0) h1
      simpa [Polynomial.coeff_map] using this
    have h2' : Rlz.ιA ((Rlz.τ.charFrob
          (Nat.Prime.toHeightOneSpectrumRingOfIntegersRat hq)).coeff 0) =
        Wit.ψ₃ ((Pv (Nat.Prime.toHeightOneSpectrumRingOfIntegersRat hq)).coeff 0) := by
      have := congrArg (fun p : Polynomial _ => p.coeff 0) h2
      simpa [Polynomial.coeff_map] using this
    -- the `ℓ`-adic constant coefficient is `det ρ (Frob_q) = q`
    have hdetρ : (ρ.charFrob
        (Nat.Prime.toHeightOneSpectrumRingOfIntegersRat hq)).coeff 0 = (q : O) := by
      rw [GaloisRep.charFrob_eq_charpoly_globalFrob,
        charpoly_eq_quadratic_of_finrank_two hfrO, coeff_zero_quadratic,
        ← GaloisRep.det_apply, hρ.det, cyclotomicCharacter_globalFrob hq hqℓ,
        map_natCast]
    -- hence the Hecke polynomial's constant coefficient is `q` in `E`
    have hPvq : (Pv (Nat.Prime.toHeightOneSpectrumRingOfIntegersRat hq)).coeff 0
        = (q : Wit.E) := by
      apply Wit.ψℓ.injective
      rw [← h1', hdetρ, map_natCast, map_natCast]
    -- transport to the `3`-adic side
    have hτcoeff : (Rlz.τ.charFrob
        (Nat.Prime.toHeightOneSpectrumRingOfIntegersRat hq)).coeff 0
        = (q : Rlz.A) := by
      apply Rlz.ιA_injective
      rw [h2', hPvq, map_natCast, map_natCast]
    rw [GaloisRep.charFrob_eq_charpoly_globalFrob,
      charpoly_eq_quadratic_of_finrank_two hfrA, coeff_zero_quadratic]
      at hτcoeff
    rw [GaloisRep.det_apply]
    exact hτcoeff
  -- the `3`-adic cyclotomic character at a good Frobenius is `q`
  have hchiq : ∀ (q : ℕ) (hq : q.Prime), q ≠ 3 →
      algebraMap ℤ_[3] Rlz.A ((cyclotomicCharacter (AlgebraicClosure ℚ) 3
        (globalFrob (Nat.Prime.toHeightOneSpectrumRingOfIntegersRat hq)).toRingEquiv :
          ℤ_[3]ˣ) : ℤ_[3]) = (q : Rlz.A) := by
    intro q hq hq3
    rw [cyclotomicCharacter_globalFrob hq hq3, map_natCast]
  -- both sides are continuous
  have hcont1 : Continuous fun g : Field.absoluteGaloisGroup ℚ => Rlz.τ.det g :=
    ContinuousMonoidHom.continuous_toFun _
  have hRA : ∀ g : Field.absoluteGaloisGroup ℚ,
      MulSemiringAction.toRingAut (Field.absoluteGaloisGroup ℚ)
        (AlgebraicClosure ℚ) g = g.toRingEquiv :=
    fun _ => RingEquiv.ext fun _ => rfl
  have hbridge : ∀ g : Field.absoluteGaloisGroup ℚ,
      cyclotomicCharacter (AlgebraicClosure ℚ) 3 g.toRingEquiv =
        ((cyclotomicCharacter (AlgebraicClosure ℚ) 3).comp
          (MulSemiringAction.toRingAut (Field.absoluteGaloisGroup ℚ)
            (AlgebraicClosure ℚ))) g := by
    intro g
    rw [MonoidHom.comp_apply, hRA]
  have hcontχ : Continuous fun g : Field.absoluteGaloisGroup ℚ =>
      ((cyclotomicCharacter (AlgebraicClosure ℚ) 3 g.toRingEquiv : ℤ_[3]ˣ) :
        ℤ_[3]) := by
    simp only [hbridge]
    exact Units.continuous_val.comp
      (cyclotomicCharacter.continuous 3 ℚ (AlgebraicClosure ℚ))
  have hcont2 : Continuous fun g : Field.absoluteGaloisGroup ℚ =>
      algebraMap ℤ_[3] Rlz.A
        ((cyclotomicCharacter (AlgebraicClosure ℚ) 3 g.toRingEquiv : ℤ_[3]ˣ) :
          ℤ_[3]) :=
    (continuous_algebraMap ℤ_[3] Rlz.A).comp hcontχ
  have hclosed : IsClosed {g : Field.absoluteGaloisGroup ℚ |
      Rlz.τ.det g = algebraMap ℤ_[3] Rlz.A
        ((cyclotomicCharacter (AlgebraicClosure ℚ) 3 g.toRingEquiv : ℤ_[3]ˣ) :
          ℤ_[3])} :=
    isClosed_eq hcont1 hcont2
  -- … and the agreement set contains the dense set of Frobenius conjugates
  have hsub : {x : Field.absoluteGaloisGroup ℚ |
      ∃ v : HeightOneSpectrum (NumberField.RingOfIntegers ℚ), v ∉ S ∧
        ∃ g, x = g * globalFrob v * g⁻¹} ⊆
      {g : Field.absoluteGaloisGroup ℚ |
        Rlz.τ.det g = algebraMap ℤ_[3] Rlz.A
          ((cyclotomicCharacter (AlgebraicClosure ℚ) 3 g.toRingEquiv : ℤ_[3]ˣ) :
            ℤ_[3])} := by
    rintro x ⟨v, hvS, g, rfl⟩
    obtain ⟨q, hq, rfl⟩ := exists_prime_toHeightOneSpectrum v
    have hq3 : q ≠ 3 := by
      rintro rfl
      exact hvS (by
        rw [hSdef]
        exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
    -- conjugation invariance of the determinant
    have hdetconj : Rlz.τ.det (g * globalFrob
        (Nat.Prime.toHeightOneSpectrumRingOfIntegersRat hq) * g⁻¹) =
        Rlz.τ.det (globalFrob
          (Nat.Prime.toHeightOneSpectrumRingOfIntegersRat hq)) := by
      have hgg : Rlz.τ.det g * Rlz.τ.det g⁻¹ = 1 := by
        rw [← map_mul, mul_inv_cancel, map_one]
      calc Rlz.τ.det (g * globalFrob
            (Nat.Prime.toHeightOneSpectrumRingOfIntegersRat hq) * g⁻¹)
          = Rlz.τ.det g * Rlz.τ.det (globalFrob
              (Nat.Prime.toHeightOneSpectrumRingOfIntegersRat hq)) *
            Rlz.τ.det g⁻¹ := by rw [map_mul, map_mul]
        _ = Rlz.τ.det (globalFrob
              (Nat.Prime.toHeightOneSpectrumRingOfIntegersRat hq)) *
            (Rlz.τ.det g * Rlz.τ.det g⁻¹) := by ring
        _ = Rlz.τ.det (globalFrob
              (Nat.Prime.toHeightOneSpectrumRingOfIntegersRat hq)) := by
            rw [hgg, mul_one]
    -- conjugation invariance of the cyclotomic character
    have hχconj : cyclotomicCharacter (AlgebraicClosure ℚ) 3
        (g * globalFrob (Nat.Prime.toHeightOneSpectrumRingOfIntegersRat hq) *
          g⁻¹).toRingEquiv =
        cyclotomicCharacter (AlgebraicClosure ℚ) 3 (globalFrob
          (Nat.Prime.toHeightOneSpectrumRingOfIntegersRat hq)).toRingEquiv := by
      rw [hbridge, hbridge, map_mul, map_mul, map_inv, mul_right_comm,
        mul_inv_cancel, one_mul]
    show Rlz.τ.det _ = _
    rw [hdetconj, hχconj, hdetq q hq hvS, hchiq q hq hq3]
  -- density concludes
  intro g
  have hdense := dense_conjClasses_globalFrob (K := ℚ) S
  have hall : (Set.univ : Set (Field.absoluteGaloisGroup ℚ)) ⊆ _ :=
    hdense.closure_eq ▸ hclosed.closure_subset_iff.mpr hsub
  exact hall (Set.mem_univ g)

set_option linter.unusedVariables false in
/-- **The `3`-adic member is unramified at `ℓ`** (PROVEN 2026-07-26 by
the SEAM CHANGE — now a one-line projection of the
`ThreeadicRealization` field `unramifiedAtEll`; previously a CITATION
LEAF split off 2026-07-25 from
`threeadicRealization_ramified_transfer_of_witness` below, whose
`p ≠ ℓ` clause is exactly this statement): the Brauer-descended
`3`-adic member `τ` is unramified at the `ℓ`-adic member's OWN residue
characteristic `ℓ`.

**SEAM CHANGE, 2026-07-26 — READ THIS BEFORE ANY AUDIT BELOW.** Every
ROUTE AUDIT in this docstring is now HISTORICAL, and each of them was
correct: this leaf was INTERFACE-limited, not machinery-limited, and no
leaf-level cut existed. The THIRD CLOSURE below states the resolution
exactly — "the only two closures are (a) a seam change that names it
(below), or (b) breaking the circularity of the collapse half" — and
records that (a) is an ORCHESTRATOR-LEVEL DECISION. That decision was
taken, and closure (a) is what is implemented here.

What changed: `ThreeadicRealization` gained a field `unramifiedAtEll`
carrying exactly this conclusion, discharged at the single construction
site `exists_threeadicRealization_of_witness` out of a new clause (4)
of the construction citation `blggt_threeadicBrauerSum_of_witness`.
This is the THIRD field added to that structure for this reason, after
`flatAtThreePow` and `stableLineAtTwo` (the 2026-07-25 CUT-LEVEL
REPAIR), and it is added for the identical reason: the datum is inertia
data that must be chosen TOGETHER WITH `τ`, and only the citation that
chooses `τ` can assert it.

Why this is not hiding. The two literature inputs the 2026-07-25 split
exists to keep apart are still textually apart: this one is
Fontaine–Laffaille at `ℓ` and is clause (4) of the construction
citation, while the sibling
`threeadicRealization_unramifiedTransfer_of_witness` is Carayol strict
compatibility and is clause (5). Neither was merged into the other, and
each clause carries its own attribution — exactly as clauses (2) and
(3) already do for the two local-shape inputs. The NARROWING AUDIT of
the sibling makes the further point that for clause (5) the change is
outright DEDUPLICATION, the construction citation having under-asserted
relative to BLGGT Theorem 5.5.1, which produces a member of a strictly
compatible system.

What did NOT change: no mathematics, and no literature input was
dropped or weakened. The obligation moved from here to the construction
citation; the frontier shrank by two leaves and gained none.

WHY THIS IS A LEAF OF ITS OWN. This is the FONTAINE–LAFFAILLE input,
and it is a different literature theorem from the member-independence
transfer at a place prime to both residue characteristics
(`threeadicRealization_unramifiedTransfer_of_witness`, immediately
below), which is why the two are now separate citations rather than one
bundled clause. The chain is:

* `ρ` is FLAT at `ℓ` (`hρ.isFlat`) — i.e. crystalline of Hodge–Tate
  weights `{0, 1}` in the weight-`2` normalization;
* by Fontaine–Laffaille (the weight is small relative to `ℓ` — weight
  `2` against `ℓ ≥ 5 > 2` — so the functor is an equivalence and
  flatness IS the integral crystalline condition), that is the local
  condition at `ℓ`
  corresponding to LEVEL PRIME TO `ℓ`: the automorphic local component
  `π_λ` at the places `λ | ℓ` of the Hilbert newform through which the
  descent runs is unramified;
* `ℓ ≠ 3` (indeed `ℓ ≥ 5`), so the place `ℓ` is prime to the residue
  characteristic of the `3`-adic member, and Carayol's local-global
  compatibility applies to `τ` there: `WD_ℓ(τ) ≅ ς(π_ℓ)`, which is
  unramified.

Note that this is the ONLY point in the whole ramification chain at
which `hρ.isFlat` is consumed; the transfer leaf below consumes only
Carayol.

Literature: Fontaine–Laffaille, *Construction de représentations
p-adiques*, Ann. Sci. ÉNS 15 (1982) (flat ⟺ crystalline with
Hodge–Tate weights `{0,1}`, and level prime to `ℓ` in weight `2`);
Carayol, *Sur les représentations `ℓ`-adiques associées aux formes
modulaires de Hilbert*, Ann. Sci. ÉNS 19 (1986), Théorème (A) p. 410
(the local parameter is pinned at every finite place of residue
characteristic different from that of `λ`); BLGGT, *Potential
automorphy and change of weight*, Ann. of Math. 179 (2014), §5.1, §5.5.

ROUTE AUDIT (2026-07-25; the datum inventory CORRECTED 2026-07-26): no
formal route exists in the interface. This audit used to say that the
only arithmetic datum `ThreeadicRealization` carries is `compat`; that
became FALSE with the 2026-07-25 cut-level repair, which added the
local-shape fields `flatAtThreePow` (at `3`) and `stableLineAtTwo` (at
`2`). The route is closed anyway, and for a reason unaffected by the
correction: `ℓ ≥ 5`, so neither local-shape field says anything at `ℓ`,
and the only remaining datum is `compat`, which
equates CHARACTERISTIC POLYNOMIALS OF FROBENIUS at unramified places
away from the finite set `Rlz.S₁`; Frobenius data determines at most
the semisimplification of `τ` and says nothing whatsoever about the
inertia subgroup at `ℓ`. Concretely, the closure-of-Frobenius-classes
argument that PROVES the determinant transfer
(`threeadicRealization_det_cyclotomic_of_witness` above) cannot be
imitated here: it works because `det τ` and the cyclotomic character
take the SAME RATIONAL VALUE `q` at `Frob_q`, i.e. it compares two
continuous functions that are known to agree on a dense set, whereas
`τ|_{I_ℓ} = 1` is not the agreement of two continuous functions known
at Frobenii. So this is cut as a literature joint.

ROUTE AUDIT, SECOND CLOSURE (2026-07-26): the `τF` ROUTE is closed too.
It is the most natural remaining attempt, because the witness ALREADY
carries a `3`-adic member — `Wit.τF`, the `3`-adic realization over `F`
of the same eigensystem — and the Fontaine–Laffaille input really IS
expressible on it with existing vocabulary, namely
`∀ w, (ℓ : 𝓞 F) ∈ w.asIdeal → Wit.τF.IsUnramifiedAt w`, which is what
"level prime to `ℓ`" amounts to once Carayol is applied over `F` at a
place prime to `3`. It nonetheless does not reach `Rlz.τ`, for two
INDEPENDENT reasons, either of which alone is fatal:

* the interface nowhere relates `Rlz.τ|_{G_F}` to `Wit.τF`. The only
  link between them is again Frobenius data — `Rlz.compat` and
  `Wit.matchF₃` both factor through the same Hecke polynomials — so the
  semisimplification obstruction recorded above applies verbatim, one
  level down; and
* even GRANTING `Rlz.τ|_{G_F} ≅ Wit.τF`, unramifiedness at the places
  `w | ℓ` of `F` gives only `I_w ≤ ker`, whereas the conclusion here is
  `I_ℓ ≤ ker` over `ℚ`; and `I_w ⊊ I_ℓ` unless `ℓ` is UNRAMIFIED in `F`,
  which `PotentialModularityWitness` does not record (it carries only
  `totallyReal` and `galoisF`) and which Moret–Bailly does not supply,
  since `F` is chosen to kill local obstructions, not to be unramified.

STRUCTURAL OPTION, EVALUATED (2026-07-26 — REJECTED AS A CLOSURE, and
recorded so it is costed rather than rediscovered). The move flagged at
the cut as most promising, "record level prime to `ℓ` in
`PotentialModularityWitness`", is expressible (as the `τF` clause of the
first bullet) and would be a genuine relocation of the
Fontaine–Laffaille citation into the interface, where every other cited
classical assertion of the witness already lives. But by the two bullets
above it does NOT discharge this leaf: the residue is the descent step
over `ℚ`, which is a citation of the same size as the whole. It would
therefore turn one leaf into two without closing either, and is not
taken.

ROUTE AUDIT, THIRD CLOSURE — THE SEAM CHANGE IS COSTED AND REFUTED
(2026-07-26). The one repair the second closure appears to leave open is:
add "`ℓ` is unramified in `F`" to `PotentialModularityWitness` (thereby
killing the second bullet), and state Fontaine–Laffaille about
`Rlz.τ.map (algebraMap ℚ Wit.F)` rather than `Wit.τF` (thereby killing the
first, since no `τF` occurs). It was proposed as a four-declaration seam
change. Both halves fail, for independent and now-explicit reasons.

* **The narrowing is EMPTY — a DICHOTOMY, not a matter of degree.** Write
  `w | ℓ` for a place of `F` and identify `Γ_{F_w} ≤ Γ_{ℚ_ℓ}`. Then
  `I_w = I_ℓ ∩ Γ_{F_w}`, and `F_w/ℚ_ℓ` is unramified exactly when
  `I_ℓ ≤ Γ_{F_w}` (an unramified `F_w` lies in `ℚ_ℓ^{nr}`, whose Galois
  group is `Γ_{ℚ_ℓ}/I_ℓ`). Hence:

  - WITH the new hypothesis, `I_w = I_ℓ` **on the nose**, and since
    `(Rlz.τ.map (algebraMap ℚ F)).toLocal w` is `Rlz.τ.toLocal v_ℓ`
    precomposed with `Γ_{F_w} ↪ Γ_{ℚ_ℓ}`, the `F`-form is *literally the
    same condition* as this leaf. Nothing is narrowed; the citation is
    only moved.
  - WITHOUT it, `I_w ⊊ I_ℓ` and the `F`-form is strictly weaker, so it
    does not discharge this leaf at all (this is the second bullet above).

  There is no third case, so no amount of restating along the `F`-axis can
  produce a leaf that is both implied-by-the-literature and strictly
  weaker than this one. So the seam change trades one citation for one
  citation PLUS one formal lemma that does not exist — see next.

* **THE ONE MISSING LEMMA, NAMED (and the surrounding dictionary is
  already built — do not rebuild it).** The formal residue of the
  "equivalent" branch is inertia LIFTING along an unramified local
  extension. Everything around it is in the tree already:

  - `IsDedekindDomain.HeightOneSpectrum.adicCompletionMap`
    (`CompletionTransport.lean:208`) is the canonical `φ : K_v →+* L_w`
    for `w | v`, built from `WithVal.uniformContinuous_map_of_le` and
    `valuation_map_le_of_le_one`, with `adicCompletionMap_coe`,
    `adicCompletionMap_continuous` and `adicCompletionMap_mem_integers`;
  - `Field.absoluteGaloisGroup.map_mem_localInertiaGroup`
    (`CompletionTransport.lean:386`) is the PUSH-DOWN direction:
    `Field.absoluteGaloisGroup.map φ` carries `localInertiaGroup w` into
    `localInertiaGroup v`;
  - `Field.absoluteGaloisGroup.exists_conj_map_comp'` supplies the single
    conjugator relating `τ.toLocal v ∘ map φ` to
    `(τ.map (algebraMap ℚ F)).toLocal w`, exactly as
    `GaloisRep.exists_finset_isUnramifiedAt_map`
    (`GaloisRepTransport.lean`) already does for the away-from-`S` case.

  What is absent is the ONTO half — `localInertiaGroup v ≤ Subgroup.map
  (Field.absoluteGaloisGroup.map φ).toMonoidHom (localInertiaGroup w)`
  when `w/v` is unramified (`e = 1`, i.e. `𝔪_v · 𝒪_w = 𝔪_w`) — whose
  classical proof is "an unramified `L_w` lies in `K_v^{nr}`, which every
  element of `I_v` fixes". The tree has only the restriction direction
  (`restrictNormalHom_mem_inertia_of_mem_localInertiaGroup`,
  `Threeadic.lean:4598`) and this push-down. That lemma is well-posed,
  self-contained and reusable — the sibling
  `threeadicRealization_unramifiedTransfer_of_witness` needs the same
  `I_p = I_w` identification at every `p` unramified in `F` — and it is
  the honest dispatchable task on this axis. It does NOT, however, close
  this leaf: by the previous bullet it only re-expresses it.

* **The hypothesis is classically free but NOT free to record**, and this
  was the load-bearing mis-estimate in the proposal. It is not addable at
  `exists_moretBailly_seed_of_five_le`: that theorem is a PROVEN assembly,
  as are `exists_hilbertBlumenthalPoint_of_five_le`,
  `exists_totallyReal_point_of_geometricallyIrreducible` and its affine
  form, so the unramifiedness must be PRODUCED by the Moret–Bailly stack,
  not asserted above it. That stack already has the right vocabulary —
  `IsTotallySplitAt`, and `exists_totallySplitPoint_of_affine_curve`
  already takes a finite set `S` of primes with `ℚ_p`-points and returns
  complete splitting at every `p ∈ S` — but the datum is CUT OFF one rung
  higher: `exists_normalRealPoint_of_affine_curve` feeds it only the
  Chebotarev auxiliary primes chosen ABOVE the Weil–Hensel bound `B` of
  `exists_bound_forall_padicPoint_of_geometricallyIrreducible`, and the
  fixed prime `ℓ` need not exceed `B`. Threading `ℓ` in needs a
  `ℚ_ℓ`-point of the moduli space carried down to the curve, i.e.

  - a `p`-adic approximation-ball leaf beside the real one inside
    `exists_bertiniHyperplane_of_affine_geometricallyIrreducible` (PROVEN,
    over `exists_realApproximationBall_of_affine_geometricallyIrreducible`
    and `exists_rat_mem_box_eval_ne_zero`; the rational hyperplane
    parameter would have to meet the real box AND finitely many `p`-adic
    balls — weak approximation), threaded through
    `exists_dimensionDrop_…` and `exists_affineCurve_…`; and
  - a COMMON AFFINE OPEN for the real and the `ℓ`-adic point inside
    `exists_totallyReal_point_of_geometricallyIrreducible`, whose current
    `exists_isAffineOpen_hasRationalPoint` handles one point only. The
    naive many-point form is **FALSE** for a general separated smooth
    finite-type scheme; it needs quasi-projectivity of the twisted
    Hilbert–Blumenthal moduli scheme, which
    `exists_twistedHilbertBlumenthalModuliScheme_of_five_le` does not
    record.

  So the "four-declaration seam change" is a nine-declaration change
  across the Moret–Bailly stack plus two new geometric leaves, and by the
  first bullet it buys no narrowing at the far end. It is NOT taken.

What WOULD close this leaf is a strictly larger seam change, namely
giving `ThreeadicRealization` a `level` field carrying exactly the two
clauses of `exists_conductor_threeadicRealization_of_witness` below.
PRECEDENT: the reference project `~/cs/FLT` avoids leaves of this shape
in precisely that way — its automorphy predicate
`GaloisRep.IsAutomorphicOfLevel p hp hV S`
(`FLT/GaloisRepresentation/Automorphic.lean`) asserts `ρ.IsUnramifiedAt v`
for every `v ∉ S` with `v ∤ p` AS PART OF ITS DEFINITION, so the analogue
of this leaf is definitional there. The cost is that this leaf, its
sibling and the conductor node all collapse into the construction leaf
`exists_threeadicRealization_of_witness`, hiding two distinct literature
inputs inside one citation.

CORRECTION (2026-07-27). This paragraph used to continue "…and the
predicate itself is NOT vendorable, being defined over that project's
quaternionic Hecke-algebra development, which our pin does not have."
**That is false: it IS vendorable, and it HAS been vendored.** The
development's whole import closure now lives under
`Fermat/FLT/{AutomorphicForm,QuaternionAlgebra,DivisionAlgebra,HaarMeasure,
NumberField,DedekindDomain,Hacks,Mathlib}/…` and builds green against our
pin, at a cost of one sorried leaf (`isFiniteRelIndex_Δ`). See the REFUTED
block earlier in this file (search `It IS vendorable`) for the full
accounting. So unvendorability is NOT a reason to prefer the seam change
described above; the remaining argument for it is only the one given in
the sentence before this correction.

MACHINERY AUDIT (2026-07-26, hard search of BOTH libraries — recorded so
this leaf is not re-scoped as single-agent work). Restating it over a
Weil–Deligne formalism is not a shortcut: NOTHING in the prerequisite
chain exists in the pin or in the reference project.

* `grep -rl 'WeilDeligne|weilGroup|WeilGroup'` over all of `Mathlib/`
  and over `~/cs/FLT/FLT` returns EMPTY. There is no Weil group, hence
  no `WD_v(−)` functor to restate anything over.
* Mathlib's entire ramification-group development is
  `Mathlib/RingTheory/Valuation/RamificationGroup.lean` — 54 lines,
  carrying `decompositionSubgroup` and `inertiaSubgroup` and the comment
  `TODO: Define higher ramification groups in lower numbering`. So there
  is no wild/tame filtration, no tame quotient, and no `ℓ`-adic tame
  character `t_ℓ : I_p ↠ ℤ_ℓ(1)` — the three inputs from which
  Grothendieck's local monodromy theorem is built.
* There is no local class field theory and no smooth or admissible
  representations of `GL₂` of a `p`-adic field (`grep
  'SmoothRep|AdmissibleRep|LocalLanglands'` over `Mathlib/` is empty).
* Fontaine theory is present but far too early to help: `Mathlib/`
  `RingTheory/Perfectoid/` has `FontaineTheta.lean`, `Untilt.lean` and
  `BDeRham.lean` (`𝔹_dR⁺`, `𝔹_dR`, whose own TODO list still contains
  "show `𝔹_dR⁺` is a discrete valuation ring"), and NOTHING for
  `𝔹_cris`, crystalline or semistable representations, Hodge–Tate
  weights, or the Fontaine–Laffaille functor (`grep
  'BCris|B_cris|crystallineRep|HodgeTate'` and `grep 'semistable
  representation'` over `Mathlib/` are both empty). So the flatness side
  of the chain has no library statement to be restated over either.

The honest prerequisite chain for a formal `WD_ℓ(−)` is therefore
higher ramification groups → tame quotient → tame character → local
monodromy → Weil group → Weil–Deligne representations. That is a
multi-agent theory-building programme, not a leaf.

MACHINERY AUDIT RE-VERIFIED MECHANICALLY (2026-07-26, a later owner;
recorded so the sweep is not run a third time). Every absence claim of
the MACHINERY AUDIT above was re-run against the CURRENT pin rather
than taken on trust, and all of them still hold:

* `WeilDeligne|weilGroup|WeilGroup` — no file matches, in `Mathlib/` OR
  in `~/cs/FLT/FLT`. Confirmed empty in both trees;
* `Mathlib/RingTheory/Valuation/RamificationGroup.lean` is still
  **exactly 54 lines**, with the `TODO: Define higher ramification
  groups in lower numbering` on line 16 and `decompositionSubgroup` /
  `inertiaSubgroup` its only content;
* `SmoothRep|AdmissibleRep|LocalLanglands` — no matches in `Mathlib/`;
* `BCris|B_cris|crystallineRep|HodgeTate` — no matches in `Mathlib/`;
  `RingTheory/Perfectoid/` still contains exactly `BDeRham.lean`,
  `FontaineTheta.lean`, `Untilt.lean` and nothing else;
* Hilbert modular forms / Shimura curves — no matches (the single
  `shimura` hit anywhere in `Mathlib/` is a prose mention inside
  `NumberTheory/HeckeRing/Defs.lean`, not a development).

THE "ONE MISSING LEMMA" IS STILL MISSING — re-checked directly, because
it is the one claim above that an in-tree lemma could plausibly have
falsified since it was written. Every declaration in the tree mentioning
`localInertiaGroup` was enumerated and classified; none supplies the ONTO
half. The two that come closest, and why neither is it:

* `exists_mem_localInertiaGroup_restrictNormalHom_eq`
  (`LocalInertiaFixedField.lean:1450`) lifts an inertia element from a
  finite Galois LEVEL `N` to the full local inertia group **at the same
  place `v`** (the profinite half of Neukirch II.9.11). That is a
  VERTICAL lift inside one completion, not the HORIZONTAL `w → v` lift
  between two different fields' completions that is wanted here;
* `Field.absoluteGaloisGroup.exists_finset_conj_localInertiaGroup_le`
  (`GaloisRepTransport.lean:611`) is the push-down direction again —
  `I_w` lands in a CONJUGATE of `I_v`, for all but finitely many `w`.

So the audit's verdict stands verbatim and the gap is real. Also note
`restrictNormalHom_mem_inertia_of_mem_localInertiaGroup` has drifted to
`Threeadic.lean:5212` (cited as `:4598` above); locate it by name.

ROUTE AUDIT, THIRD CLOSURE (2026-07-26, 07:53 — **SUPERSEDED AT 09:17
THE SAME DAY; READ THE REFUTATION ABOVE BEFORE ACTING ON ANY OF THIS**):
the `τF`-FREE variant of the relocation is closed too — and by a
DIFFERENT obstruction from the second closure's.

**SUPERSESSION NOTICE (2026-07-26, third owner of this leaf).** The
paragraph below ending "the four-declaration interface repair above" has
been read as a WORK ORDER, and has now generated at least one dispatch at
this leaf on that basis. It is not a work order. The audit titled *THE
SEAM CHANGE IS COSTED AND REFUTED* above (commit `4947248b`, 09:17) was
written 84 minutes AFTER this closure (commit `168afa7f`, 07:53) and
refutes exactly the repair this closure proposes, on two independent
grounds: the narrowing is EMPTY (the `I_w = I_ℓ` dichotomy), and the
datum is not addable where this closure says it is. Both grounds were
re-verified independently by a third owner; see the COST RE-DERIVATION at
the end of this closure, which also corrects the four-declaration
estimate below and makes the eventual repair cheaper than either audit
says. Nothing in this closure is dispatchable as a leaf-level task.

State the Fontaine–Laffaille input directly about `Rlz.τ` restricted to
`G_F`, never mentioning `Wit.τF` at all:

    ∀ w, (ℓ : 𝓞 Wit.F) ∈ w.asIdeal →
      (Rlz.τ.map (algebraMap ℚ Wit.F)).IsUnramifiedAt w

Since `I_w ≤ I_ℓ`, this is strictly weaker than the conclusion here, so
it is a genuine narrowing; and bullet ONE of the second closure — that
nothing in the interface relates `Rlz.τ|_{G_F}` to `Wit.τF` — EVAPORATES,
because `Wit.τF` no longer occurs. What survives is bullet TWO alone: the
residue is the descent `I_w ≤ ker ⟹ I_ℓ ≤ ker`, valid exactly when `ℓ`
is UNRAMIFIED in `F`.

So the leaf reduces to Fontaine–Laffaille over `F` plus ONE arithmetic
datum about the auxiliary field. That datum is classically free — Taylor's
potential modularity chooses `F` linearly disjoint from `ℚ(ζ_ℓ)` and
unramified at `ℓ`, and it must, since otherwise the modularity lifting
theorem over `F` has no Fontaine–Laffaille local condition at `ℓ` to lift
with — but it is recorded NOWHERE in this module, and its honest home is
four levels up: `F` enters through `exists_moretBailly_seed_of_five_le`,
so the clause has to be added to that theorem's conclusion, threaded
through `exists_potentialModularityWitness_of_five_le`, and stored as a
field of `PotentialModularityWitness` beside `totallyReal` and `galoisF`.

Why this is a CLOSURE and not a plan for THIS leaf: writing the descent as
a sorried step inside this proof introduces a step that is not merely
unproven but FALSE for an abstract witness — "for every
potential-modularity witness, `ℓ` is unramified in `F`" is an assertion
about a bare field with no representation in it, refuted by any witness
whose `F` ramifies at `ℓ`. EVERY decomposition of this leaf through
`Wit.F` has that shape. The abstract-quantification caveat of pillar β
covers it formally, but a step of that shape is strictly worse than the
present single citation. The split becomes correct only TOGETHER with the
four-declaration interface repair above, which is a cut-level task and not
a leaf.

Second half of the descent, costed, so the repair is not underestimated:
even with the datum in hand the descent is not free. It needs `F_w/ℚ_ℓ`
unramified ⟹ `I_ℓ ≤ range (Field.absoluteGaloisGroup.map φ)` together
with surjectivity of `I_w → I_ℓ` — local-field inertia theory the pin does
not have. The nearest in-tree machinery,
`restrictNormalHom_mem_inertia_of_mem_localInertiaGroup`
(`HardlyRamified/Threeadic.lean`, ~100 lines of instance plumbing), goes
the OTHER way: it RESTRICTS inertia downwards, and what is needed here is
lifting it upwards.

COST RE-DERIVATION AND SHARPENING (2026-07-26, third owner; an
independent re-trace of the Moret–Bailly stack, recorded because it both
CONFIRMS the 09:17 refutation and makes the eventual repair materially
cheaper than either audit above estimates).

*Confirming the refutation.* `F` is produced by a chain of PROVEN
assemblies — `exists_moretBailly_seed_of_five_le` →
`exists_hilbertBlumenthalPoint_of_five_le` →
`exists_totallyReal_point_of_geometricallyIrreducible` → … →
`exists_normalRealPoint_of_affine_curve` — bottoming out at the sorried
geometric leaf `exists_totallySplitPoint_of_affine_curve`. A clause added
to the conclusion of `exists_moretBailly_seed_of_five_le` therefore
breaks its proof and has to be threaded down all six rungs; it cannot be
asserted there. That is precisely the 09:17 audit's claim, and it holds
as written. "Four declarations" undercounts by about a factor of two
before the new geometric leaves are counted at all.

*The sharpening: record TOTAL SPLITTING, not unramifiedness.* Both audits
frame the datum as "`ℓ` is unramified in `F`". That is the wrong formal
choice in this pin, and choosing it is what makes the descent look
expensive. Record `IsTotallySplitAt F ℓ` instead:

- it is ALREADY the vocabulary the stack produces —
  `exists_totallySplitPoint_of_affine_curve` returns exactly
  `∀ p ∈ S, IsTotallySplitAt F p` — so no new definition and no new
  threading vocabulary is introduced anywhere;
- it needs no contact with mathlib's ramification theory, which is
  `RingTheory/Valuation/RamificationGroup.lean`: 54 lines ending in a
  TODO. `IsTotallySplitAt` is `Nat.card (F →+* ℚ_[p]) = finrank ℚ F`,
  which is stateable today, whereas "`ℓ` is unramified in `F`" has no
  clean statement against that file; and
- **it deletes the "second half of the descent" above entirely.** Totally
  split at `ℓ` means `F_w = ℚ_ℓ` for every `w | ℓ`, hence
  `Γ_{F_w} = Γ_{ℚ_ℓ}` and `I_w = I_ℓ` by EQUALITY OF THE COMPLETIONS — no
  inertia lifting, no `I_ℓ ≤ range (Field.absoluteGaloisGroup.map φ)`, no
  surjectivity of `I_w → I_ℓ`. The paragraph above costs a lemma that the
  merely-unramified formulation needs and the totally-split formulation
  does not. Both formulations yield `I_w = I_ℓ` — that is the 09:17
  dichotomy — and they differ only in what it costs to PROVE it here; the
  gap between them is the whole of local-field inertia theory.

  This is also the faithful reading of the source. Taylor's argument does
  not choose `F` unramified at `ℓ` and hope; it prescribes the
  `ℚ_ℓ`-point of the moduli space corresponding to the given flat local
  deformation, which is exactly what makes `F ⊗ ℚ_ℓ ≅ ℚ_ℓ^{[F:ℚ]}` and
  makes `ρ|_{G_F}` at the places over `ℓ` literally `ρ|_{G_{ℚ_ℓ}}`.

*What survives, and why it is STILL NOT TAKEN.* The residue is the single
input the 09:17 audit isolated: `ℓ` may be added to the Chebotarev set
`S` only against `HasRationalPoint fC (ULift ℚ_[ℓ])` for the Bertini
curve `C`, and `S` is currently populated only with primes ABOVE the
Weil–Hensel bound `B` of
`exists_bound_forall_padicPoint_of_geometricallyIrreducible`, which `ℓ`
need not exceed. Supplying it needs a new conclusion
`HasRationalPoint fX (ULift ℚ_[ℓ])` on
`exists_twistedHilbertBlumenthalModuli_of_five_le` — classically true, it
is the flat deformation point, but a NEW citation — plus preservation of
that point through Bertini and the dimension drop, i.e. the `p`-adic
approximation-ball leaf named above. So the sharpened repair is still two
new leaves plus six rungs of threading, bought in exchange for a leaf
that by the dichotomy is LITERALLY THE SAME CONDITION restated over `F`.
The refutation stands. NOT TAKEN.

A caution for whoever eventually does take it, since it was nearly
recorded here as fact and is not: it is tempting to "prove" the datum
unobtainable by exhibiting a geometrically irreducible affine `ℚ`-curve
with a real point and `ℚ_p`-points beyond `B`, all of whose number-field
points ramify at `ℓ`. No such counterexample was found, and the obvious
candidates all fail (conics of the shape `y² = ℓ(x²+1)` absorb the
constant into `x²+1` and in fact carry a `ℚ`-point, e.g. `(2, 5)` at
`ℓ = 5`). The obstruction here is that the datum is NOT ASSERTED by the
current leaf and must be produced — not that it is false.

REFERENCE-PROJECT AUDIT, CORRECTED (2026-07-26, read at `~/cs/FLT`
directly). The PRECEDENT note above is imprecise in a way that matters.
`GaloisRep.IsAutomorphicOfLevel` asserts `ρ.IsUnramifiedAt v` only for
`v ∤ p` AND `v ∉ S`; at the member's OWN residue characteristic it asserts
nothing, so it is NOT the analogue of this leaf. The true analogue there
is `IsHardlyRamified.isUnramified` — unramified at every `p ∉ {2, ℓ}` —
asserted for EVERY member of the compatible family by `mem_isCompatible`
(`FLT/GaloisRepresentation/HardlyRamified/Family.lean`), which is itself a
single `sorry`. So the reference project does not discharge this content
either: it packages it one level up, in a seam whose shape is "the
`3`-adic member is itself HARDLY RAMIFIED", not "the realization carries a
level". That packaging subsumes this leaf, its sibling AND the conductor
node at once — and it is precisely what `exists_threeadic_member_of_witness`
below already assembles, which is why the packaging is available to us as a
relocation only, never as a shortcut. `IsAutomorphicOfLevel` is also not
vendorable, as recorded: it is defined over that project's `HeckeAlgebra`
for a totally definite quaternion algebra, which our pin lacks.

LOAD-BEARING AUDIT (2026-07-26): re-confirmed that the leaf can be neither
dropped nor narrowed away from `ℓ`. Its consumer chain ends at
`exists_threeadic_member_of_witness`, whose `isUnramified` component is
`IsHardlyRamified`'s and is quantified over EVERY prime `p ∉ {2, 3}`. The
sibling transfer leaf covers exactly `p ∉ {2, 3, ℓ}` — it consumes
`hρ.isUnramified`, which is silent at `ℓ` — so `p = ℓ` is precisely and
only what this leaf supplies.

SOUNDNESS AUDIT (both ways, 2026-07-25): (i) direct — for the
realization produced by the construction leaf this is the
Fontaine–Laffaille/Carayol chain above, applied to the descended
eigensystem; for an abstract realization the abstract-quantification
caveat of pillar β applies, and (ii) collapse — the hypothesis set is
classically unsatisfiable (headline at the end of this module), so the
statement is classically true for every package.

CIRCULARITY GUARD (inherited from pillar β, load-bearing): no
discharge through `Family.lean`, `Lift.lean`, or
`Modularity/Interface.lean`. -/
theorem threeadicRealization_isUnramifiedAtEll_of_witness
    {ℓ : ℕ} (hℓodd : Odd ℓ) [Fact ℓ.Prime] (hℓ5 : 5 ≤ ℓ)
    {O : Type u} [CommRing O] [IsDomain O] [TopologicalSpace O]
    [IsTopologicalRing O] [Algebra ℤ_[ℓ] O] [IsLocalRing O]
    [Module.Finite ℤ_[ℓ] O] [IsModuleTopology ℤ_[ℓ] O]
    (hZinj : Function.Injective (algebraMap ℤ_[ℓ] O))
    {ρ : GaloisRep ℚ O (Fin 2 → O)}
    (hrank : Module.rank O (Fin 2 → O) = 2)
    (hρ : IsHardlyRamified hℓodd hrank ρ)
    {k : Type u} [Field k] [Finite k] [Algebra ℤ_[ℓ] k]
    [TopologicalSpace k] [DiscreteTopology k]
    {W : Type v} [AddCommGroup W] [Module k W] [Module.Finite k W]
    [Module.Free k W]
    (hW : Module.rank k W = 2) {ρbar : GaloisRep ℚ k W}
    (hρbar : IsHardlyRamified hℓodd hW ρbar)
    (hirr : ρbar.IsIrreducible)
    (π : O →+* k) (hπsurj : Function.Surjective π)
    (hπ : ∀ (q : ℕ) (hq : q.Prime), q ≠ 2 → q ≠ ℓ →
      (ρ.charFrob hq.toHeightOneSpectrumRingOfIntegersRat).map π =
        ρbar.charFrob hq.toHeightOneSpectrumRingOfIntegersRat)
    {Wit : PotentialModularityWitness ℓ O ρ}
    (Rlz : ThreeadicRealization ℓ O ρ Wit) :
    Rlz.τ.IsUnramifiedAt
      (Nat.Prime.toHeightOneSpectrumRingOfIntegersRat (Fact.out : ℓ.Prime)) :=
  Rlz.unramifiedAtEll

set_option linter.unusedVariables false in
/-- **Member-independence of the ramification locus at a place prime to
BOTH residue characteristics** (PROVEN 2026-07-26 by the SEAM CHANGE —
now a one-line projection of the `ThreeadicRealization` field
`unramifiedTransfer`; previously a CITATION LEAF split off
2026-07-25 from `threeadicRealization_ramified_transfer_of_witness`
below, whose `¬ ρ.IsUnramifiedAt` clause is the contrapositive of this
statement): at a prime `p ∉ {3, ℓ}` at which the `ℓ`-adic member `ρ`
is UNRAMIFIED, the Brauer-descended `3`-adic member `τ` is unramified
too.

**SEAM CHANGE, 2026-07-26 — READ THIS BEFORE ANY AUDIT BELOW.** Every
ROUTE AUDIT in this docstring is now HISTORICAL, and each was correct:
no leaf-level cut existed, the obstruction was the INTERFACE, and the
NARROWING AUDIT below costed this exact repair as *the seam change*,
flagging it an ORCHESTRATOR-LEVEL DECISION. That decision was taken.

`ThreeadicRealization` gained a field `unramifiedTransfer` carrying
exactly this conclusion, discharged at the single construction site
`exists_threeadicRealization_of_witness` out of a new clause (5) of the
construction citation `blggt_threeadicBrauerSum_of_witness`. As the
NARROWING AUDIT below argues, for THIS clause the change is
DEDUPLICATION rather than hiding: `blggt_threeadicBrauerSum_of_witness`
already cites BLGGT §5.3 / Theorem 5.5.1, that theorem produces a
member of a STRICTLY compatible system and so already asserts the local
parameters at every `p ∤ 3`, and the construction leaf was therefore
under-asserting relative to its own source while this leaf paid for the
difference by citing the same theorem a second time. That second
citation is now gone.

The audit's stated objection to the seam change — that it "hides two
distinct literature inputs inside one citation" — was answered rather
than overridden: the Fontaine–Laffaille input at `ℓ` is clause (4) and
the Carayol input here is clause (5), two separate clauses with
separate attributions, exactly as clauses (2) and (3) already keep the
two local-shape inputs apart. The 2026-07-25 split is preserved; only
its location moved. The EQUIVALENCE NOTE below still stands and is
untouched: this leaf and its sibling were NOT collapsed into each
other, nor back into `exists_conductor_threeadicRealization_of_witness`.

This is Carayol's member-independence in its bare local form: it is
purely LOCAL (one prime at a time), carries no existential, no
finiteness-of-ramification bookkeeping, and no input at the two residue
characteristics `3` and `ℓ` — the place `ℓ` is handled by the separate
Fontaine–Laffaille leaf
`threeadicRealization_isUnramifiedAtEll_of_witness` above, and nothing
whatever is asserted at `p = 3` (where the flatness node
`threeadicRealization_isFlat_of_witness` carries the local condition
instead).

WHY THIS IS THE CITATION. Strict compatibility of the system through
which the descent runs says that a single Weil–Deligne representation
`WD_p(R)` over the coefficient field reproduces
`WD(r_λ|_{G_{ℚ_p}})^{F-ss}` for every `λ` whose residue characteristic
differs from `p` (BLGGT §5.1, the display
`ς WD_p(R) ≅ WD(r_λ|G_{ℚ_p})^{F-ss}`). Here `p ∉ {3, ℓ}`, so BOTH
`λ | ℓ` (the member `ρ`) and `λ | 3` (the member `τ`) are legitimate,
and the two local parameters are isomorphic; an unramified
Weil–Deligne parameter on one member is therefore unramified on the
other. Carayol's theorem for Hilbert newforms is what pins the local
constituent at EVERY finite place of residue characteristic `≠ λ`, not
merely almost all.

DIRECTION AUDIT: Carayol gives the parameters isomorphic, hence the
IFF; only the direction the consumer needs is stated here, which is the
weaker assertion. The reverse direction (`τ` unramified ⟹ `ρ`
unramified) is nowhere used in this module and is deliberately not
claimed.

Literature: Carayol, *Sur les représentations `ℓ`-adiques associées aux
formes modulaires de Hilbert*, Ann. Sci. ÉNS 19 (1986), Théorème (A)
p. 410; Khare–Wintenberger, *Serre's modularity conjecture (I)*,
Invent. Math. 178 (2009), §5 (strict compatibility away from the
residue characteristic); BLGGT, *Potential automorphy and change of
weight*, Ann. of Math. 179 (2014), §5.1 and Theorem 5.5.1.

ROUTE AUDIT (2026-07-25, re-checked at the split): the *charFrob cut*
out of `Rlz.compat` is again rejected — `compat` equates
characteristic polynomials of Frobenius at unramified places away from
the finite set `Rlz.S₁` and therefore carries no inertia information
whatsoever. (CORRECTED 2026-07-26: this audit used to add "and
`ThreeadicRealization` carries no other arithmetic datum", which has been
FALSE since the 2026-07-25 cut-level repair gave the structure the two
local-shape fields `flatAtThreePow` and `stableLineAtTwo`. The rejection
stands regardless, and is now the sharper claim: those two fields are
local data at `3` and at `2` respectively, so neither says anything about
inertia at a prime `p ∉ {2, 3}`, which is what this node needs.) Sharper
form of the same objection, recorded here so it is not
re-litigated: Frobenius data pins at most the SEMISIMPLIFICATION of
`τ`, and semisimplification destroys exactly the information at stake —
over `ℚ` the extensions of `1` by the `3`-adic cyclotomic character are
classified by `H¹(G_ℚ, ℤ_3(1))`, i.e. by the `3`-adic completion of
`ℚ^×` (Kummer theory), and a class whose valuation at `p` is nonzero is
RAMIFIED at `p` while having, at every prime, the same characteristic
polynomial of Frobenius as the split extension (any lift of Frobenius
acts by an upper-triangular matrix with the same diagonal). So no
formal route to an inertia statement exists in the
interface, which is why this is cut as a literature joint.

ROUTE AUDIT, SECOND CLOSURE (2026-07-26): the PIECEWISE ROUTE — prove
the transfer on the Brauer pieces and induce — is UNSOUND, and is
recorded here because the interface's `Wit.τF` invites it. Write, as
classically one does, `τ ~ Σ nᵢ · Ind_{G_{Fᵢ}}^{G_ℚ}(τ_{fᵢ} ⊗ χᵢ)` with
`Fᵢ = F^{Hᵢ}` the fixed fields of the Brauer subgroups. Neither half of
the piecewise argument survives:

* solvable base change does NOT preserve unramifiedness downwards. A
  local component that is a RAMIFIED principal series `π(χ, χ⁻¹)` over
  `Fᵢ` becomes UNRAMIFIED after base change to `F` (the ramified
  character becomes unramified over the extension it cuts out), so "`f`
  is unramified above `p`" does not make the descended `fᵢ` unramified
  above `p`; and
* `Ind_{G_{Fᵢ}}^{G_ℚ}` of an unramified representation is unramified at
  `p` only when `p` is UNRAMIFIED in `Fᵢ`, which the witness does not
  record and which fails in general — Moret–Bailly's `F` is chosen to
  kill local obstructions, not to be unramified.

Classically the ramification of the individual induced pieces CANCELS in
the virtual sum; that cancellation is a property of the sum, invisible
piece by piece. Which is exactly why the citation has to be taken on the
sum — i.e. here — and cannot be pushed down onto the pieces.

MACHINERY AUDIT (2026-07-26): see the sibling leaf
`threeadicRealization_isUnramifiedAtEll_of_witness` above for the hard
search. Summary: neither the pin nor `~/cs/FLT` has a Weil group, a
Weil–Deligne representation, higher ramification groups, a tame
character, local class field theory, or smooth representations of `GL₂`
of a `p`-adic field — mathlib's whole ramification-group file is 54
lines ending in a TODO, and its Fontaine theory stops at `𝔹_dR`. So
restating this
leaf over `WD_p(−)` is not a shortcut but a multi-agent theory-building
programme; it is NOT single-agent-sized, and this leaf should not be
re-scoped as though it were.

RE-VERIFIED MECHANICALLY 2026-07-26 (a later owner): every absence claim
of that search was re-run against the CURRENT pin and all still hold —
see the `MACHINERY AUDIT RE-VERIFIED MECHANICALLY` block in the sibling
for the exact results. Relevant to THIS leaf in particular: the `I_p =
I_w` identification that the second closure's `τF` revival needs is
still not available in either direction that would help, and the ONTO
half of the inertia lift is still absent from the tree.

MACHINERY BUILT (2026-07-26 — a POSITIVE note, so it is not looked for
again). The RIGIDITY step that `hirr` exists to buy — Frobenius data
away from a finite set pins a 2-dimensional representation up to
conjugacy, once the comparison object is irreducible — now exists in
characteristic zero and over an arbitrary number field, as
`GaloisRepresentation.exists_conj_of_charFrob_eq_away_of_two_ne_zero`
and its `CharZero` corollary
(`GaloisRepresentation/BrauerNesbittConjugacy.lean`, Step 8). The
previously available form, `exists_conj_of_charFrob_eq_away`, was pinned
to the base `ℚ` and to a FINITE DISCRETE coefficient field, so it could
not be applied on the `3`-adic side at all; the new form applies over
`ℚ_3`, over any finite extension of it, and over `Frac A` for a
coefficient ring `A` module-finite over `ℤ_3`.

That does NOT close this leaf, and the reason is worth stating precisely
because it is a different reason from the ones audited above. Rigidity
pins `Rlz.τ` against a SECOND representation with the same Frobenius
data; the interface carries no such second object on the `3`-adic side —
there is no `τ_Carayol` — so there is nothing to pin `Rlz.τ` to. The gap
is therefore still the structural one already costed above (a `level`
field on `ThreeadicRealization`), and it is an INTERFACE gap, not a
machinery gap. Note also that the ring-level statement over `A` itself,
as opposed to `Frac A`, is FALSE without a residual hypothesis: two
`A`-lattices in one `Frac A` representation have identical Frobenius
charpolys and need not be `A`-conjugate.

HYPOTHESIS LOAD-BEARING AUDIT (2026-07-26, WITH AN EXPLICIT
COUNTEREXAMPLE — this is new, and it is the sharpest thing known about
this leaf, so do not delete it). The hypothesis block is long and looks
like boilerplate carried from the pillar-β template. It is not. Exactly
ONE of its arithmetic hypotheses is load-bearing, and dropping it makes
this leaf FALSE — not merely unprovable:

* **`hirr` (residual irreducibility) IS LOAD-BEARING.** Delete it and
  the following package satisfies every remaining hypothesis and
  refutes the conclusion. Take `ℓ = 5`, `O = ℤ_5`,
  `ρ = 1 ⊕ χ_{cyc,5}` (diagonal on `Fin 2 → ℤ_5`). Then
  `IsHardlyRamified` holds in all four clauses: `det ρ = χ_{cyc,5}`;
  `ρ` is unramified outside `{5} ⊆ {2, 5}`; `ρ` is flat at `5`, being
  the generic fibre of `ℤ/5ⁿ ⊕ μ_{5ⁿ}`; and it is tame at `2` with the
  projection onto the trivial factor as the `1`-dimensional quotient
  and `δ = 1`. Take `k = 𝔽_5`, `ρbar = 1 ⊕ χ̄_{cyc,5}` — again hardly
  ramified, and `hπ` holds because `charFrob ρ (q) = (X−1)(X−q)`
  reduces to `charFrob ρbar (q)`. Take `F` any totally real Galois
  field, `E = ℚ`, `heckeF w = X² − (1+Nw)X + Nw`,
  `τF = (1 ⊕ χ_{cyc,3})|_{G_F}`: that is a `PotentialModularityWitness`
  (`modularF` and `matchF₃` are the displayed factorisation). Finally
  take `S₁ = ∅`, `A = ℤ_3`, and for `τ` the NON-SPLIT extension of `1`
  by `χ_{cyc,3}` attached to the Kummer class of `p` in
  `H¹(G_ℚ, ℤ_3(1)) = (ℚ^×)^∧_3`. Its Frobenius characteristic
  polynomial at every `q` is `(X−1)(X−q)`, so `compat` holds; and it is
  RAMIFIED at `p` because the Kummer class has nonzero valuation there.
  At `p = 7`: `ρ` is unramified at `7`, `τ` is not, and `7 ∉ {3, 5}`.

  So `hirr` is the ONLY thing standing between this statement and a
  concrete refutation — a fact worth knowing well beyond this leaf,
  since the same package refutes `hirr`-free forms of the sibling, of
  `threeadicRealization_ramified_transfer_of_witness` and of
  `threeadicRealization_isUnramified_of_witness`. **Nobody may weaken
  `hirr` anywhere upstream of this cluster without re-deriving all
  four.**

* **`hρ` is NOT an input to this citation.** The counterexample above
  satisfies `hρ` in full, so hard ramification does not exclude it; and
  in the other direction the classical argument (Carayol at the places
  of `F` over `p`, then the descent) never consumes `det ρ`,
  `ρ`'s flatness at `ℓ` or its tameness at `2` — the local
  unramifiedness input it needs is the explicit hypothesis
  `ρ.IsUnramifiedAt p`. This is the formal counterpart of the sibling's
  remark that flatness is consumed THERE and not here. `hρ` is retained
  only because it is what makes the collapse half of the soundness
  audit below available, and for uniformity of the cluster's hypothesis
  block; it must not be read as a mathematical input.

ROUTE AUDIT, THIRD CLOSURE (2026-07-26): THIS LEAF IS
INTERFACE-LIMITED, NOT MACHINERY-LIMITED. The MACHINERY AUDIT above
ends by costing a Weil–Deligne programme, and must NOT be read as
"once that programme exists, this leaf follows". It does not, and the
counterexample above is the proof: no amount of local theory —
ramification filtration, tame character, local monodromy, Weil group,
`WD_p(−)` — can distinguish the two packages there, because both have
literally the same `compat` data. What separates them is `hirr`, and
the route from `hirr` to the conclusion is RIGIDITY, not local theory:
`ρbar` irreducible ⟹ `ρ` irreducible ⟹ the `E`-eigensystem is
irreducible ⟹ (Brauer–Nesbitt + Chebotarev) `τ` is the unique
representation with those Frobenius characteristic polynomials, hence
`τ ≅ τ_Carayol`, which is unramified at `p` by strict compatibility.

That chain needs `τ_Carayol` AS AN OBJECT, and the interface does not
carry it: `ThreeadicRealization` quantifies over every `τ` satisfying
`compat`, and the Carayol member is nowhere named. So the residue is
not a missing theory but a missing datum, and the only two closures are
(a) a seam change that names it (below), or (b) breaking the
circularity of the collapse half — i.e. proving the hypothesis set
unsatisfiable without routing through the headline, which consumes this
node. Do not dispatch a theory-building programme AT THIS LEAF.

CORRECTION TO THE SECOND CLOSURE (2026-07-26, same audit; the closure
still holds but its first bullet is too strong, and the sharper form
locates the obstruction somewhere else, so it is recorded rather than
silently repaired). That bullet says the interface's only link between
`Rlz.τ|_{G_F}` and `Wit.τF` is Frobenius data, "so the
semisimplification obstruction applies verbatim". Under `hirr` it does
NOT: rigidity is exactly the tool that converts Frobenius data into an
isomorphism. `Rlz.compat` and `Wit.matchF₃` both compute through the
same `heckeF`, so `Rlz.τ|_{G_F}` and `Wit.τF` have equal Frobenius
characteristic polynomials at almost every place of `F`; if both are
irreducible, Brauer–Nesbitt plus Chebotarev makes them isomorphic. The
route then continues: at a `p` UNRAMIFIED in `F` one has `I_p ⊆ G_F`
and `I_p = I_w`, so unramifiedness of `τF` at `w | p` transfers to
`Rlz.τ` at `p` verbatim — which is also why the `p ∉ S₁` narrowing
below really does remove an input.

Two things block it, and neither is the one that was recorded:

* irreducibility of the RESTRICTION `ρ|_{G_F}` (hence of `τF`) is not
  carried by `PotentialModularityWitness`. It is available upstream —
  `exists_moretBailly_seed_of_five_le` produces `hirrF` — but it is
  dropped before the witness is formed, and irreducibility does not
  descend from `ρbar` to `ρbar|_{G_F}` for free; and
* the places `p` RAMIFIED in `F`, where `I_p ⊋ I_w` and the transfer
  genuinely needs the virtual-sum cancellation of the second closure.
  These are precisely the places the consumer cannot avoid.

So the corrected statement of the obstruction is: not "Frobenius data
cannot give an isomorphism", but "the witness drops the irreducibility
that would make rigidity applicable, and the ramified-in-`F` places
need the cancellation regardless". Anyone reviving the `τF` route
should attack those two, in that order.

TWO NOTES ON THAT REVIVAL (2026-07-26, the owner of this leaf and its
sibling; both are cheap and neither is acted on here).

* *The irreducibility blocker is the cheap half, and the datum already
  exists upstream.* `exists_moretBailly_seed_of_five_le` does not merely
  produce `hirrF` internally — it already CARRIES
  `(ρbar.map (algebraMap ℚ F)).IsIrreducible` in its conclusion, and
  `exists_potentialModularityWitness_of_five_le` binds it as `hirrF`,
  uses it to call `exists_heckePackage_of_seed`, and then drops it when
  it builds the witness. So recording it as a field of
  `PotentialModularityWitness` costs one field and one constructor entry,
  needs no new leaf, and there is exactly ONE construction site in the
  tree. It is NOT done here only because it would sit unconsumed until
  the rest of the rigidity route exists — a decision for whoever owns
  that route, not a difficulty.
* *Use TOTAL SPLITTING, not unramifiedness, at the places where the
  `I_p = I_w` identification is wanted.* See the COST RE-DERIVATION in
  the sibling `threeadicRealization_isUnramifiedAtEll_of_witness` above:
  `IsTotallySplitAt F p` gives `F_w = ℚ_p`, hence `I_w = I_p` by equality
  of completions, whereas mere unramifiedness gives the same equality
  only through inertia-lifting theory the pin does not have. The remark
  above that "at a `p` UNRAMIFIED in `F` one has `I_p = I_w`" is
  mathematically right and formally expensive; the totally-split form is
  both. It does not help at the ramified-in-`F` places, which remain the
  real obstruction for THIS leaf.

MACHINERY NOTE for that route, since it names a concrete and plausibly
provable missing lemma rather than a programme: the rigidity step is
ALREADY IN THE TREE in one special case, as
`GaloisRepresentation/BrauerNesbittConjugacy.lean`'s
`exists_conj_of_charFrob_eq_away` (Chebotarev density via
`dense_conjClasses_globalFrob` + the dimension-`2` Brauer–Nesbitt core
`exists_linearEquiv_of_charpoly_eq`; Carayol, Contemp. Math. 165
(1994), Théorème 1; Diamond–Darmon–Taylor, Lemma 3.27). What it does
NOT cover is exactly what the `τF` route needs, in two independent
directions: its coefficients are a FINITE DISCRETE field (the residual
case), whereas `Rlz.A` is `3`-adic of characteristic `0`; and its base
field is `ℚ`, whereas the comparison `Rlz.τ|_{G_F} ≅ Wit.τF` lives over
`F`. A characteristic-zero, module-finite-over-`ℤ_p`, general-number-
field analogue of that one theorem is a well-posed target — unlike the
Weil–Deligne programme, which the THIRD CLOSURE above shows would not
help here even if it existed.

NARROWING AUDIT (2026-07-26; the fleet's test for a terminal citation
is whether a narrowing REMOVES A LITERATURE INPUT, so all three
candidates are costed against it and none is taken):

* *Exclude `p = 2`.* Downstream never uses it — the STRENGTH AUDIT of
  `threeadicRealization_ramified_transfer_of_witness` shows the only
  extracted content is "`τ` is unramified outside `{2, 3}`". But
  Carayol covers `p = 2` exactly as it covers `p = 5`, so this removes
  no input and is cosmetic. NOT TAKEN.
* *Add `p ∉ Rlz.S₁`.* This one DOES remove a genuine input: `S₁`
  contains the primes ramified in `F`, and at `p ∉ S₁` the descent may
  be run piece by piece (`Ind` of an unramified representation is
  unramified at a prime unramified in the intermediate field), so the
  virtual-sum CANCELLATION of the SECOND CLOSURE above is not needed.
  It is nevertheless NOT TAKEN, because it breaks the consumer: the
  conductor node needs the conclusion at every `p ≠ 3`, and `S₁` is
  produced existentially upstream in a form that can be ENLARGED but
  never shrunk — unlike `badF` in
  `carayol_threeadic_realization_of_heckePackage`, where enlargement
  was exactly what made the same manoeuvre free.
* *The seam change* — give `ThreeadicRealization` a `level` field, as
  the sibling's STRUCTURAL OPTION describes. New argument in its
  favour, recorded for whoever owns the seam rather than acted on here:
  it is DEDUPLICATION, not hiding. The construction citation
  `blggt_threeadicBrauerSum_of_witness` already cites BLGGT §5.3 /
  Theorem 5.5.1, and that theorem produces a member of a STRICTLY
  compatible system, i.e. it already asserts the local parameters at
  every `p ∤ 3`. So the construction leaf currently under-asserts
  relative to its own source, and this leaf pays for the difference by
  citing the same theorem a second time. Against that: the split of
  2026-07-25 exists to keep Fontaine–Laffaille and Carayol visibly
  apart, and the change touches a structure, two proven assemblies and
  another agent's sorried leaf. ORCHESTRATOR-LEVEL DECISION, not a
  leaf-level one.

EQUIVALENCE NOTE (2026-07-26, so the re-cut is not re-litigated): this
leaf and its sibling together are EQUIVALENT, given `hρ`, to the single
statement of `exists_conductor_threeadicRealization_of_witness` below —
that node is currently PROVEN from the two of them, and conversely each
of them follows from its two clauses (`p ∤ N` gives clause 1 directly;
`p ∣ N` gives `p ≠ ℓ`, which kills the `ℓ` case, and
`¬ ρ.IsUnramifiedAt p`, which kills the transfer case). Collapsing back
to one leaf therefore changes no mathematics and LOSES the separation of
the two distinct literature inputs, which is the whole point of the
2026-07-25 split. Do not do it.

SOUNDNESS AUDIT (both ways, 2026-07-25): (i) direct — for the
realization produced by the construction leaf this is Carayol's theorem
as cited, applied to the descended eigensystem on both sides of the
compatible family; for an abstract realization the
abstract-quantification caveat of pillar β applies, and (ii) collapse —
the hypothesis set is classically unsatisfiable (headline at the end of
this module), so the statement is classically true for every package.

CIRCULARITY GUARD (inherited from pillar β, load-bearing): no
discharge through `Family.lean`, `Lift.lean`, or
`Modularity/Interface.lean`. -/
theorem threeadicRealization_unramifiedTransfer_of_witness
    {ℓ : ℕ} (hℓodd : Odd ℓ) [Fact ℓ.Prime] (hℓ5 : 5 ≤ ℓ)
    {O : Type u} [CommRing O] [IsDomain O] [TopologicalSpace O]
    [IsTopologicalRing O] [Algebra ℤ_[ℓ] O] [IsLocalRing O]
    [Module.Finite ℤ_[ℓ] O] [IsModuleTopology ℤ_[ℓ] O]
    (hZinj : Function.Injective (algebraMap ℤ_[ℓ] O))
    {ρ : GaloisRep ℚ O (Fin 2 → O)}
    (hrank : Module.rank O (Fin 2 → O) = 2)
    (hρ : IsHardlyRamified hℓodd hrank ρ)
    {k : Type u} [Field k] [Finite k] [Algebra ℤ_[ℓ] k]
    [TopologicalSpace k] [DiscreteTopology k]
    {W : Type v} [AddCommGroup W] [Module k W] [Module.Finite k W]
    [Module.Free k W]
    (hW : Module.rank k W = 2) {ρbar : GaloisRep ℚ k W}
    (hρbar : IsHardlyRamified hℓodd hW ρbar)
    (hirr : ρbar.IsIrreducible)
    (π : O →+* k) (hπsurj : Function.Surjective π)
    (hπ : ∀ (q : ℕ) (hq : q.Prime), q ≠ 2 → q ≠ ℓ →
      (ρ.charFrob hq.toHeightOneSpectrumRingOfIntegersRat).map π =
        ρbar.charFrob hq.toHeightOneSpectrumRingOfIntegersRat)
    {Wit : PotentialModularityWitness ℓ O ρ}
    (Rlz : ThreeadicRealization ℓ O ρ Wit) :
    ∀ p (hp : p.Prime), p ≠ 3 → p ≠ ℓ →
      ρ.IsUnramifiedAt hp.toHeightOneSpectrumRingOfIntegersRat →
      Rlz.τ.IsUnramifiedAt hp.toHeightOneSpectrumRingOfIntegersRat :=
  Rlz.unramifiedTransfer

/-- **Member-independence of the ramification locus away from `3`**
(DECOMPOSED 2026-07-25 — now a PROVEN assembly over the two citation
leaves above, one per literature input; previously a single bundled
citation leaf isolated 2026-07-25 out of
`exists_conductor_threeadicRealization_of_witness`, whose conductor
bookkeeping is PROVEN below over it): every prime `p ≠ 3` at which the
Brauer-descended `3`-adic member `τ` genuinely RAMIFIES is distinct
from `ℓ`, and is a prime at which the `ℓ`-adic member `ρ` itself
genuinely ramifies.

CITATION-SPLIT AUDIT (2026-07-25). The old sorry here bundled TWO
different literature theorems into one clause, which is why it is now
an assembly:

* the `p ≠ ℓ` clause is the FONTAINE–LAFFAILLE input at the `ℓ`-adic
  member's own residue characteristic — `ρ` is flat at `ℓ`
  (`hρ.isFlat`), hence the level is prime to `ℓ`, hence `τ` is
  unramified at `ℓ`; it is now the leaf
  `threeadicRealization_isUnramifiedAtEll_of_witness`, which is a
  statement about `τ` ALONE and mentions `ρ` only through the
  hypothesis set;
* the `¬ ρ.IsUnramifiedAt p` clause is the CARAYOL member-independence
  half, at a place prime to both residue characteristics; it is now the
  leaf `threeadicRealization_unramifiedTransfer_of_witness`, stated in
  its contrapositive (and weakest useful) form "`ρ` unramified at
  `p ∉ {3, ℓ}` ⟹ `τ` unramified at `p`".

Nothing is lost or smuggled by the split: the assembly below is pure
logic, and conversely each leaf is an instance of this statement
(`p = ℓ` for the first, the contrapositive at `p ∉ {3, ℓ}` for the
second), so the cut is an equivalence, not a weakening.

ASSEMBLY (2026-07-25, PROVEN). Let `p ≠ 3` be a prime at which `τ`
ramifies. If `p = ℓ` then the Fontaine–Laffaille leaf says `τ` is
unramified at `p`, a contradiction; so `p ≠ ℓ`. With `p ∉ {3, ℓ}` in
hand, the Carayol transfer leaf applies at `p`, and its contrapositive
turns ramification of `τ` at `p` into ramification of `ρ` at `p`.

Note what is NOT asserted: nothing about `p = 3` (the residue
characteristic of `τ`, where the flatness node
`threeadicRealization_isFlat_of_witness` carries the local condition
instead), and no claim that any prime ramifies. Consequently the
statement is satisfiable by a member unramified everywhere away from
`3`, which is precisely the classical expectation here — the conductor
of the system divides `2`.

STRENGTH AUDIT (2026-07-25): the conclusion is strictly stronger than
anything downstream consumes. Every consumer (through
`exists_conductor_threeadicRealization_of_witness` and
`threeadicRealization_isUnramified_of_witness`) uses
`¬ ρ.IsUnramifiedAt p` only to CONTRADICT `hρ.isUnramified`, so what is
extracted downstream is just "`τ` is unramified outside `{2, 3}`"; the
residual content — that `ρ` genuinely ramifies at `2` whenever `τ`
does — is carried but never used. It is kept because it is what Carayol
actually gives, and because dropping it would make this node's
statement no longer an equivalent recut of the two leaves above.

Literature (via the leaves): Carayol, *Sur les représentations
`ℓ`-adiques associées aux formes modulaires de Hilbert*, Ann. Sci. ÉNS
19 (1986) (local-global compatibility); Khare–Wintenberger, *Serre's
modularity conjecture (I)*, Invent. Math. 178 (2009), §5 (strict
compatibility away from the residue characteristic); BLGGT, *Potential
automorphy and change of weight*, Ann. of Math. 179 (2014), §5.5;
Fontaine–Laffaille, *Construction de représentations p-adiques*,
Ann. Sci. ÉNS 15 (1982) (flat at `ℓ` ⟺ level prime to `ℓ` in weight
`2`).

SOUNDNESS AUDIT (both ways, 2026-07-25): inherited from the two leaves
(see their docstrings) — (i) direct: Carayol's theorem plus the
Fontaine–Laffaille level bound, applied to the descended eigensystem on
both sides of the compatible family, for an abstract realization
subject to the abstract-quantification caveat of pillar β; and (ii)
collapse: the hypothesis set is classically unsatisfiable (headline at
the end of this module), so the statement is classically true for every
package. The assembly below adds nothing to audit — it is pure logic.

CIRCULARITY GUARD (inherited from pillar β, load-bearing): respected —
the only leaves consumed are the two above, which carry the same guard;
nothing routes through `Family.lean`, `Lift.lean`, or
`Modularity/Interface.lean`. -/
theorem threeadicRealization_ramified_transfer_of_witness
    {ℓ : ℕ} (hℓodd : Odd ℓ) [Fact ℓ.Prime] (hℓ5 : 5 ≤ ℓ)
    {O : Type u} [CommRing O] [IsDomain O] [TopologicalSpace O]
    [IsTopologicalRing O] [Algebra ℤ_[ℓ] O] [IsLocalRing O]
    [Module.Finite ℤ_[ℓ] O] [IsModuleTopology ℤ_[ℓ] O]
    (hZinj : Function.Injective (algebraMap ℤ_[ℓ] O))
    {ρ : GaloisRep ℚ O (Fin 2 → O)}
    (hrank : Module.rank O (Fin 2 → O) = 2)
    (hρ : IsHardlyRamified hℓodd hrank ρ)
    {k : Type u} [Field k] [Finite k] [Algebra ℤ_[ℓ] k]
    [TopologicalSpace k] [DiscreteTopology k]
    {W : Type v} [AddCommGroup W] [Module k W] [Module.Finite k W]
    [Module.Free k W]
    (hW : Module.rank k W = 2) {ρbar : GaloisRep ℚ k W}
    (hρbar : IsHardlyRamified hℓodd hW ρbar)
    (hirr : ρbar.IsIrreducible)
    (π : O →+* k) (hπsurj : Function.Surjective π)
    (hπ : ∀ (q : ℕ) (hq : q.Prime), q ≠ 2 → q ≠ ℓ →
      (ρ.charFrob hq.toHeightOneSpectrumRingOfIntegersRat).map π =
        ρbar.charFrob hq.toHeightOneSpectrumRingOfIntegersRat)
    {Wit : PotentialModularityWitness ℓ O ρ}
    (Rlz : ThreeadicRealization ℓ O ρ Wit) :
    ∀ p (hp : p.Prime), p ≠ 3 →
      ¬ Rlz.τ.IsUnramifiedAt hp.toHeightOneSpectrumRingOfIntegersRat →
      p ≠ ℓ ∧
        ¬ ρ.IsUnramifiedAt hp.toHeightOneSpectrumRingOfIntegersRat := by
  intro p hp hp3 hram
  -- `p ≠ ℓ`: the Fontaine–Laffaille leaf says `τ` is unramified at `ℓ`
  have hpℓ : p ≠ ℓ := by
    rintro rfl
    exact hram (threeadicRealization_isUnramifiedAtEll_of_witness hℓodd hℓ5
      hZinj hrank hρ hW hρbar hirr π hπsurj hπ Rlz)
  -- `ρ` ramifies at `p`: the contrapositive of the Carayol transfer leaf,
  -- now legitimate since `p` is prime to both residue characteristics
  exact ⟨hpℓ, fun hun => hram
    (threeadicRealization_unramifiedTransfer_of_witness hℓodd hℓ5 hZinj
      hrank hρ hW hρbar hirr π hπsurj hπ Rlz p hp hp3 hpℓ hun)⟩

/-- **Carayol local-global compatibility away from the residue
characteristic — the conductor of the descended system** (PROVEN
2026-07-25 over the sharper purely local node
`threeadicRealization_ramified_transfer_of_witness`): the
Brauer-descended `3`-adic member `τ` has a
conductor `N` in the usual sense, namely

* `τ` is unramified at every prime `p ∤ 3N` (clause 1), and
* every prime `p ∤ 3` dividing `N` is a prime at which the `ℓ`-adic
  member `ρ` itself genuinely ramifies, and is distinct from `ℓ`
  (clause 2).

The literature content of this node — that the conductor is an
invariant of the compatible system away from the residue characteristic
— is now carried by the sharper, purely local node
`threeadicRealization_ramified_transfer_of_witness` (immediately above):
every prime `p ≠ 3` at which `τ` ramifies is a prime `≠ ℓ` at which `ρ`
ramifies. That node is itself PROVEN (2026-07-25) over TWO citation
leaves, one per literature input — see its CITATION-SPLIT AUDIT. It is
exactly Carayol's member-independence of the
Weil–Deligne parameter at places prime to both residue characteristics,
together with the Fontaine–Laffaille input `p ≠ ℓ` (`ρ` is FLAT at `ℓ`
by `hρ.isFlat`, i.e. crystalline of Hodge–Tate weights `{0, 1}`, the
local condition corresponding to level prime to `ℓ`, so `ℓ` does not
divide the conductor). Everything else in this statement — the
existential conductor itself, its finite support, and the degeneracy
bookkeeping — is PROVEN here; the two formulations are in fact
EQUIVALENT given `hρ` (clause 1's contrapositive against clause 2 gives
the local transfer back), so nothing is lost or smuggled by the cut.

ASSEMBLY (2026-07-25, PROVEN). By the local transfer leaf and
`hρ.isUnramified` (`ρ` is unramified outside `{2, ℓ}`), a prime `p ≠ 3`
at which `τ` ramifies satisfies `p ≠ ℓ` and `ρ` ramified at `p`, hence
`p = 2`: away from `3`, the ONLY prime at which `τ` can ramify is `2`.
The conductor is then read off by a case split on that single prime:

* if `τ` is unramified at `2`, take `N = 1` — clause 1 holds at every
  `p ≠ 3` (no such `p` ramifies), and clause 2 is vacuous since no
  prime divides `1`;
* if `τ` ramifies at `2`, take `N = 2` — clause 1 holds at every prime
  `p ≠ 3` with `p ∤ 2`, since a ramified such `p` would be `2`; and
  clause 2 at the only prime divisor `p = 2` is precisely the transfer
  leaf applied at `2`.

This is the Lean rendering of "the conductor of the system divides
`2`", and it also settles the degeneracy question mechanically: the
witness produced here is `1` or `2`, never `0`, so the bad set is
finite and clause 1 is never vacuous.

Literature (via the leaf): Carayol, *Sur les représentations `ℓ`-adiques
associées aux formes modulaires de Hilbert*, Ann. Sci. ÉNS 19 (1986)
(local-global compatibility fixing the conductor); Khare–Wintenberger,
*Serre's modularity conjecture (I)*, Invent. Math. 178 (2009), §5
(strict compatibility away from the residue characteristic); BLGGT,
*Potential automorphy and change of weight*, Ann. of Math. 179 (2014),
§5.5 (strict compatibility of the constructed system);
Fontaine–Laffaille, *Construction de représentations p-adiques*,
Ann. Sci. ÉNS 15 (1982) (flat at `ℓ` ⟺ level prime to `ℓ` in weight
`2`).

SOUNDNESS AUDIT (both ways, 2026-07-24, re-audited 2026-07-25 after the
cut): (i) direct — for the realization produced by the construction
leaf the transfer leaf is Carayol's theorem as cited, applied to the
descended eigensystem on both sides of the compatible family, and the
assembly above is formal; for an abstract realization the
abstract-quantification caveat of pillar β applies, and (ii) collapse —
the hypothesis set is classically unsatisfiable (headline below), so
the statement is classically true for every package. Degeneracy check:
the statement is NOT satisfiable by a degenerate `N`. `N = 0` is
excluded by clause 2 at `p = ℓ` (`ℓ ∣ 0` and `ℓ ≠ 3` since `ℓ ≥ 5`
would force `ℓ ≠ ℓ`), so any witness has finitely many bad primes; and
clause 1 is not vacuous for any witness, since it covers every prime
outside the finite support of `3N`.

CIRCULARITY GUARD (inherited from pillar β, load-bearing): no
discharge through `Family.lean`, `Lift.lean`, or
`Modularity/Interface.lean` — the transfer leaf carries the same guard,
and the assembly below consumes nothing else. -/
theorem exists_conductor_threeadicRealization_of_witness
    {ℓ : ℕ} (hℓodd : Odd ℓ) [Fact ℓ.Prime] (hℓ5 : 5 ≤ ℓ)
    {O : Type u} [CommRing O] [IsDomain O] [TopologicalSpace O]
    [IsTopologicalRing O] [Algebra ℤ_[ℓ] O] [IsLocalRing O]
    [Module.Finite ℤ_[ℓ] O] [IsModuleTopology ℤ_[ℓ] O]
    (hZinj : Function.Injective (algebraMap ℤ_[ℓ] O))
    {ρ : GaloisRep ℚ O (Fin 2 → O)}
    (hrank : Module.rank O (Fin 2 → O) = 2)
    (hρ : IsHardlyRamified hℓodd hrank ρ)
    {k : Type u} [Field k] [Finite k] [Algebra ℤ_[ℓ] k]
    [TopologicalSpace k] [DiscreteTopology k]
    {W : Type v} [AddCommGroup W] [Module k W] [Module.Finite k W]
    [Module.Free k W]
    (hW : Module.rank k W = 2) {ρbar : GaloisRep ℚ k W}
    (hρbar : IsHardlyRamified hℓodd hW ρbar)
    (hirr : ρbar.IsIrreducible)
    (π : O →+* k) (hπsurj : Function.Surjective π)
    (hπ : ∀ (q : ℕ) (hq : q.Prime), q ≠ 2 → q ≠ ℓ →
      (ρ.charFrob hq.toHeightOneSpectrumRingOfIntegersRat).map π =
        ρbar.charFrob hq.toHeightOneSpectrumRingOfIntegersRat)
    {Wit : PotentialModularityWitness ℓ O ρ}
    (Rlz : ThreeadicRealization ℓ O ρ Wit) :
    ∃ N : ℕ,
      (∀ p (hp : p.Prime), p ≠ 3 → ¬ p ∣ N →
        Rlz.τ.IsUnramifiedAt hp.toHeightOneSpectrumRingOfIntegersRat) ∧
      (∀ p (hp : p.Prime), p ≠ 3 → p ∣ N →
        p ≠ ℓ ∧
          ¬ ρ.IsUnramifiedAt hp.toHeightOneSpectrumRingOfIntegersRat) := by
  classical
  -- the local literature joint: away from `3`, ramification of `τ`
  -- transfers to ramification of `ρ` at a prime distinct from `ℓ`
  have htr := threeadicRealization_ramified_transfer_of_witness hℓodd hℓ5
    hZinj hrank hρ hW hρbar hirr π hπsurj hπ Rlz
  -- hence, away from `3`, the ONLY prime at which `τ` can ramify is `2`:
  -- `ρ` is unramified outside `{2, ℓ}`, and the transfer rules out `ℓ`
  have hbadtwo : ∀ p (hp : p.Prime), p ≠ 3 →
      ¬ Rlz.τ.IsUnramifiedAt hp.toHeightOneSpectrumRingOfIntegersRat →
      p = 2 := by
    intro p hp hp3 hram
    obtain ⟨hpℓ, hρram⟩ := htr p hp hp3 hram
    by_contra hp2
    exact hρram (hρ.isUnramified p hp ⟨hp2, hpℓ⟩)
  by_cases h2 : Rlz.τ.IsUnramifiedAt
      Nat.prime_two.toHeightOneSpectrumRingOfIntegersRat
  · -- `τ` is unramified at `2` as well: the conductor is `1`
    refine ⟨1, ?_, ?_⟩
    · intro p hp hp3 _
      by_contra hram
      have hp2 : p = 2 := hbadtwo p hp hp3 hram
      subst hp2
      exact hram h2
    · intro p hp _ hdvd
      exact absurd (Nat.dvd_one.mp hdvd) hp.ne_one
  · -- `τ` ramifies at `2`: the conductor is `2`
    refine ⟨2, ?_, ?_⟩
    · intro p hp hp3 hdvd
      by_contra hram
      have hp2 : p = 2 := hbadtwo p hp hp3 hram
      subst hp2
      exact hdvd dvd_rfl
    · intro p hp hp3 hdvd
      have hp2 : p = 2 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hdvd
      subst hp2
      exact htr 2 hp hp3 h2

/-- **Condition transfer, ramification — unramified outside `{2, 3}`**
(PROVEN 2026-07-24 over the Carayol citation leaf
`exists_conductor_threeadicRealization_of_witness`): the
Brauer-descended `3`-adic member is unramified at
every prime `p ∉ {2, 3}`. Classically: the compatible system attached
to the descended eigensystem has conductor dividing `2` (the hardly
ramified `ρ` has conductor `2`, and the conductor is constant in a
strictly compatible system), and a member of a strictly compatible
system is unramified at every prime away from the conductor and the
residue characteristic — here away from `2` and `3` (strict
compatibility in the sense of Khare–Wintenberger (I) §5: the
Weil–Deligne parameter at `p` is independent of the member for
`p` prime to the residue characteristic, and it is unramified off the
conductor).

Literature: Khare–Wintenberger, *Serre's modularity conjecture (I)*,
Invent. Math. 178 (2009), §5; BLGGT, *Potential automorphy and change
of weight*, Ann. of Math. 179 (2014), §5.5 (strict compatibility of
the constructed system); Carayol, *Sur les représentations ℓ-adiques
associées aux formes modulaires de Hilbert*, Ann. Sci. ÉNS 19 (1986)
(local-global compatibility fixing the conductor).

ROUTE AUDIT (2026-07-24). Two cuts of this node were considered.

* The *charFrob cut*: transport the ramification statement out of the
  realization's own compatibility clause `Rlz.compat`. REJECTED — and
  it is worth recording why, since `compat` is the only arithmetic
  datum the interface structure carries. `compat` equates
  CHARACTERISTIC POLYNOMIALS OF FROBENIUS at unramified places; it says
  nothing whatever about inertia, and it is quantified away from the
  finite exceptional set `Rlz.S₁`, which is precisely where the
  ramification question is nontrivial. No amount of Frobenius data
  determines an inertia action, so this cut cannot close — it would
  have to smuggle the whole content into a "compatibility ⟹ inertia"
  step that is itself the theorem.
* The *conductor cut* (TAKEN): cut at the literature joint, i.e. at
  Carayol's local-global compatibility itself, which is the theorem
  that produces a conductor with the two defining properties (`τ`
  unramified off `3N`; the support of `N` away from `3` seen on the
  `ℓ`-adic member). Everything downstream of that joint is then a
  formal `p ∣ N` dichotomy against the hardly ramified hypotheses on
  `ρ`, and is PROVEN here.

ASSEMBLY (2026-07-24, PROVEN): let `N` be the conductor supplied by
`exists_conductor_threeadicRealization_of_witness`, and let `p` be a
prime with `p ≠ 2`, `p ≠ 3`. Dichotomy on `p ∣ N`.

* `p ∤ N`: clause 1 of the citation leaf gives `τ` unramified at `p`
  directly — this is the generic case, and the informal "conductor
  divides `2`" is exactly the assertion that it is the only case.
* `p ∣ N`: clause 2 gives `p ≠ ℓ` together with `ρ` RAMIFIED at `p`.
  But `ρ` is hardly ramified, hence unramified at every prime outside
  `{2, ℓ}` (`hρ.isUnramified`), and `p ∉ {2, ℓ}` — contradiction. So
  this case is empty, which is the Lean rendering of "the conductor of
  the system divides `2`": its only possible odd prime divisor away
  from `3` would be a prime of genuine ramification of `ρ`, and there
  is none.

The residual sorries of this node are therefore exactly the citation
leaves under `threeadicRealization_ramified_transfer_of_witness` (two
of them since the split of 2026-07-25: Carayol member-independence at
`p ∤ 3ℓ`, and Fontaine–Laffaille at `ℓ`), and the two hardly ramified
inputs it is cut against
(`hρ.isUnramified` here, `hρ.isFlat` inside the leaf's `p ≠ ℓ` clause)
are recorded at the joint rather than assumed silently.

SOUNDNESS AUDIT (both ways, 2026-07-24): (i) direct — for the
realization produced by the construction leaf this is the strict
compatibility transfer above; for an abstract realization the
abstract-quantification caveat of pillar β applies, and (ii) collapse
— the hypothesis set is classically unsatisfiable (headline below),
so the statement is classically true for every package.

CIRCULARITY GUARD (inherited from pillar β, load-bearing): no
discharge through `Family.lean`, `Lift.lean`, or
`Modularity/Interface.lean` — the citation leaf carries the same
guard, and the assembly below consumes nothing else. -/
theorem threeadicRealization_isUnramified_of_witness
    {ℓ : ℕ} (hℓodd : Odd ℓ) [Fact ℓ.Prime] (hℓ5 : 5 ≤ ℓ)
    {O : Type u} [CommRing O] [IsDomain O] [TopologicalSpace O]
    [IsTopologicalRing O] [Algebra ℤ_[ℓ] O] [IsLocalRing O]
    [Module.Finite ℤ_[ℓ] O] [IsModuleTopology ℤ_[ℓ] O]
    (hZinj : Function.Injective (algebraMap ℤ_[ℓ] O))
    {ρ : GaloisRep ℚ O (Fin 2 → O)}
    (hrank : Module.rank O (Fin 2 → O) = 2)
    (hρ : IsHardlyRamified hℓodd hrank ρ)
    {k : Type u} [Field k] [Finite k] [Algebra ℤ_[ℓ] k]
    [TopologicalSpace k] [DiscreteTopology k]
    {W : Type v} [AddCommGroup W] [Module k W] [Module.Finite k W]
    [Module.Free k W]
    (hW : Module.rank k W = 2) {ρbar : GaloisRep ℚ k W}
    (hρbar : IsHardlyRamified hℓodd hW ρbar)
    (hirr : ρbar.IsIrreducible)
    (π : O →+* k) (hπsurj : Function.Surjective π)
    (hπ : ∀ (q : ℕ) (hq : q.Prime), q ≠ 2 → q ≠ ℓ →
      (ρ.charFrob hq.toHeightOneSpectrumRingOfIntegersRat).map π =
        ρbar.charFrob hq.toHeightOneSpectrumRingOfIntegersRat)
    {Wit : PotentialModularityWitness ℓ O ρ}
    (Rlz : ThreeadicRealization ℓ O ρ Wit) :
    ∀ p (hp : p.Prime), p ≠ 2 ∧ p ≠ 3 →
      Rlz.τ.IsUnramifiedAt hp.toHeightOneSpectrumRingOfIntegersRat := by
  -- the conductor of the descended system (Carayol local-global
  -- compatibility away from the residue characteristic)
  obtain ⟨N, hunr, hbad⟩ :=
    exists_conductor_threeadicRealization_of_witness hℓodd hℓ5 hZinj
      hrank hρ hW hρbar hirr π hπsurj hπ Rlz
  rintro p hp ⟨hp2, hp3⟩
  by_cases hdvd : p ∣ N
  · -- `p` divides the conductor: then `ρ` itself ramifies at `p`,
    -- contradicting hard ramification since `p ∉ {2, ℓ}`
    obtain ⟨hpℓ, hρbad⟩ := hbad p hp hp3 hdvd
    exact absurd (hρ.isUnramified p hp ⟨hp2, hpℓ⟩) hρbad
  · -- `p` is prime to the conductor and to `3`
    exact hunr p hp hp3 hdvd

/-- **Raynaud quotient closure, in prolongation form** (sorry node, cut
2026-07-25 for the Fontaine–Laffaille level reduction below): a
`G_ℚ`-equivariant QUOTIENT of a Galois representation which has a flat
prolongation at `v` again has a flat prolongation at `v`.
Scheme-theoretically this is the closure of finite flat group schemes
over the DVR `𝒪ᵥ` under quotients by flat closed subgroup schemes
(Raynaud, *Schémas en groupes de type `(p, …, p)`*, Bull. SMF 102
(1974), §1–3; Tate, *Finite flat group schemes*, in
Cornell–Silverman–Stevens ch. V), read on `ℚ̄ᵥ`-points — the form the
project's prolongation package takes. The equivariance hypothesis is
stated for the GLOBAL action, as in
`GaloisRep.HasFlatProlongationAt.of_addEquiv`; it implies the local one
because `toLocal` is precomposition with `G_ℚᵥ → G_ℚ`.

Intended proof (dual to a subobject closure, and easier — SUB-algebras
of the witness where a subobject closure would quotient it):
* (α) *finiteness*: the source point group is finite (the generic fibre
  `Q := Kᵥ ⊗[𝒪ᵥ] G` of the witness is finite étale over `Kᵥ`), hence so
  is the target through the surjection `e`.
* (β) *étale–Galois*: the target is a finite `G_ℚᵥ`-group, hence the
  point group of a finite étale `Kᵥ`-Hopf algebra `H` by the PROVEN
  Gelfand-duality machinery of `KnownIn1980s/EllipticCurves/Flat.lean`
  (`galoisEquivariantAlgebra` with `galoisEquivariantEval_injective` /
  `_surjective` and `exists_hopfAlgebra_galoisEquivariantAlgebra`);
  pullback of functions along the point surjection is an INJECTIVE
  `Kᵥ`-bialgebra map `H → Q` (injective because the points of the étale
  `H` separate its functions; a bialgebra map because the point
  surjection is a group homomorphism).
* (γ) *schematic closure over the DVR*: `G' := H ∩ G` (inside `Q`) is
  an `𝒪ᵥ`-subalgebra, module-finite over the noetherian `𝒪ᵥ` and
  torsion-free, hence finite FREE, so flat; it spans `H` over `Kᵥ`
  (every `x ∈ H ⊆ Q = Kᵥ · G` has `cx ∈ G` for some `c ≠ 0` in `𝒪ᵥ`,
  and `cx ∈ H` as `H` is a `Kᵥ`-subspace), so `Kᵥ ⊗[𝒪ᵥ] G' ≅ H` has
  étale generic fibre; and `G'` is SATURATED in `G`, which makes the
  comultiplication of `H` carry `G'` into `G' ⊗[𝒪ᵥ] G'` (counit and
  antipode restrict likewise), i.e. `G'` is a Hopf order.
* (δ) *conclusion*: the `ℚ̄ᵥ`-points of `Kᵥ ⊗[𝒪ᵥ] G'` are those of
  `H`, i.e. the target, `G_ℚᵥ`-equivariantly.

Unconditionally TRUE — permanent library material carrying no
hypothesis package (for `e` bijective this is already
`GaloisRep.HasFlatProlongationAt.of_addEquiv`, and for a subsingleton
target `GaloisRep.hasFlatProlongationAt_of_subsingleton`).

HOME AUDIT (2026-07-25, load-bearing — read before "deduplicating"
this brick). The same Raynaud content exists in the tree ONCE more, as
the carrier-level `IsFlatPointsGroupAt.of_surjective` of
`Modularity/Interface.lean` (there over an abstract `G_ℚᵥ`-module
rather than a representation). That one is IMPORT-UNREACHABLE from
here: `Interface.lean` imports THIS module, so consuming it would be a
literal import cycle — the very thing the pillar-β circularity guard
forbids. The architecturally neutral home for both would be
`Deformations/RepresentationTheory/FlatProlongation.lean` (below
`Interface.lean` and below this module, and already the home of the
`of_addEquiv` transport), and the intended unification is to move this
brick there and re-prove `Interface.lean`'s carrier version from it.
That was deliberately NOT done in this pass for two reasons: the
carrier leaf is separately owned, and `FlatProlongation.lean` sits
under the 30k-line `ModThree.lean` cone, so touching it forces a
full-cone rebuild in every worktree of the fleet, while this module
already had to be rebuilt for the decomposition below. Whoever
performs the unification should move BOTH, not restate a third copy. -/
theorem hasFlatProlongationAt_of_surjective
    {v : HeightOneSpectrum (NumberField.RingOfIntegers ℚ)}
    {A₁ : Type*} [CommRing A₁] [TopologicalSpace A₁]
    {M₁ : Type*} [AddCommGroup M₁] [Module A₁ M₁]
    {A₂ : Type*} [CommRing A₂] [TopologicalSpace A₂]
    {M₂ : Type*} [AddCommGroup M₂] [Module A₂ M₂]
    {ρ₁ : GaloisRep ℚ A₁ M₁} {ρ₂ : GaloisRep ℚ A₂ M₂}
    (h : ρ₁.HasFlatProlongationAt v)
    (e : M₁ →+ M₂) (hsurj : Function.Surjective e)
    (he : ∀ (σ : Field.absoluteGaloisGroup ℚ) (x : M₁), e (ρ₁ σ x) = ρ₂ σ (e x)) :
    ρ₂.HasFlatProlongationAt v :=
  sorry

set_option linter.unusedVariables false in
/-- **The Fontaine–Laffaille local shape at `3`, on the `3`-power
levels of the stable lattice** (PROVEN 2026-07-25 by the CUT-LEVEL
REPAIR — now a one-line projection of the `ThreeadicRealization` field
`flatAtThreePow`): for every `m ≥ 1` the `3`-power level
`(A ⧸ 3^m) ⊗_A (Fin 2 → A)` — i.e. `T/3^m T` for the stable lattice
`T = Fin 2 → A` — is the group of `ℚ̄_3`-points of the generic fibre of
a finite flat group scheme over `ℤ_3`, the package spelled by
`GaloisRep.HasFlatProlongationAt`.

REPAIR NOTE (2026-07-25 — read this before treating the name as a
frontier node; it is no longer one). This WAS the literature joint of
the flatness transfer, and it was UNDISCHARGEABLE as quantified: over an
arbitrary `Rlz : ThreeadicRealization` the only constraint on `τ` is
`compat`, i.e. characteristic polynomials of Frobenius at almost all
`q ∉ {2, 3, ℓ}`, which pins `τ` at most up to SEMISIMPLIFICATION —
while finite flatness at `3` is a property of the EXTENSION CLASS,
invisible to semisimplification (the two extensions of `ℤ/3` by `μ_3`
over `ℚ_3` classified by `1` and by `3` in `ℚ_3^×/(ℚ_3^×)^3` share all
Frobenius data and exactly one is finite flat over `ℤ_3`). No amount of
Fontaine–Laffaille formalization would have changed that; the defect was
in the CUT, not in the difficulty.

The local shape at `3` is therefore now a FIELD of the interface
(`ThreeadicRealization.flatAtThreePow`), supplied at the construction
site out of clause (2) of `blggt_threeadicBrauerSum_of_witness` — which
is where the classical discussion, the five-route audit, the
Fontaine–Laffaille literature and the missing-machinery chain now live.
Read that docstring, not this one, for the mathematics. (Between
2026-07-25 and 2026-07-26 that content sat in a separate leaf,
`blggt_threeadicMember_flatAtThreePow`; it was absorbed into the
Brauer-sum citation and deleted.)

This declaration is kept, with its signature unchanged, purely so that
its consumer
`threeadicRealization_hasFlatProlongationAt_of_finite_quotient` and the
whole downstream flatness transfer need no edit. Its hypotheses beyond
`Rlz`, `m` and `hm` are consequently unused — hence the
`linter.unusedVariables` suppression above, which is the mechanically
visible signature of the repair: everything the old proof would have had
to extract from those hypotheses is now carried by the realization
itself.

SOUNDNESS: inherited verbatim from the field, hence from clause (2) of
`blggt_threeadicBrauerSum_of_witness`.

CIRCULARITY GUARD (inherited from pillar β, load-bearing): respected —
the only input is a field of the interface; nothing routes through
`Family.lean`, `Lift.lean`, or `Modularity/Interface.lean`. -/
theorem threeadicRealization_hasFlatProlongationAt_threePow
    {ℓ : ℕ} (hℓodd : Odd ℓ) [Fact ℓ.Prime] (hℓ5 : 5 ≤ ℓ)
    {O : Type u} [CommRing O] [IsDomain O] [TopologicalSpace O]
    [IsTopologicalRing O] [Algebra ℤ_[ℓ] O] [IsLocalRing O]
    [Module.Finite ℤ_[ℓ] O] [IsModuleTopology ℤ_[ℓ] O]
    (hZinj : Function.Injective (algebraMap ℤ_[ℓ] O))
    {ρ : GaloisRep ℚ O (Fin 2 → O)}
    (hrank : Module.rank O (Fin 2 → O) = 2)
    (hρ : IsHardlyRamified hℓodd hrank ρ)
    {k : Type u} [Field k] [Finite k] [Algebra ℤ_[ℓ] k]
    [TopologicalSpace k] [DiscreteTopology k]
    {W : Type v} [AddCommGroup W] [Module k W] [Module.Finite k W]
    [Module.Free k W]
    (hW : Module.rank k W = 2) {ρbar : GaloisRep ℚ k W}
    (hρbar : IsHardlyRamified hℓodd hW ρbar)
    (hirr : ρbar.IsIrreducible)
    (π : O →+* k) (hπsurj : Function.Surjective π)
    (hπ : ∀ (q : ℕ) (hq : q.Prime), q ≠ 2 → q ≠ ℓ →
      (ρ.charFrob hq.toHeightOneSpectrumRingOfIntegersRat).map π =
        ρbar.charFrob hq.toHeightOneSpectrumRingOfIntegersRat)
    {Wit : PotentialModularityWitness ℓ O ρ}
    (Rlz : ThreeadicRealization ℓ O ρ Wit)
    (m : ℕ) (hm : 1 ≤ m) :
    (Rlz.τ.baseChange (Rlz.A ⧸ Ideal.span {(3 : Rlz.A) ^ m})).HasFlatProlongationAt
      (Nat.Prime.toHeightOneSpectrumRingOfIntegersRat
        (Fact.out : Nat.Prime 3)) :=
  Rlz.flatAtThreePow m hm

/-- **The Fontaine–Laffaille local shape at `3`, at an arbitrary finite
level** (DECOMPOSED 2026-07-25 — now a PROVEN transport over the
literature joint `threeadicRealization_hasFlatProlongationAt_threePow`
above and the unconditional Raynaud quotient brick
`hasFlatProlongationAt_of_surjective`): every NONTRIVIAL
finite congruence quotient `(A ⧸ I) ⊗_A (Fin 2 → A)` of the
Brauer-descended `3`-adic member is the group of `ℚ̄_3`-points of the
generic fibre of a finite flat group scheme over `ℤ_3`.

TRANSPORT (PROVEN here — the arbitrary-finite-level quantifier reduced
to the cofinal `3`-power subtower, exactly the reduction the E2b′
lattice-flatness transfer of `Modularity/Interface.lean` performs for
its own levels):

* *a finite congruence quotient kills a power of `3`*: the composite
  `ℤ_3 → A → A ⧸ I` cannot be injective, `ℤ_3` being infinite
  (`CharZero.infinite`) and `A ⧸ I` finite, so its kernel contains
  some `x ≠ 0`; over the discrete valuation ring `ℤ_3` such an `x`
  factors as `u · 3^m` with `u` a unit
  (`IsDiscreteValuationRing.eq_unit_mul_pow_irreducible` at the
  irreducible `3`, `PadicInt.irreducible_p`), whence `3^m ∈ I` — and
  `m ≥ 1` because `I ≠ ⊤` forbids `1 ∈ I`. Note that OPENNESS of `I`
  is not used: finiteness of the quotient is the whole input, which is
  also the form the Fontaine–Laffaille statement takes;
* *the level is a quotient of the `3`-power level*: `3^m ∈ I` gives
  `(3^m) ≤ I`, hence the transition map `A ⧸ 3^m → A ⧸ I`
  (`Submodule.mapQ` along the identity), surjective, and tensoring
  with the lattice (`LinearMap.rTensor`) makes the `I`-level a
  `G_ℚ`-equivariant quotient of the `3^m`-level — equivariance because
  both base-changed actions are `τ` on the right tensor factor
  (`GaloisRep.baseChange_tmul`);
* *Raynaud closure under quotients* then carries the prolongation of
  the `3`-power level (the literature joint above) to the `I`-level.

Classically the mathematical content is the joint's: the system has
parallel weight `2` and conductor prime to `3`, so its `3`-adic member
is crystalline at `3` with Hodge–Tate weights `{0, 1}`, and over `ℤ_3`
(`e = 1 < p - 1 = 2`) Fontaine–Laffaille makes the stable lattice the
Tate module of a `3`-divisible group; see that docstring for the
literature.

SOUNDNESS AUDIT (both ways, 2026-07-25): (i) direct — the transport is
unconditional glue over the joint, so soundness is the joint's; for an
abstract realization the abstract-quantification caveat of pillar β
applies, and (ii) collapse — the hypothesis set is classically
unsatisfiable (headline below), so the statement is classically true
for every package.

CIRCULARITY GUARD (inherited from pillar β, load-bearing): no
discharge through `Family.lean`, `Lift.lean`, or
`Modularity/Interface.lean`; in particular the Raynaud quotient brick
consumed here is `hasFlatProlongationAt_of_surjective` of THIS module,
NOT the carrier-level `IsFlatPointsGroupAt.of_surjective` of
`Modularity/Interface.lean`, which is import-unreachable from here —
see that brick's HOME AUDIT. -/
theorem threeadicRealization_hasFlatProlongationAt_of_finite_quotient
    {ℓ : ℕ} (hℓodd : Odd ℓ) [Fact ℓ.Prime] (hℓ5 : 5 ≤ ℓ)
    {O : Type u} [CommRing O] [IsDomain O] [TopologicalSpace O]
    [IsTopologicalRing O] [Algebra ℤ_[ℓ] O] [IsLocalRing O]
    [Module.Finite ℤ_[ℓ] O] [IsModuleTopology ℤ_[ℓ] O]
    (hZinj : Function.Injective (algebraMap ℤ_[ℓ] O))
    {ρ : GaloisRep ℚ O (Fin 2 → O)}
    (hrank : Module.rank O (Fin 2 → O) = 2)
    (hρ : IsHardlyRamified hℓodd hrank ρ)
    {k : Type u} [Field k] [Finite k] [Algebra ℤ_[ℓ] k]
    [TopologicalSpace k] [DiscreteTopology k]
    {W : Type v} [AddCommGroup W] [Module k W] [Module.Finite k W]
    [Module.Free k W]
    (hW : Module.rank k W = 2) {ρbar : GaloisRep ℚ k W}
    (hρbar : IsHardlyRamified hℓodd hW ρbar)
    (hirr : ρbar.IsIrreducible)
    (π : O →+* k) (hπsurj : Function.Surjective π)
    (hπ : ∀ (q : ℕ) (hq : q.Prime), q ≠ 2 → q ≠ ℓ →
      (ρ.charFrob hq.toHeightOneSpectrumRingOfIntegersRat).map π =
        ρbar.charFrob hq.toHeightOneSpectrumRingOfIntegersRat)
    {Wit : PotentialModularityWitness ℓ O ρ}
    (Rlz : ThreeadicRealization ℓ O ρ Wit)
    (I : Ideal Rlz.A) (hItop : I ≠ ⊤) (hIfin : Finite (Rlz.A ⧸ I)) :
    (Rlz.τ.baseChange (Rlz.A ⧸ I)).HasFlatProlongationAt
      (Nat.Prime.toHeightOneSpectrumRingOfIntegersRat
        (Fact.out : Nat.Prime 3)) := by
  classical
  -- a FINITE congruence quotient of the `ℤ_3`-algebra `A` kills a power
  -- of `3`: the composite `ℤ_3 → A → A ⧸ I` is not injective, and over
  -- the discrete valuation ring `ℤ_3` a nonzero kernel element is a
  -- unit times a power of `3`
  obtain ⟨a, b, hab, heq⟩ :=
    @Finite.exists_ne_map_eq_of_infinite ℤ_[3] (Rlz.A ⧸ I) _ hIfin
      (fun x => Ideal.Quotient.mk I (algebraMap ℤ_[3] Rlz.A x))
  have hx0 : a - b ≠ 0 := sub_ne_zero.mpr hab
  have hxmem : algebraMap ℤ_[3] Rlz.A (a - b) ∈ I := by
    have h0 : Ideal.Quotient.mk I (algebraMap ℤ_[3] Rlz.A (a - b)) = 0 := by
      rw [map_sub, map_sub]
      exact sub_eq_zero_of_eq heq
    exact Ideal.Quotient.eq_zero_iff_mem.mp h0
  obtain ⟨m, u, hu⟩ :=
    IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hx0
      (PadicInt.irreducible_p (p := 3))
  have hm : (3 : Rlz.A) ^ m ∈ I := by
    have hpow : algebraMap ℤ_[3] Rlz.A (((3 : ℕ) : ℤ_[3]) ^ m) ∈ I := by
      have h3 : ((3 : ℕ) : ℤ_[3]) ^ m = ((u⁻¹ : ℤ_[3]ˣ) : ℤ_[3]) * (a - b) := by
        rw [hu, ← mul_assoc]
        simp
      rw [h3, map_mul]
      exact I.mul_mem_left _ hxmem
    simpa [map_pow, map_ofNat] using hpow
  -- the level is a positive one: `I ≠ ⊤` forbids `1 ∈ I`
  have hm1 : 1 ≤ m := by
    rcases Nat.eq_zero_or_pos m with rfl | hpos
    · rw [pow_zero] at hm
      exact absurd ((Ideal.eq_top_iff_one I).mpr hm) hItop
    · exact hpos
  have hle : Ideal.span {(3 : Rlz.A) ^ m} ≤ I := by
    rw [Ideal.span_singleton_le_iff_mem]
    exact hm
  -- the level-transition surjection, `A`-linearly on the left factor
  let q : (Rlz.A ⧸ Ideal.span {(3 : Rlz.A) ^ m}) →ₗ[Rlz.A] (Rlz.A ⧸ I) :=
    Submodule.mapQ (Ideal.span {(3 : Rlz.A) ^ m} : Submodule Rlz.A Rlz.A)
      (I : Submodule Rlz.A Rlz.A) LinearMap.id hle
  have hqsurj : Function.Surjective q := by
    intro y
    obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective (I : Submodule Rlz.A Rlz.A) y
    exact ⟨Submodule.Quotient.mk x, by simp [q]⟩
  have hφsurj : Function.Surjective (LinearMap.rTensor (Fin 2 → Rlz.A) q) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => exact ⟨0, map_zero _⟩
    | add c d hc hd =>
      obtain ⟨x, rfl⟩ := hc
      obtain ⟨y, rfl⟩ := hd
      exact ⟨x + y, map_add _ _ _⟩
    | tmul c w =>
      obtain ⟨c', rfl⟩ := hqsurj c
      exact ⟨c' ⊗ₜ w, by rw [LinearMap.rTensor_tmul]⟩
  -- the literature joint at the `3`-power level `m`
  have hflat := threeadicRealization_hasFlatProlongationAt_threePow hℓodd hℓ5
    hZinj hrank hρ hW hρbar hirr π hπsurj hπ Rlz m hm1
  -- Raynaud closure under quotients
  refine hasFlatProlongationAt_of_surjective hflat
    (LinearMap.rTensor (Fin 2 → Rlz.A) q).toAddMonoidHom hφsurj ?_
  intro σ x
  show (LinearMap.rTensor (Fin 2 → Rlz.A) q)
      ((Rlz.τ.baseChange (Rlz.A ⧸ Ideal.span {(3 : Rlz.A) ^ m})) σ x) =
    (Rlz.τ.baseChange (Rlz.A ⧸ I)) σ ((LinearMap.rTensor (Fin 2 → Rlz.A) q) x)
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add c d hc hd => simp only [map_add, hc, hd]
  | tmul c w =>
    rw [GaloisRep.baseChange_tmul, LinearMap.rTensor_tmul,
      LinearMap.rTensor_tmul, GaloisRep.baseChange_tmul]

/-- **Condition transfer, flatness at `3` — Fontaine–Laffaille**
(DECOMPOSED 2026-07-24 — now a PROVEN transport over
`threeadicRealization_hasFlatProlongationAt_of_finite_quotient` above,
itself PROVEN glue (2026-07-25) over the literature joint
`threeadicRealization_hasFlatProlongationAt_threePow` and the Raynaud
quotient brick `hasFlatProlongationAt_of_surjective`): the
Brauer-descended `3`-adic member is flat at `3` in the
project's sense `GaloisRep.IsFlatAt` — every OPEN-ideal congruence
quotient of `τ` has a finite flat prolongation at `3`.

TRANSPORT (PROVEN here — the open-ideal quantifier of
`GaloisRep.IsFlatAt.cond` reduced to the literature's finite-quotient
form):

* `I = ⊤`: the congruence quotient `(A ⧸ ⊤) ⊗_A (Fin 2 → A)` is a
  module over the zero ring, hence a single point, and
  `GaloisRep.hasFlatProlongationAt_of_subsingleton` provides the
  prolongation with the trivial Hopf algebra `𝒪ᵥ` — no literature
  input;
* `I ≠ ⊤`: the coefficient ring `A` is finite FREE over `ℤ_3` with its
  module topology, so a `ℤ_3`-basis is a homeomorphism `A ≃ₜ ℤ_3ⁿ`
  (`IsModuleTopology.continuous_of_linearMap` both ways), making `A` a
  COMPACT HAUSDORFF Noetherian local topological ring
  (`IsNoetherianRing.of_finite`). For such a ring an ideal is open iff
  its quotient is finite (`IsLocalRing.isOpen_iff_finite_quotient`),
  which is exactly the hypothesis of the local-shape leaf.

Classically the mathematical content is: the system has parallel
weight `2` and conductor prime to `3`, so its `3`-adic member is
crystalline at `3` with Hodge–Tate weights `{0, 1}`, and over `ℤ_3`
(`e = 1 < p - 1 = 2`) Fontaine–Laffaille/Raynaud make every finite
quotient of the stable lattice the generic fibre of a finite flat
group scheme; see the leaf's docstring for the literature.

ROUTE AUDIT (2026-07-24, the dichotomy route): the collapse route that
discharges pillar 2's interface leaf — `absurd hirr` against the
headline `not_isIrreducible_of_isHardlyRamified_of_five_le` — is NOT
available here and must not be used. The headline is PROVEN over
pillar β, pillar β over `exists_threeadic_member_of_witness`, and that
assembly consumes THIS node; discharging this node by the headline
would close a literal dependency cycle (and is rejected by Lean, the
headline being declared below). The same audit applies to the three
sibling condition-transfer leaves. The only sound discharge is the
direct one — the Fontaine–Laffaille local shape, cut above.

SOUNDNESS AUDIT (both ways, 2026-07-24): (i) direct — for the
realization produced by the construction leaf this is
Fontaine–Laffaille/Raynaud plus the transport proven here; for an
abstract realization the abstract-quantification caveat of pillar β
applies, and (ii) collapse — the hypothesis set is classically
unsatisfiable (headline below), so the statement is classically true
for every package.

CIRCULARITY GUARD (inherited from pillar β, load-bearing): no
discharge through `Family.lean`, `Lift.lean`, or
`Modularity/Interface.lean`. The two proof-only imports this transport
adds (`FlatProlongation`, `Mathlib.Topology.Algebra.Ring.Compact`) are
Family-free. -/
theorem threeadicRealization_isFlat_of_witness
    {ℓ : ℕ} (hℓodd : Odd ℓ) [Fact ℓ.Prime] (hℓ5 : 5 ≤ ℓ)
    {O : Type u} [CommRing O] [IsDomain O] [TopologicalSpace O]
    [IsTopologicalRing O] [Algebra ℤ_[ℓ] O] [IsLocalRing O]
    [Module.Finite ℤ_[ℓ] O] [IsModuleTopology ℤ_[ℓ] O]
    (hZinj : Function.Injective (algebraMap ℤ_[ℓ] O))
    {ρ : GaloisRep ℚ O (Fin 2 → O)}
    (hrank : Module.rank O (Fin 2 → O) = 2)
    (hρ : IsHardlyRamified hℓodd hrank ρ)
    {k : Type u} [Field k] [Finite k] [Algebra ℤ_[ℓ] k]
    [TopologicalSpace k] [DiscreteTopology k]
    {W : Type v} [AddCommGroup W] [Module k W] [Module.Finite k W]
    [Module.Free k W]
    (hW : Module.rank k W = 2) {ρbar : GaloisRep ℚ k W}
    (hρbar : IsHardlyRamified hℓodd hW ρbar)
    (hirr : ρbar.IsIrreducible)
    (π : O →+* k) (hπsurj : Function.Surjective π)
    (hπ : ∀ (q : ℕ) (hq : q.Prime), q ≠ 2 → q ≠ ℓ →
      (ρ.charFrob hq.toHeightOneSpectrumRingOfIntegersRat).map π =
        ρbar.charFrob hq.toHeightOneSpectrumRingOfIntegersRat)
    {Wit : PotentialModularityWitness ℓ O ρ}
    (Rlz : ThreeadicRealization ℓ O ρ Wit) :
    Rlz.τ.IsFlatAt
      (Nat.Prime.toHeightOneSpectrumRingOfIntegersRat
        (Fact.out : Nat.Prime 3)) := by
  classical
  constructor
  intro I hIopen
  rcases eq_or_ne I ⊤ with rfl | hItop
  · -- `I = ⊤`: the congruence quotient is a single point
    haveI : Subsingleton (Rlz.A ⧸ (⊤ : Ideal Rlz.A)) :=
      Ideal.Quotient.subsingleton_iff.mpr rfl
    haveI : Subsingleton
        (TensorProduct Rlz.A (Rlz.A ⧸ (⊤ : Ideal Rlz.A)) (Fin 2 → Rlz.A)) :=
      Module.subsingleton (Rlz.A ⧸ (⊤ : Ideal Rlz.A)) _
    exact GaloisRep.hasFlatProlongationAt_of_subsingleton _
      (Rlz.τ.baseChange (Rlz.A ⧸ (⊤ : Ideal Rlz.A)))
  · -- `I ≠ ⊤`: openness upgrades to finiteness of the quotient, the
    -- form the Fontaine–Laffaille leaf consumes
    haveI hNoeth : IsNoetherianRing Rlz.A := IsNoetherianRing.of_finite ℤ_[3] Rlz.A
    -- a `ℤ_3`-basis is a homeomorphism `A ≃ₜ ℤ_3ⁿ`
    let eA : Rlz.A ≃ₗ[ℤ_[3]] (Module.Free.ChooseBasisIndex ℤ_[3] Rlz.A → ℤ_[3]) :=
      (Module.Free.chooseBasis ℤ_[3] Rlz.A).equivFun
    have hcont₁ : Continuous eA :=
      IsModuleTopology.continuous_of_linearMap eA.toLinearMap
    have hcont₂ : Continuous eA.symm :=
      IsModuleTopology.continuous_of_linearMap eA.symm.toLinearMap
    let homA : Rlz.A ≃ₜ (Module.Free.ChooseBasisIndex ℤ_[3] Rlz.A → ℤ_[3]) :=
      { toEquiv := eA.toEquiv
        continuous_toFun := hcont₁
        continuous_invFun := hcont₂ }
    haveI : CompactSpace Rlz.A := homA.symm.compactSpace
    haveI : T2Space Rlz.A := homA.symm.symm.isEmbedding.t2Space
    have hIfin : Finite (Rlz.A ⧸ I) :=
      IsLocalRing.isOpen_iff_finite_quotient.mp hIopen
    exact threeadicRealization_hasFlatProlongationAt_of_finite_quotient
      hℓodd hℓ5 hZinj hrank hρ hW hρbar hirr π hπsurj hπ Rlz I hItop hIfin

set_option linter.unusedVariables false in
/-- **The Weil–Deligne type at `2` of the `3`-adic member, as a stable
line with unramified quadratic quotient** (PROVEN 2026-07-25 by the
CUT-LEVEL REPAIR — now a one-line projection of the
`ThreeadicRealization` field `stableLineAtTwo`): there are an `A`-basis
`b` of the stable lattice `Fin 2 → A` and an unramified square-trivial
character `δ` of `G_{ℚ_2}` such that `G_{ℚ_2}` acts on the quotient of
the lattice by the line `A · b 0` through `δ`:

  `τ g v ≡ δ g 1 • v  (mod A · b 0)`  for all `g` and all `v`.

REPAIR NOTE (2026-07-25 — read this before treating the name as a
frontier node; it is no longer one). This WAS the shrunk literature
joint of the tameness transfer, and it was UNDISCHARGEABLE as
quantified, for the reason recorded at its flatness sibling
`threeadicRealization_hasFlatProlongationAt_threePow` and applied at `2`
instead of `3`: over an arbitrary `Rlz : ThreeadicRealization` the only
constraint on `τ` is `compat`, which equates characteristic polynomials
of Frobenius at unramified places `q ∉ {2, 3, ℓ}` and therefore says
NOTHING at `2`, let alone anything about inertia at `2`.

The local type at `2` is therefore now a FIELD of the interface
(`ThreeadicRealization.stableLineAtTwo`), supplied at the construction
site out of clause (3) of `blggt_threeadicBrauerSum_of_witness` — which
is where the strict-compatibility discussion and the Carayol/BLGGT
literature now live. Read that docstring, not this one, for the
mathematics. (Between 2026-07-25 and 2026-07-26 that content sat in a
separate leaf, `blggt_threeadicMember_stableLineAtTwo`; it was absorbed
into the Brauer-sum citation and deleted.)

This declaration is kept, with its signature unchanged, purely so that
its consumer `threeadicRealization_weilDeligneType_two_of_witness` and
the downstream tameness transfer need no edit; its hypotheses beyond
`Rlz` are consequently unused, hence the `linter.unusedVariables`
suppression above.

SOUNDNESS: inherited verbatim from the field, hence from clause (3) of
`blggt_threeadicBrauerSum_of_witness`.

CIRCULARITY GUARD (inherited from pillar β, load-bearing): respected —
the only input is a field of the interface; nothing routes through
`Family.lean`, `Lift.lean`, or `Modularity/Interface.lean`. -/
theorem threeadicRealization_stableLineAtTwo_of_witness
    {ℓ : ℕ} (hℓodd : Odd ℓ) [Fact ℓ.Prime] (hℓ5 : 5 ≤ ℓ)
    {O : Type u} [CommRing O] [IsDomain O] [TopologicalSpace O]
    [IsTopologicalRing O] [Algebra ℤ_[ℓ] O] [IsLocalRing O]
    [Module.Finite ℤ_[ℓ] O] [IsModuleTopology ℤ_[ℓ] O]
    (hZinj : Function.Injective (algebraMap ℤ_[ℓ] O))
    {ρ : GaloisRep ℚ O (Fin 2 → O)}
    (hrank : Module.rank O (Fin 2 → O) = 2)
    (hρ : IsHardlyRamified hℓodd hrank ρ)
    {k : Type u} [Field k] [Finite k] [Algebra ℤ_[ℓ] k]
    [TopologicalSpace k] [DiscreteTopology k]
    {W : Type v} [AddCommGroup W] [Module k W] [Module.Finite k W]
    [Module.Free k W]
    (hW : Module.rank k W = 2) {ρbar : GaloisRep ℚ k W}
    (hρbar : IsHardlyRamified hℓodd hW ρbar)
    (hirr : ρbar.IsIrreducible)
    (π : O →+* k) (hπsurj : Function.Surjective π)
    (hπ : ∀ (q : ℕ) (hq : q.Prime), q ≠ 2 → q ≠ ℓ →
      (ρ.charFrob hq.toHeightOneSpectrumRingOfIntegersRat).map π =
        ρbar.charFrob hq.toHeightOneSpectrumRingOfIntegersRat)
    {Wit : PotentialModularityWitness ℓ O ρ}
    (Rlz : ThreeadicRealization ℓ O ρ Wit) :
    ∃ (b : Module.Basis (Fin 2) Rlz.A (Fin 2 → Rlz.A))
      (δ : GaloisRep ℚ_[2] Rlz.A Rlz.A),
      (AddSubgroup.inertia
          ((IsLocalRing.maximalIdeal Z2bar).toAddSubgroup :
            AddSubgroup Z2bar)
          (Field.absoluteGaloisGroup ℚ_[2]) ≤ δ.ker) ∧
      (∀ g : Field.absoluteGaloisGroup ℚ_[2], δ g * δ g = 1) ∧
      ∀ (g : Field.absoluteGaloisGroup ℚ_[2]) (v : Fin 2 → Rlz.A),
        Rlz.τ.map (algebraMap ℚ ℚ_[2]) g v - δ g 1 • v ∈
          Submodule.span Rlz.A {b 0} :=
  Rlz.stableLineAtTwo

/-- **The Weil–Deligne type at `2` of the `3`-adic member, in lattice
coordinates** (DECOMPOSED 2026-07-25 — now a PROVEN transport over the
shrunk literature joint `threeadicRealization_stableLineAtTwo_of_witness`
above): there is an `A`-basis of the stable lattice `Fin 2 → A` in which
the whole decomposition group at `2` acts through UPPER-triangular
matrices, the diagonal `(1,1)`-entry being the scalar `δ g 1` of an
unramified square-trivial character `δ` of `G_{ℚ_2}`.

CITATION-SHRINKING AUDIT (2026-07-25). The old sorry here bundled two
unrelated things: (a) the genuine literature input — constancy of the
local Weil–Deligne type at `2` across the compatible system, i.e. the
existence of a `G_{ℚ_2}`-stable saturated line in the lattice whose
quotient carries an unramified quadratic character — and (b) the
representation-theoretic bookkeeping turning that description into
matrix entries in an adapted basis. (b) is FORMAL at this pin and is
proven below; only (a) remains a citation, and it is now stated with no
matrices in it (`threeadicRealization_stableLineAtTwo_of_witness`).

ASSEMBLY (PROVEN). Both matrix clauses are the `1`-st coordinate of
`b.repr` applied to the joint's congruence
`τ g v ≡ δ g 1 • v (mod A · b 0)` — `LinearMap.toMatrix_apply` reads
the `(i, j)` entry as `b.repr (f (b j)) i`, and `b.repr` kills the line
`A · b 0` at the index `1` (`b.repr (c • b 0) 1 = c * 0`):

* `j = 0`: the congruence at `v = b 0` puts `τ g (b 0)` itself in the
  line (`δ g 1 • b 0` is in the line, and the line is a submodule), so
  the `(1,0)` entry vanishes — this is the stability of the line;
* `j = 1`: the congruence at `v = b 1` writes
  `τ g (b 1) = c • b 0 + δ g 1 • b 1`, whose `b.repr … 1` is
  `c * 0 + δ g 1 * 1 = δ g 1` — this is the diagonal clause.

The unramifiedness and square-triviality clauses are the joint's own,
`δ` being unchanged by the transport.

SOUNDNESS: inherited verbatim from the joint (both the direct reading
and the collapse reading; see its docstring).

CIRCULARITY GUARD (inherited from pillar β, load-bearing): respected —
the only leaf consumed is the joint above, which carries the same
guard; nothing routes through `Family.lean`, `Lift.lean`, or
`Modularity/Interface.lean`. -/
theorem threeadicRealization_weilDeligneType_two_of_witness
    {ℓ : ℕ} (hℓodd : Odd ℓ) [Fact ℓ.Prime] (hℓ5 : 5 ≤ ℓ)
    {O : Type u} [CommRing O] [IsDomain O] [TopologicalSpace O]
    [IsTopologicalRing O] [Algebra ℤ_[ℓ] O] [IsLocalRing O]
    [Module.Finite ℤ_[ℓ] O] [IsModuleTopology ℤ_[ℓ] O]
    (hZinj : Function.Injective (algebraMap ℤ_[ℓ] O))
    {ρ : GaloisRep ℚ O (Fin 2 → O)}
    (hrank : Module.rank O (Fin 2 → O) = 2)
    (hρ : IsHardlyRamified hℓodd hrank ρ)
    {k : Type u} [Field k] [Finite k] [Algebra ℤ_[ℓ] k]
    [TopologicalSpace k] [DiscreteTopology k]
    {W : Type v} [AddCommGroup W] [Module k W] [Module.Finite k W]
    [Module.Free k W]
    (hW : Module.rank k W = 2) {ρbar : GaloisRep ℚ k W}
    (hρbar : IsHardlyRamified hℓodd hW ρbar)
    (hirr : ρbar.IsIrreducible)
    (π : O →+* k) (hπsurj : Function.Surjective π)
    (hπ : ∀ (q : ℕ) (hq : q.Prime), q ≠ 2 → q ≠ ℓ →
      (ρ.charFrob hq.toHeightOneSpectrumRingOfIntegersRat).map π =
        ρbar.charFrob hq.toHeightOneSpectrumRingOfIntegersRat)
    {Wit : PotentialModularityWitness ℓ O ρ}
    (Rlz : ThreeadicRealization ℓ O ρ Wit) :
    ∃ (b : Module.Basis (Fin 2) Rlz.A (Fin 2 → Rlz.A))
      (δ : GaloisRep ℚ_[2] Rlz.A Rlz.A),
      (AddSubgroup.inertia
          ((IsLocalRing.maximalIdeal Z2bar).toAddSubgroup :
            AddSubgroup Z2bar)
          (Field.absoluteGaloisGroup ℚ_[2]) ≤ δ.ker) ∧
      (∀ g : Field.absoluteGaloisGroup ℚ_[2], δ g * δ g = 1) ∧
      ∀ g : Field.absoluteGaloisGroup ℚ_[2],
        LinearMap.toMatrix b b
            (Rlz.τ.map (algebraMap ℚ ℚ_[2]) g) 1 0 = 0 ∧
        LinearMap.toMatrix b b
            (Rlz.τ.map (algebraMap ℚ ℚ_[2]) g) 1 1 = δ g 1 := by
  classical
  -- the shrunk literature joint: a stable line with unramified
  -- square-trivial quotient character, stated without coordinates
  obtain ⟨b, δ, hδur, hδsq, hquot⟩ :=
    threeadicRealization_stableLineAtTwo_of_witness hℓodd hℓ5 hZinj
      hrank hρ hW hρbar hirr π hπsurj hπ Rlz
  refine ⟨b, δ, hδur, hδsq, fun g => ⟨?_, ?_⟩⟩
  · -- `(1,0)`: the congruence at `v = b 0` puts `τ g (b 0)` in the line
    have hstab : Rlz.τ.map (algebraMap ℚ ℚ_[2]) g (b 0) ∈
        Submodule.span Rlz.A {b 0} := by
      have hline : δ g 1 • b 0 ∈ Submodule.span Rlz.A ({b 0} : Set (Fin 2 → Rlz.A)) :=
        Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
      simpa using Submodule.add_mem _ (hquot g (b 0)) hline
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hstab
    rw [LinearMap.toMatrix_apply, ← hc]
    simp
  · -- `(1,1)`: the congruence at `v = b 1`, read at the index `1`
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp (hquot g (b 1))
    have hval : Rlz.τ.map (algebraMap ℚ ℚ_[2]) g (b 1) =
        c • b 0 + δ g 1 • b 1 := by
      rw [hc]; abel
    rw [LinearMap.toMatrix_apply, hval]
    simp

/-- **Condition transfer, tameness at `2` — constant Weil–Deligne
type** (DECOMPOSED 2026-07-24 — now a PROVEN transport over the
literature joint `threeadicRealization_weilDeligneType_two_of_witness`
above): the Brauer-descended `3`-adic member is tame at
`2` in the hardly ramified sense: it has a surjective rank-1 quotient
on which `G_{ℚ_2}` acts through an unramified square-trivial
character. Classically: the Weil–Deligne parameter at `2` is constant
in a strictly compatible system away from the residue characteristic
(Khare–Wintenberger (I) §5; here `2 ≠ 3`), and equals that of the
hardly ramified `ρ` — whose type at `2` is exactly "extension of an
unramified square-trivial character by its cyclotomic twist"
(`hρ.isTameAtTwo`); transporting the parameter back into the stable
lattice (the rank-1 quotient of the lattice is the lattice of the
rank-1 quotient, after the stable-lattice normalization of the
construction leaf) produces the surjection `πq`, the unramified
character `δ` with `δ² = 1`, and the equivariance clause.

Literature: Khare–Wintenberger, *Serre's modularity conjecture (I)*,
Invent. Math. 178 (2009), §5 (strict compatibility of Weil–Deligne
parameters away from the residue characteristic); BLGGT §5.5;
Carayol, Ann. Sci. ÉNS 19 (1986) (local-global compatibility at the
bad places). FLT blueprint ch. 4: "tame at 2".

SOUNDNESS AUDIT (both ways, 2026-07-24): (i) direct — for the
realization produced by the construction leaf this is the
Weil–Deligne-type transfer above; for an abstract realization the
abstract-quantification caveat of pillar β applies, and (ii) collapse
— the hypothesis set is classically unsatisfiable (headline below),
so the statement is classically true for every package.

ROUTE AUDIT (2026-07-24). Two routes were weighed for this leaf.

* The **shared odd-prime dichotomy** — the route discharging the
  sibling transfer leaves of `Modularity/Interface.lean`
  (`isTameAtTwo_of_isRealizationCompatible` and friends, all of the
  form `absurd hirr (not_isIrreducible_of_isHardlyRamified_of_odd …)`)
  — is NOT available here, and the obstruction is circularity, not
  taste: `not_isIrreducible_of_isHardlyRamified_of_odd` routes `ℓ ≥ 5`
  through the headline `not_isIrreducible_of_isHardlyRamified_of_five_le`
  of THIS module, whose proof consumes pillar β
  (`exists_threeadic_compatible_member_of_five_le` →
  `exists_threeadic_member_of_witness`) and hence consumes this very
  leaf. Discharging the leaf by the dichotomy would close the loop
  `isTameAtTwo → threeadic member → pillar β → headline → isTameAtTwo`;
  Lean rejects it outright (the headline is declared below), and it
  would be vicious even if it were not. The vacuity of the hypothesis
  package therefore records the leaf's soundness but cannot be spent
  as its proof.
* The **literature-joint cut** taken here: keep the mathematical
  content in the citation `threeadicRealization_weilDeligneType_two_of_witness`
  (the constancy of the Weil–Deligne type at `2` across the system,
  read in lattice coordinates) and PROVE the transport from that type
  description to this in-tree tame-at-`2` predicate.

ASSEMBLY (2026-07-24, PROVEN transport): the joint supplies a basis
`b` of the lattice in which every `g ∈ G_{ℚ_2}` acts by an
upper-triangular matrix with `(1,1)`-entry `δ g 1`. The quotient
functional is the second coordinate `b.coord 1` — surjective because
`b.coord 1 (a • b 1) = a` — and the equivariance clause is the
`(1,·)`-row of `LinearMap.toMatrix_mulVec_repr`: the vanishing of the
lower-left entry kills the `b 0`-contribution, leaving
`b.repr (τ g v) 1 = (δ g 1) * b.repr v 1 = δ g (b.repr v 1)` (a
`Rlz.A`-endomorphism of `Rlz.A` is multiplication by its value at
`1`). The unramifiedness and square-triviality clauses are the joint's
own, `δ` being unchanged by the transport.

CIRCULARITY GUARD (inherited from pillar β, load-bearing): respected —
the only leaf consumed is the literature joint above, which carries the
same guard; nothing routes through `Family.lean`, `Lift.lean`, or
`Modularity/Interface.lean`. -/
theorem threeadicRealization_isTameAtTwo_of_witness
    {ℓ : ℕ} (hℓodd : Odd ℓ) [Fact ℓ.Prime] (hℓ5 : 5 ≤ ℓ)
    {O : Type u} [CommRing O] [IsDomain O] [TopologicalSpace O]
    [IsTopologicalRing O] [Algebra ℤ_[ℓ] O] [IsLocalRing O]
    [Module.Finite ℤ_[ℓ] O] [IsModuleTopology ℤ_[ℓ] O]
    (hZinj : Function.Injective (algebraMap ℤ_[ℓ] O))
    {ρ : GaloisRep ℚ O (Fin 2 → O)}
    (hrank : Module.rank O (Fin 2 → O) = 2)
    (hρ : IsHardlyRamified hℓodd hrank ρ)
    {k : Type u} [Field k] [Finite k] [Algebra ℤ_[ℓ] k]
    [TopologicalSpace k] [DiscreteTopology k]
    {W : Type v} [AddCommGroup W] [Module k W] [Module.Finite k W]
    [Module.Free k W]
    (hW : Module.rank k W = 2) {ρbar : GaloisRep ℚ k W}
    (hρbar : IsHardlyRamified hℓodd hW ρbar)
    (hirr : ρbar.IsIrreducible)
    (π : O →+* k) (hπsurj : Function.Surjective π)
    (hπ : ∀ (q : ℕ) (hq : q.Prime), q ≠ 2 → q ≠ ℓ →
      (ρ.charFrob hq.toHeightOneSpectrumRingOfIntegersRat).map π =
        ρbar.charFrob hq.toHeightOneSpectrumRingOfIntegersRat)
    {Wit : PotentialModularityWitness ℓ O ρ}
    (Rlz : ThreeadicRealization ℓ O ρ Wit) :
    ∃ (πq : (Fin 2 → Rlz.A) →ₗ[Rlz.A] Rlz.A)
      (_ : Function.Surjective πq) (δ : GaloisRep ℚ_[2] Rlz.A Rlz.A),
      ∀ (g : Field.absoluteGaloisGroup ℚ_[2]) (v : Fin 2 → Rlz.A),
        πq (Rlz.τ.map (algebraMap ℚ ℚ_[2]) g v) = δ g (πq v) ∧
        (AddSubgroup.inertia
            ((IsLocalRing.maximalIdeal Z2bar).toAddSubgroup :
              AddSubgroup Z2bar)
            (Field.absoluteGaloisGroup ℚ_[2]) ≤ δ.ker) ∧
        (∀ g' : Field.absoluteGaloisGroup ℚ_[2], δ g' * δ g' = 1) := by
  classical
  -- the literature joint: the constant Weil–Deligne type at `2`, read
  -- in a basis of the stable lattice
  obtain ⟨b, δ, hδur, hδsq, hshape⟩ :=
    threeadicRealization_weilDeligneType_two_of_witness hℓodd hℓ5 hZinj
      hrank hρ hW hρbar hirr π hπsurj hπ Rlz
  refine ⟨b.coord 1, fun a => ⟨a • b 1, by simp⟩, δ, fun g v => ⟨?_, hδur, hδsq⟩⟩
  -- the `(1,·)`-row of the matrix identity `M *ᵥ b.repr v = b.repr (τ g v)`
  have hM := LinearMap.toMatrix_mulVec_repr b b
    (Rlz.τ.map (algebraMap ℚ ℚ_[2]) g) v
  have hrow : b.repr (Rlz.τ.map (algebraMap ℚ ℚ_[2]) g v) 1 =
      b.repr v 1 * δ g 1 := by
    rw [← hM]
    simp only [Matrix.mulVec_apply_eq_sum, Fin.sum_univ_two, (hshape g).1,
      (hshape g).2, zero_mul, zero_add]
    exact mul_comm _ _
  -- an `A`-endomorphism of `A` is multiplication by its value at `1`
  have hscal : δ g (b.repr v 1) = b.repr v 1 * δ g 1 := by
    conv_lhs => rw [show (b.repr v 1 : Rlz.A) = b.repr v 1 • (1 : Rlz.A) by
      rw [smul_eq_mul, mul_one]]
    rw [map_smul, smul_eq_mul]
  rw [Module.Basis.coord_apply, Module.Basis.coord_apply, hrow, hscal]

/-- **Brauer descent, `3`-adic side — the hardly ramified `3`-adic
member over `ℚ`** (DECOMPOSED 2026-07-24 — now a PROVEN assembly over
the `3`-adic realization carrier `ThreeadicRealization`; the depth
now lives in the five sorried leaves above: the raw Brauer-descent
construction and the four per-condition transfers of BLGGT Theorem
5.5.1): given a potential-modularity carrier
for the lift `ρ`, the compatible system it generates has a `3`-adic
member over `ℚ`: a representation `τ` on a coefficient package `A` (a
local ring, finite FREE over `ℤ_3` — what the proven `3`-adic
classification consumes) which is hardly ramified `3`-adic and whose
Frobenius characteristic polynomials agree with those of `ρ` through
the Hecke field: whenever `P ∈ E[X]` interpolates `charFrob ρ` at `q`
through `ψℓ` (such a `P` is unique, `ψℓ` being injective on the field
`E`), then `τ`'s characteristic polynomial at `q` is `P` through
`ψ₃`.

Classically `τ` is the Brauer virtual sum
`Σ nᵢ · Ind_{G_{Fᵢ}}^{G_ℚ} (τ_{fᵢ,λ} ⊗ χᵢ)` at the place `λ | 3` of
the Hecke field — a TRUE representation, not merely virtual (BLGGT
§5.3: the virtual character is a true character because at the place
over `ℓ` it is the character of `ρ`; Brauer–Nesbitt then pins the
semisimple representation at every `λ`). Its hardly ramified
conditions transfer along strict compatibility: cyclotomic
determinant across the system; unramified outside `{2,3}` since the
system's conductor divides `2` (Khare–Wintenberger (I) §5, strict
compatibility away from the residue characteristic); FLAT at `3` by
Fontaine–Laffaille theory (weight `2`, `3` prime to the conductor —
Fontaine–Laffaille, *Construction de représentations p-adiques*,
Ann. Sci. ÉNS 15 (1982); the blueprint's "flat at 3"); tame at `2`
with an unramified square-trivial rank-1 quotient — the Weil–Deligne
type at `2` is constant in the system and equals that of the hardly
ramified `ρ` (the blueprint's "tame at 2"). The lattice normalization
(a stable lattice finite free over `ℤ_3` inside the
`E_λ`-representation) yields the package `A` with an injective
continuous coefficient embedding `ιA` into `ℚ̄_3`.

Literature: Barnet-Lamb–Gee–Geraghty–Taylor, *Potential automorphy
and change of weight*, Ann. of Math. 179 (2014), §5.3 and Theorem
5.5.1 (compatible systems attached to potentially automorphic
representations via the Brauer trick); Khare–Wintenberger, *Serre's
modularity conjecture (I)*, Invent. Math. 178 (2009), §5; Taylor,
*Remarks on a conjecture of Fontaine and Mazur*, J. Inst. Math.
Jussieu 1 (2002), §6; Fontaine–Laffaille (1982). FLT blueprint
ch. 4: "look at the 3-adic specialisation of this family … flat at 3
and tame at 2".

SOUNDNESS AUDIT (both ways, 2026-07-24): (i) direct — for the carrier
produced by the inhabitation leaf this is BLGGT §5.5 + the local
transfers above; for an abstract carrier the abstract-quantification
caveat of pillar β applies, and (ii) collapse — the hypothesis set is
classically unsatisfiable (headline below), so the statement is
classically true for every package.

ASSEMBLY (2026-07-24, PROVEN): the construction leaf
(`exists_threeadicRealization_of_witness`) supplies the realization
`Rlz` — coefficient package, representation `τ`, embedding `ιA`,
exceptional set and compatibility clause — the rank clause is the
standard computation (`rank_finTwoFun`), and the four hardly ramified
fields are exactly the four condition-transfer leaves
(`threeadicRealization_det_cyclotomic_of_witness`,
`threeadicRealization_isUnramified_of_witness`,
`threeadicRealization_isFlat_of_witness`,
`threeadicRealization_isTameAtTwo_of_witness`). Those five leaves are
now the residual sorries of this node; the circularity guard binds
each of them.

CIRCULARITY GUARD (inherited from pillar β, load-bearing): no
discharge through `Family.lean`, `Lift.lean`, or
`Modularity/Interface.lean`. -/
theorem exists_threeadic_member_of_witness
    {ℓ : ℕ} (hℓodd : Odd ℓ) [Fact ℓ.Prime] (hℓ5 : 5 ≤ ℓ)
    {O : Type u} [CommRing O] [IsDomain O] [TopologicalSpace O]
    [IsTopologicalRing O] [Algebra ℤ_[ℓ] O] [IsLocalRing O]
    [Module.Finite ℤ_[ℓ] O] [IsModuleTopology ℤ_[ℓ] O]
    (hZinj : Function.Injective (algebraMap ℤ_[ℓ] O))
    {ρ : GaloisRep ℚ O (Fin 2 → O)}
    (hrank : Module.rank O (Fin 2 → O) = 2)
    (hρ : IsHardlyRamified hℓodd hrank ρ)
    {k : Type u} [Field k] [Finite k] [Algebra ℤ_[ℓ] k]
    [TopologicalSpace k] [DiscreteTopology k]
    {W : Type v} [AddCommGroup W] [Module k W] [Module.Finite k W]
    [Module.Free k W]
    (hW : Module.rank k W = 2) {ρbar : GaloisRep ℚ k W}
    (hρbar : IsHardlyRamified hℓodd hW ρbar)
    (hirr : ρbar.IsIrreducible)
    (π : O →+* k) (hπsurj : Function.Surjective π)
    (hπ : ∀ (q : ℕ) (hq : q.Prime), q ≠ 2 → q ≠ ℓ →
      (ρ.charFrob hq.toHeightOneSpectrumRingOfIntegersRat).map π =
        ρbar.charFrob hq.toHeightOneSpectrumRingOfIntegersRat)
    (Wit : PotentialModularityWitness ℓ O ρ) :
    ∃ (S₁ : Finset (HeightOneSpectrum (NumberField.RingOfIntegers ℚ)))
      (A : Type u) (_ : CommRing A) (_ : TopologicalSpace A)
      (_ : IsTopologicalRing A) (_ : Algebra ℤ_[3] A) (_ : IsLocalRing A)
      (_ : Module.Finite ℤ_[3] A) (_ : Module.Free ℤ_[3] A)
      (_ : IsModuleTopology ℤ_[3] A)
      (τ : GaloisRep ℚ A (Fin 2 → A))
      (hrankA : Module.rank A (Fin 2 → A) = 2)
      (_ : IsHardlyRamified (show Odd 3 by decide) hrankA τ)
      (ιA : A →+* AlgebraicClosure ℚ_[3]) (_ : Function.Injective ιA),
      ∀ (q : ℕ) (hq : q.Prime),
        hq.toHeightOneSpectrumRingOfIntegersRat ∉ S₁ →
        q ≠ 2 → q ≠ 3 → q ≠ ℓ →
        ∀ P : Polynomial Wit.E,
          (ρ.charFrob hq.toHeightOneSpectrumRingOfIntegersRat).map Wit.ιO =
            P.map Wit.ψℓ →
          (τ.charFrob hq.toHeightOneSpectrumRingOfIntegersRat).map ιA =
            P.map Wit.ψ₃ := by
  classical
  -- the raw Brauer-descended realization (BLGGT §5.3)
  obtain ⟨Rlz⟩ :=
    exists_threeadicRealization_of_witness hℓodd hℓ5 hZinj hrank hρ hW
      hρbar hirr π hπsurj hπ Wit
  -- the standard rank computation for the free rank-2 module
  have hrankA : Module.rank Rlz.A (Fin 2 → Rlz.A) = 2 :=
    rank_finTwoFun Rlz.A
  refine ⟨Rlz.S₁, Rlz.A, Rlz.commRingA, Rlz.topologicalSpaceA,
    Rlz.isTopologicalRingA, Rlz.algebraA, Rlz.isLocalRingA,
    Rlz.moduleFiniteA, Rlz.moduleFreeA, Rlz.isModuleTopologyA, Rlz.τ,
    hrankA, ?_, Rlz.ιA, Rlz.ιA_injective, Rlz.compat⟩
  -- the four hardly ramified fields are the four transfer leaves
  exact
    { det := threeadicRealization_det_cyclotomic_of_witness hℓodd hℓ5
        hZinj hrank hρ hW hρbar hirr π hπsurj hπ Rlz
      isUnramified := threeadicRealization_isUnramified_of_witness
        hℓodd hℓ5 hZinj hrank hρ hW hρbar hirr π hπsurj hπ Rlz
      isFlat := threeadicRealization_isFlat_of_witness hℓodd hℓ5 hZinj
        hrank hρ hW hρbar hirr π hπsurj hπ Rlz
      isTameAtTwo := threeadicRealization_isTameAtTwo_of_witness hℓodd
        hℓ5 hZinj hrank hρ hW hρbar hirr π hπsurj hπ Rlz }

/-- **Pillar β — the compatible system and its `3`-adic member**
(PROVEN 2026-07-24 as an assembly over the potential-modularity
carrier; the potential-modularity content — the genuine depth of the
residual-modularity leaf — now lives in the carrier's three sorried
leaves): a hardly ramified `ℓ`-adic lift (as produced
by pillar α) of an irreducible hardly ramified mod-`ℓ` representation,
`ℓ ≥ 5`, lies in a compatible system: there are a number field `E`, a
family `Pv` of `E`-coefficient polynomials indexed by the places of `ℚ`,
and embeddings identifying `Pv` at almost all places both with the
Frobenius characteristic polynomials of `ρ` (through `ψℓ`, `ιO` into
`ℚ̄_ℓ`) and with those of a hardly ramified `3`-ADIC representation `τ`
(through `ψ₃`, `ιA` into `ℚ̄_3`) over a coefficient package `A` of the
same characteristic-zero shape — in particular `ℤ_3`-FREE, as the
integers of a finite extension of `ℚ_3` are, which is what the proven
`3`-adic classification consumes.

Classically the `3`-adic member is hardly ramified because strict
compatibility transports the type: the conductor divides `2` and the
determinant is cyclotomic across the family; flatness at `3` holds by
Fontaine–Laffaille theory (weight 2, `3` prime to the conductor); the
tame unramified square-trivial rank-1 quotient at `2` is the fixed
Weil–Deligne type at `2`.

Literature: Khare–Wintenberger, *Serre's modularity conjecture (I)*,
Invent. Math. 178 (2009), §5 (the lift is part of a strictly compatible
system — via potential modularity and Brauer's theorem, following
Dieulefait and Taylor); Barnet-Lamb–Gee–Geraghty–Taylor, *Potential
automorphy and change of weight*, Ann. of Math. 179 (2014), §5 (the
Brauer-trick construction of compatible systems attached to potentially
automorphic representations); Taylor, *Remarks on a conjecture of
Fontaine and Mazur*, J. Inst. Math. Jussieu 1 (2002) (potential
modularity via Moret–Bailly). FLT blueprint ch. 4: "put it into an
`ℓ`-adic family using the Brauer's theorem trick … and look at the
`3`-adic specialisation".

SOUNDNESS AUDIT (both ways, 2026-07-24): (i) direct — for the intended
instantiation (pillar α's package, the KW minimal lift) this is KW (I)
§5 verbatim; for an abstract package `(O, ρ, π)` not arising from that
construction the literature statement does not directly apply
(abstract-quantification caveat, same as the interface's pillar 3b),
but (ii) collapse — the hypothesis set includes an irreducible hardly
ramified mod-`ℓ` representation with `ℓ ≥ 5`, classically unsatisfiable
(headline below), so the statement is classically true for every
package.

CIRCULARITY GUARD (load-bearing, stronger than the usual note): the
in-tree twin of this pillar is `Family.lean`'s `mem_isCompatible`
composed with `Lift.lean`'s `residual_charFrob_eq_of_family` — but
`mem_isCompatible` is proven THROUGH the modularity interface (the
compatible family is extracted from the eigenform attached by the
interface's assemblies), i.e. through the consumer of the leaf this
module discharges. Porting that proof here would close the cycle. The
ONLY sound discharges of this pillar are the genuinely independent
constructions: KW (I) §5, or the blueprint's potential-modularity chain
(Moret–Bailly + dihedral residual modularity + modularity lifting over
totally real fields + base-change descent). Future dispatches on this
node must build that machinery, not reuse `Family.lean`.

ASSEMBLY (2026-07-24, PROVEN): carrier inhabitation
(`exists_potentialModularityWitness_of_five_le` — Taylor 2002 +
modularity lifting over totally real fields) + the `ℓ`-adic Brauer
descent of the Hecke eigensystem to `ℚ`
(`exists_heckeField_system_of_witness` — BLGGT §5.3) + the hardly
ramified `3`-adic member (`exists_threeadic_member_of_witness` —
BLGGT §5.5, Fontaine–Laffaille, strict compatibility; since
2026-07-24 itself a PROVEN assembly over the realization carrier
`ThreeadicRealization` and its five leaves), glued by
uniting the two exceptional sets and instantiating the `3`-adic
compatibility clause at the descended polynomials. Carrier
inhabitation was in turn PROVEN (2026-07-24) as an assembly over the
Moret–Bailly seed, and the `ℓ`-adic descent and the `3`-adic member
are likewise proven assemblies; the residual sorries of this pillar
are now the inhabitation node's three
(`exists_moretBailly_seed_of_five_le`, `exists_heckePackage_of_seed`,
`exists_threeadic_realization_of_heckePackage`), the Brauer descent's
two remaining arithmetic ones
(`exists_descended_heckeSystem_of_solvable`,
`exists_heckeField_system_of_witness_of_pieces` — its group-theoretic
node `brauer_induction_trivial_character` was PROVEN 2026-07-24 by
Artin induction), and the realization
carrier's five (`exists_threeadicRealization_of_witness` plus the
four per-condition transfer leaves); the circularity guard above
binds each of them. -/
theorem exists_threeadic_compatible_member_of_five_le
    {ℓ : ℕ} (hℓodd : Odd ℓ) [Fact ℓ.Prime] (hℓ5 : 5 ≤ ℓ)
    {O : Type u} [CommRing O] [IsDomain O] [TopologicalSpace O]
    [IsTopologicalRing O] [Algebra ℤ_[ℓ] O] [IsLocalRing O]
    [Module.Finite ℤ_[ℓ] O] [IsModuleTopology ℤ_[ℓ] O]
    (hZinj : Function.Injective (algebraMap ℤ_[ℓ] O))
    {ρ : GaloisRep ℚ O (Fin 2 → O)}
    (hrank : Module.rank O (Fin 2 → O) = 2)
    (hρ : IsHardlyRamified hℓodd hrank ρ)
    {k : Type u} [Field k] [Finite k] [Algebra ℤ_[ℓ] k]
    [TopologicalSpace k] [DiscreteTopology k]
    {W : Type v} [AddCommGroup W] [Module k W] [Module.Finite k W]
    [Module.Free k W]
    (hW : Module.rank k W = 2) {ρbar : GaloisRep ℚ k W}
    (hρbar : IsHardlyRamified hℓodd hW ρbar)
    (hirr : ρbar.IsIrreducible)
    (π : O →+* k) (hπsurj : Function.Surjective π)
    (hπ : ∀ (q : ℕ) (hq : q.Prime), q ≠ 2 → q ≠ ℓ →
      (ρ.charFrob hq.toHeightOneSpectrumRingOfIntegersRat).map π =
        ρbar.charFrob hq.toHeightOneSpectrumRingOfIntegersRat) :
    ∃ (E : Type u) (_ : Field E) (_ : NumberField E)
      (S₀ : Finset (HeightOneSpectrum (NumberField.RingOfIntegers ℚ)))
      (Pv : HeightOneSpectrum (NumberField.RingOfIntegers ℚ) → Polynomial E)
      (ψℓ : E →+* AlgebraicClosure ℚ_[ℓ])
      (ιO : O →+* AlgebraicClosure ℚ_[ℓ]) (_ : Function.Injective ιO)
      (A : Type u) (_ : CommRing A) (_ : TopologicalSpace A)
      (_ : IsTopologicalRing A) (_ : Algebra ℤ_[3] A) (_ : IsLocalRing A)
      (_ : Module.Finite ℤ_[3] A) (_ : Module.Free ℤ_[3] A)
      (_ : IsModuleTopology ℤ_[3] A)
      (τ : GaloisRep ℚ A (Fin 2 → A))
      (hrankA : Module.rank A (Fin 2 → A) = 2)
      (_ : IsHardlyRamified (show Odd 3 by decide) hrankA τ)
      (ψ₃ : E →+* AlgebraicClosure ℚ_[3])
      (ιA : A →+* AlgebraicClosure ℚ_[3]) (_ : Function.Injective ιA),
      ∀ (q : ℕ) (hq : q.Prime),
        hq.toHeightOneSpectrumRingOfIntegersRat ∉ S₀ →
        q ≠ 2 → q ≠ 3 → q ≠ ℓ →
        (ρ.charFrob hq.toHeightOneSpectrumRingOfIntegersRat).map ιO =
          (Pv hq.toHeightOneSpectrumRingOfIntegersRat).map ψℓ ∧
        (τ.charFrob hq.toHeightOneSpectrumRingOfIntegersRat).map ιA =
          (Pv hq.toHeightOneSpectrumRingOfIntegersRat).map ψ₃ := by
  classical
  -- the potential-modularity carrier (Taylor 2002)
  obtain ⟨Wit⟩ :=
    exists_potentialModularityWitness_of_five_le hℓodd hℓ5 hZinj hrank hρ
      hW hρbar hirr π hπsurj hπ
  -- the `ℓ`-adic Brauer descent of the Hecke eigensystem to `ℚ`
  obtain ⟨S₀, Pv, hPv⟩ :=
    exists_heckeField_system_of_witness hℓodd hℓ5 hZinj hrank hρ
      hW hρbar hirr π hπsurj hπ Wit
  -- the hardly ramified `3`-adic member and its compatibility clause
  obtain ⟨S₁, A, iA1, iA2, iA3, iA4, iA5, iA6, iA7, iA8, τ, hrankA, hτ,
    ιA, hιA, hcompat⟩ :=
    exists_threeadic_member_of_witness hℓodd hℓ5 hZinj hrank hρ
      hW hρbar hirr π hπsurj hπ Wit
  -- glue: unite the exceptional sets and transport the descended
  -- polynomials along the compatibility clause
  refine ⟨Wit.E, Wit.fieldE, Wit.numberFieldE, S₀ ∪ S₁, Pv, Wit.ψℓ,
    Wit.ιO, Wit.ιO_injective, A, iA1, iA2, iA3, iA4, iA5, iA6, iA7, iA8,
    τ, hrankA, hτ, Wit.ψ₃, ιA, hιA, ?_⟩
  intro q hq hqS hq2 hq3 hqℓ
  have hqS₀ : hq.toHeightOneSpectrumRingOfIntegersRat ∉ S₀ := fun h =>
    hqS (Finset.mem_union_left _ h)
  have hqS₁ : hq.toHeightOneSpectrumRingOfIntegersRat ∉ S₁ := fun h =>
    hqS (Finset.mem_union_right _ h)
  have hℓmatch := hPv q hq hqS₀ hq2 hq3 hqℓ
  exact ⟨hℓmatch, hcompat q hq hqS₁ hq2 hq3 hqℓ _ hℓmatch⟩

/-!
### Pillar-γ helpers: field-generic Chebotarev–Brauer–Nesbitt transfer

Three PROVEN helper lemmas for `not_isIrreducible_of_charFrob_eisenstein`
— the field-generic forms of the `ZMod ℓ`-specific steps of `Lift.lean`'s
`not_isIrreducible_of_charFrob_eq` (whose proof this pillar's proof
mirrors, per the docstring's generalization path).
-/

/-- A finite field `k` receiving a `ℤ_[ℓ]`-algebra structure has
characteristic `ℓ`: the characteristic of `k` is a prime `p` (finiteness
rules out characteristic zero), and were `p ≠ ℓ` then `p` — a unit of
`ℤ_[ℓ]`, having norm one by coprimality — would map to the unit `(p : k)
= 0`, absurd. This is what lets the `ZMod ℓ`-valued mod-`ℓ` cyclotomic
character be compared with `k`-valued Frobenius data through
`ZMod.castHom` in pillar γ. -/
theorem charP_of_algebra_padicInt (ℓ : ℕ) [Fact ℓ.Prime]
    (k : Type u) [Field k] [Finite k] [Algebra ℤ_[ℓ] k] :
    CharP k ℓ := by
  obtain ⟨p, hp⟩ := CharP.exists k
  haveI := hp
  rcases CharP.char_is_prime_or_zero k p with hpp | rfl
  · suffices hpe : p = ℓ by rwa [hpe] at hp
    by_contra hne
    have hcop : ℓ.Coprime p :=
      (Nat.coprime_primes Fact.out hpp).mpr fun hle => hne hle.symm
    have hunit : IsUnit ((p : ℤ_[ℓ])) :=
      PadicInt.isUnit_iff.mpr (PadicInt.norm_natCast_eq_one_iff.mpr hcop)
    have hmap : IsUnit ((p : k)) := by
      have hu := hunit.map (algebraMap ℤ_[ℓ] k)
      rwa [map_natCast] at hu
    rw [CharP.cast_eq_zero k p] at hmap
    exact not_isUnit_zero hmap
  · haveI : CharZero k := CharP.charP_to_charZero k
    haveI : Finite ℕ :=
      Finite.of_injective (Nat.cast : ℕ → k) Nat.cast_injective
    exact (not_finite ℕ).elim

set_option backward.isDefEq.respectTransparency false in
/-- **Field-generic invariant-submodule refutation** (helper for pillar
γ): a nonzero proper Galois-stable submodule refutes irreducibility.
Transfer of `Chebotarev.lean`'s
`not_isIrreducible_of_invariant_submodule` (stated there over `ZMod ℓ`)
to an arbitrary coefficient field; the proof is identical. -/
theorem not_isIrreducible_of_invariant_submodule_field
    {k : Type u} [Field k] [TopologicalSpace k]
    {W : Type v} [AddCommGroup W] [Module k W]
    (ρbar : GaloisRep ℚ k W) (U : Submodule k W)
    (hne : U ≠ ⊥) (htop : U ≠ ⊤)
    (hinv : ∀ g w, w ∈ U → ρbar g w ∈ U) :
    ¬ ρbar.IsIrreducible := by
  intro hirr
  haveI : IsSimpleOrder (Subrepresentation ρbar.toRepresentation) := hirr
  rcases eq_bot_or_eq_top
    (⟨U, fun g w hw => hinv g w hw⟩ :
      Subrepresentation ρbar.toRepresentation) with hP | hP
  · exact hne (congrArg Subrepresentation.toSubmodule hP)
  · exact htop (congrArg Subrepresentation.toSubmodule hP)

set_option backward.isDefEq.respectTransparency false in
/-- **Brauer–Nesbitt over a general coefficient field** (helper for
pillar γ): a 2-dimensional representation over a field `k` whose
characteristic polynomials agree *everywhere* with those of `1 ⊕ χ`,
for a unit-valued character `χ`, is not irreducible. Field-generic
transfer of `Chebotarev.lean`'s `not_isIrreducible_of_charpoly_eq`
(stated there over `ZMod ℓ` with `χ = χ̄_cyc`), by the identical
Kolchin/common-eigenvector route: Cayley–Hamilton turns the charpoly
hypothesis into `(ρ g − 1)(ρ g − χ g) = 0`; on `ker χ` every element is
unipotent, so `BrauerNesbitt.exists_fixed_of_unipotent` gives a nonzero
fixed subspace, Galois-stable by normality; if it is everything, the
image commutes and `BrauerNesbitt.exists_common_eigenvector_of_commuting`
produces an invariant line — both `BrauerNesbitt` inputs are already
field-generic. -/
theorem not_isIrreducible_of_charpoly_eq_units
    {k : Type u} [Field k] [TopologicalSpace k]
    {W : Type v} [AddCommGroup W] [Module k W] [Module.Finite k W]
    [Module.Free k W]
    (hdim : Module.rank k W = 2) (ρbar : GaloisRep ℚ k W)
    (χ : Field.absoluteGaloisGroup ℚ →* kˣ)
    (h : ∀ g, (ρbar g).charpoly =
      X ^ 2 - C (((χ g : kˣ) : k) + 1) * X + C ((χ g : kˣ) : k)) :
    ¬ ρbar.IsIrreducible := by
  classical
  have hfr : Module.finrank k W = 2 :=
    Module.finrank_eq_of_rank_eq (by exact_mod_cast hdim)
  -- Cayley–Hamilton: `(ρ g − 1)(ρ g − χ g) = 0`
  have hCH : ∀ g, (ρbar g - 1) * (ρbar g - algebraMap k
      (Module.End k W) ((χ g : kˣ) : k)) = 0 := by
    intro g
    have hch := LinearMap.aeval_self_charpoly (ρbar g)
    rw [h g] at hch
    simp only [map_add, map_sub, map_mul, map_pow, Polynomial.aeval_X,
      Polynomial.aeval_C] at hch
    have hcomm : Commute (ρbar g) (algebraMap k
        (Module.End k W) ((χ g : kˣ) : k)) :=
      (Algebra.commute_algebraMap_right _ _)
    have hexp : (ρbar g - 1) * (ρbar g - algebraMap k
        (Module.End k W) ((χ g : kˣ) : k)) =
        (ρbar g) ^ 2 - (algebraMap k (Module.End k W) ((χ g : kˣ) : k)
          + algebraMap k (Module.End k W) 1) * ρbar g
        + algebraMap k (Module.End k W) ((χ g : kˣ) : k) := by
      have e1 : (ρbar g - 1) * (ρbar g - algebraMap k
          (Module.End k W) ((χ g : kˣ) : k)) =
          ρbar g * ρbar g - ρbar g * algebraMap k
            (Module.End k W) ((χ g : kˣ) : k)
          - ρbar g + algebraMap k (Module.End k W) ((χ g : kˣ) : k) := by
        noncomm_ring
      rw [e1, hcomm.eq, map_one]
      noncomm_ring
    rw [hexp]
    exact hch
  -- the kernel of the character acts unipotently
  by_cases hWtop : (⨅ hH : χ.ker,
      LinearMap.ker (ρbar (hH : Field.absoluteGaloisGroup ℚ) - 1)) = ⊤
  · -- `ρ` kills the kernel of `χ`: commuting image, split quadratics
    have hker1 : ∀ hH : χ.ker,
        ρbar (hH : Field.absoluteGaloisGroup ℚ) = 1 := by
      intro hH
      ext v
      have hv : v ∈ (⨅ hH : χ.ker,
          LinearMap.ker (ρbar (hH : Field.absoluteGaloisGroup ℚ) - 1)) :=
        hWtop ▸ Submodule.mem_top
      have hvk := (Submodule.mem_iInf _).mp hv hH
      rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero] at hvk
      simpa using hvk
    have hcommim : ∀ g₁ g₂, Commute (ρbar g₁) (ρbar g₂) := by
      intro g₁ g₂
      have hc : g₁⁻¹ * g₂⁻¹ * g₁ * g₂ ∈ χ.ker := by
        rw [MonoidHom.mem_ker]
        simp only [map_mul, map_inv]
        rw [mul_comm (χ g₁)⁻¹ (χ g₂)⁻¹, mul_assoc, mul_assoc,
          ← mul_assoc (χ g₁)⁻¹, inv_mul_cancel, one_mul, inv_mul_cancel]
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
          exact ⟨1, ((χ g : kˣ) : k),
            by rw [map_one]; exact hCH g⟩)
    refine not_isIrreducible_of_invariant_submodule_field ρbar
      (Submodule.span k {v}) ?_ ?_ ?_
    · simpa [Submodule.span_singleton_eq_bot] using hv
    · intro htop
      have h1 : Module.finrank k (Submodule.span k {v}) = 1 :=
        finrank_span_singleton hv
      rw [htop] at h1
      rw [finrank_top] at h1
      rw [hfr] at h1
      omega
    · intro g x hx
      obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hx
      obtain ⟨c, hc⟩ := heig (ρbar g) ⟨g, rfl⟩
      rw [map_smul, hc]
      exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _
        (Submodule.mem_span_singleton_self v))
  · -- the `ker χ`-fixed space is nonzero (Kolchin), proper, Galois-stable
    let ρH : χ.ker →* Module.End k W :=
      { toFun := fun hH => ρbar (hH : Field.absoluteGaloisGroup ℚ)
        map_one' := map_one ρbar
        map_mul' := fun x y => map_mul ρbar _ _ }
    have huni : ∀ hH : χ.ker, (ρH hH - 1) ^ 2 = 0 := by
      intro hH
      have hχ1 : ((χ (hH : Field.absoluteGaloisGroup ℚ) : kˣ) : k) = 1 := by
        rw [MonoidHom.mem_ker.mp hH.2]
        rfl
      have hthis := hCH (hH : Field.absoluteGaloisGroup ℚ)
      rw [hχ1, map_one] at hthis
      rw [pow_two]
      exact hthis
    obtain ⟨v₀, hv₀ne, hv₀fix⟩ :=
      BrauerNesbitt.exists_fixed_of_unipotent hdim ρH huni
    refine not_isIrreducible_of_invariant_submodule_field ρbar
      (⨅ hH : χ.ker,
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
          χ.ker := by
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

/-- **Pillar γ — Chebotarev + Brauer–Nesbitt over a finite coefficient
field** (PROVEN 2026-07-24, along the docstring's generalization path,
over the three field-generic helpers above): a
continuous mod-`ℓ` representation over a finite coefficient field `k`
whose Frobenius characteristic polynomials away from a finite set of
places are those of `1 ⊕ χ̄_cyc` — the Eisenstein quadratic
`X² − (q+1)X + q` at `Frob_q` — is not irreducible.

This is the finite-coefficient-field form of the PROVEN
`GaloisRepresentation.not_isIrreducible_of_charFrob_eq` (`Lift.lean`,
stated over `ZMod ℓ`), whose proof consumes ONLY Family-free material,
all of it in `Chebotarev.lean` (already imported here):
`dense_conjClasses_globalFrob` (Frobenii are dense in conjugates, the
Chebotarev node), `continuous_cyclotomicCharacterModL`,
`cyclotomicCharacterModL_globalFrob`, `discreteTopology_moduleTopology`,
the quadratic coefficient lemmas, and the pointwise Brauer–Nesbitt node
`not_isIrreducible_of_charpoly_eq` (Kolchin/common-eigenvector route,
`BrauerNesbitt.lean`). The `Lift.lean` home of the twin — not its
ingredients — is what blocks a direct import (the `Family.lean` cycle);
the prover of this pillar should `import
Fermat.FLT.GaloisRepresentation.Chebotarev` (Family-free) and follow
the twin's proof.

Generalization path for the eventual proof: `char k = ℓ` (the kernel of
`ℤ_ℓ → k` is a nonzero prime, hence the maximal ideal, since `k` is
finite), so `ZMod ℓ` maps canonically into `k` (`ZMod.castHom`); replace
the `ZMod ℓ`-valued comparison functions of the twin's density argument
by their `k`-valued composites (continuity is free — `k` is discrete),
and rerun the Kolchin argument, whose two `BrauerNesbitt` inputs are
field-generic. Literature: Serre, *Abelian ℓ-adic representations and
elliptic curves*, I-2.3 (density determines the semisimplification);
Curtis–Reiner, *Methods of Representation Theory*, §30 (Brauer–Nesbitt).

SOUNDNESS AUDIT (both ways, 2026-07-24): (i) direct — a true,
NON-vacuous statement (the split representation `1 ⊕ χ̄_cyc` itself
satisfies the hypotheses); its `ZMod ℓ` instance is already proven
in-tree; (ii) no collapse clause is needed — the hypotheses are
satisfiable and the statement is unconditionally true. -/
theorem not_isIrreducible_of_charFrob_eisenstein
    {ℓ : ℕ} [Fact ℓ.Prime]
    {k : Type u} [Field k] [Finite k] [Algebra ℤ_[ℓ] k]
    [TopologicalSpace k] [DiscreteTopology k]
    {W : Type v} [AddCommGroup W] [Module k W] [Module.Finite k W]
    [Module.Free k W]
    {ρbar : GaloisRep ℚ k W}
    (S : Finset (HeightOneSpectrum (NumberField.RingOfIntegers ℚ)))
    (h : ∀ (q : ℕ) (hq : q.Prime),
      hq.toHeightOneSpectrumRingOfIntegersRat ∉ S → q ≠ ℓ →
      ρbar.charFrob hq.toHeightOneSpectrumRingOfIntegersRat =
        X ^ 2 - C ((q : k) + 1) * X + C (q : k)) :
    ¬ ρbar.IsIrreducible := by
  classical
  -- `char k = ℓ`, so `ZMod ℓ` maps canonically into `k`
  haveI hchar : CharP k ℓ := charP_of_algebra_padicInt ℓ k
  set f : ZMod ℓ →+* k := ZMod.castHom (dvd_refl ℓ) k with hfdef
  -- an auxiliary prime avoiding the exceptional places pins the rank at 2:
  -- distinct primes give distinct places, so a finite set of places
  -- excludes only finitely many primes
  obtain ⟨q₀, hq₀p, hq₀S, hq₀ℓ⟩ :
      ∃ q₀ : ℕ, ∃ hq₀ : q₀.Prime,
        (Nat.Prime.toHeightOneSpectrumRingOfIntegersRat hq₀ ∉ S) ∧ q₀ ≠ ℓ := by
    set T : Finset ℕ := (insert
        ((Fact.out : ℓ.Prime).toHeightOneSpectrumRingOfIntegersRat)
        S).attach.image
      (fun v => (exists_prime_toHeightOneSpectrum v.1).choose) with hT
    obtain ⟨q₀, hq₀ge, hq₀p⟩ := Nat.exists_infinite_primes (T.sup id + 1)
    have hq₀T : q₀ ∉ T := by
      intro hmem
      have hle := Finset.le_sup (f := id) hmem
      simp only [id] at hle
      omega
    have hq₀S' : Nat.Prime.toHeightOneSpectrumRingOfIntegersRat hq₀p ∉
        insert ((Fact.out : ℓ.Prime).toHeightOneSpectrumRingOfIntegersRat)
          S := by
      intro hmem
      apply hq₀T
      obtain ⟨hcp, hceq⟩ := (exists_prime_toHeightOneSpectrum
        (Nat.Prime.toHeightOneSpectrumRingOfIntegersRat hq₀p)).choose_spec
      have hch : (exists_prime_toHeightOneSpectrum
          (Nat.Prime.toHeightOneSpectrumRingOfIntegersRat hq₀p)).choose = q₀ :=
        toHeightOneSpectrumRingOfIntegersRat_injective hcp hq₀p hceq.symm
      rw [hT]
      exact Finset.mem_image.mpr ⟨⟨_, hmem⟩, Finset.mem_attach _ _, hch⟩
    refine ⟨q₀, hq₀p, fun hmem => hq₀S' (Finset.mem_insert_of_mem hmem), ?_⟩
    rintro rfl
    exact hq₀S' (Finset.mem_insert.mpr (Or.inl rfl))
  have hfr : Module.finrank k W = 2 := by
    have h0 := congrArg Polynomial.natDegree (h q₀ hq₀p hq₀S hq₀ℓ)
    rwa [GaloisRep.charFrob_eq_charpoly_globalFrob,
      LinearMap.charpoly_natDegree, natDegree_comparisonQuadratic] at h0
  have hrank : Module.rank k W = 2 := by
    rw [← Module.finrank_eq_rank k W, hfr]
    norm_num
  -- the endomorphism space is discrete in its module topology
  letI : TopologicalSpace (Module.End k W) := moduleTopology k (Module.End k W)
  haveI : DiscreteTopology (Module.End k W) :=
    discreteTopology_moduleTopology _ _
  have hρcont : Continuous fun g : Field.absoluteGaloisGroup ℚ => ρbar g :=
    ContinuousMonoidHom.continuous_toFun ρbar
  -- the agreement set is closed …
  have hχcont := continuous_cyclotomicCharacterModL ℓ
  have hc1 : Continuous fun g : Field.absoluteGaloisGroup ℚ =>
      (ρbar g).charpoly.coeff 1 := by
    exact Continuous.comp (continuous_of_discreteTopology
      (f := fun φ : Module.End k W => φ.charpoly.coeff 1)) hρcont
  have hc0 : Continuous fun g : Field.absoluteGaloisGroup ℚ =>
      (ρbar g).charpoly.coeff 0 := by
    exact Continuous.comp (continuous_of_discreteTopology
      (f := fun φ : Module.End k W => φ.charpoly.coeff 0)) hρcont
  have hb1 : Continuous fun g : Field.absoluteGaloisGroup ℚ =>
      -(f ((cyclotomicCharacterModL ℓ g : (ZMod ℓ)ˣ) : ZMod ℓ) + 1) := by
    exact Continuous.comp (g := fun x : ZMod ℓ => -(f x + 1))
      continuous_of_discreteTopology hχcont
  have hb0 : Continuous fun g : Field.absoluteGaloisGroup ℚ =>
      f ((cyclotomicCharacterModL ℓ g : (ZMod ℓ)ˣ) : ZMod ℓ) := by
    exact Continuous.comp (g := fun x : ZMod ℓ => f x)
      continuous_of_discreteTopology hχcont
  have hDclosed : IsClosed {g : Field.absoluteGaloisGroup ℚ |
      (ρbar g).charpoly.coeff 1 =
        -(f ((cyclotomicCharacterModL ℓ g : (ZMod ℓ)ˣ) : ZMod ℓ) + 1) ∧
      (ρbar g).charpoly.coeff 0 =
        f ((cyclotomicCharacterModL ℓ g : (ZMod ℓ)ˣ) : ZMod ℓ)} := by
    rw [Set.setOf_and]
    exact (isClosed_eq hc1 hb1).inter (isClosed_eq hc0 hb0)
  -- … and contains the dense set of Frobenius conjugates
  have hsub : {x : Field.absoluteGaloisGroup ℚ |
      ∃ v : HeightOneSpectrum (NumberField.RingOfIntegers ℚ),
        v ∉ insert
          ((Fact.out : ℓ.Prime).toHeightOneSpectrumRingOfIntegersRat) S ∧
        ∃ g, x = g * globalFrob v * g⁻¹} ⊆
      {g : Field.absoluteGaloisGroup ℚ |
        (ρbar g).charpoly.coeff 1 =
          -(f ((cyclotomicCharacterModL ℓ g : (ZMod ℓ)ˣ) : ZMod ℓ) + 1) ∧
        (ρbar g).charpoly.coeff 0 =
          f ((cyclotomicCharacterModL ℓ g : (ZMod ℓ)ˣ) : ZMod ℓ)} := by
    rintro x ⟨v, hvS, g, rfl⟩
    obtain ⟨q, hq, rfl⟩ := exists_prime_toHeightOneSpectrum v
    have hqS : Nat.Prime.toHeightOneSpectrumRingOfIntegersRat hq ∉ S :=
      fun hmem => hvS (Finset.mem_insert_of_mem hmem)
    have hqℓ : q ≠ ℓ := by
      rintro rfl
      exact hvS (Finset.mem_insert.mpr (Or.inl rfl))
    -- conjugation invariance of the characteristic polynomial
    have hgu : (ρbar g).comp (ρbar g⁻¹) = LinearMap.id := by
      have hmul : ρbar g * ρbar g⁻¹ = 1 := by
        rw [← map_mul, mul_inv_cancel, map_one]
      exact hmul
    have hgu' : (ρbar g⁻¹).comp (ρbar g) = LinearMap.id := by
      have hmul : ρbar g⁻¹ * ρbar g = 1 := by
        rw [← map_mul, inv_mul_cancel, map_one]
      exact hmul
    have hconj : (ρbar (g * globalFrob
        (Nat.Prime.toHeightOneSpectrumRingOfIntegersRat hq) * g⁻¹)).charpoly =
        (ρbar (globalFrob
          (Nat.Prime.toHeightOneSpectrumRingOfIntegersRat hq))).charpoly := by
      have heq : ρbar (g * globalFrob
          (Nat.Prime.toHeightOneSpectrumRingOfIntegersRat hq) * g⁻¹) =
          (LinearEquiv.ofLinear (ρbar g) (ρbar g⁻¹) hgu hgu').conj
            (ρbar (globalFrob
              (Nat.Prime.toHeightOneSpectrumRingOfIntegersRat hq))) := by
        ext x
        simp [map_mul, LinearEquiv.conj_apply, Module.End.mul_apply]
      rw [heq, LinearEquiv.charpoly_conj]
    -- conjugation invariance of the cyclotomic character
    have hχconj : cyclotomicCharacterModL ℓ (g * globalFrob
        (Nat.Prime.toHeightOneSpectrumRingOfIntegersRat hq) * g⁻¹) =
        cyclotomicCharacterModL ℓ (globalFrob
          (Nat.Prime.toHeightOneSpectrumRingOfIntegersRat hq)) := by
      rw [map_mul, map_mul, map_inv, mul_right_comm, mul_inv_cancel, one_mul]
    have hval := h q hq hqS hqℓ
    rw [GaloisRep.charFrob_eq_charpoly_globalFrob] at hval
    have hfrob := cyclotomicCharacterModL_globalFrob (ℓ := ℓ) hq hqℓ
    constructor
    · show (ρbar _).charpoly.coeff 1 = _
      rw [hconj, hval, coeff_one_comparisonQuadratic, hχconj, hfrob,
        map_natCast]
    · show (ρbar _).charpoly.coeff 0 = _
      rw [hconj, hval, coeff_zero_comparisonQuadratic, hχconj, hfrob,
        map_natCast]
  -- density: the agreement set is everything
  have hDall : ∀ g : Field.absoluteGaloisGroup ℚ,
      (ρbar g).charpoly.coeff 1 =
        -(f ((cyclotomicCharacterModL ℓ g : (ZMod ℓ)ˣ) : ZMod ℓ) + 1) ∧
      (ρbar g).charpoly.coeff 0 =
        f ((cyclotomicCharacterModL ℓ g : (ZMod ℓ)ˣ) : ZMod ℓ) := by
    intro g
    have hdense := dense_conjClasses_globalFrob (K := ℚ)
      (insert ((Fact.out : ℓ.Prime).toHeightOneSpectrumRingOfIntegersRat) S)
    have hall : (Set.univ : Set (Field.absoluteGaloisGroup ℚ)) ⊆ _ :=
      hdense.closure_eq ▸ hDclosed.closure_subset_iff.mpr hsub
    exact hall (Set.mem_univ g)
  -- reconstruct the polynomial identity and conclude by the field-generic
  -- Brauer–Nesbitt helper, with `χ = χ̄_cyc` pushed into `k` through `f`
  apply not_isIrreducible_of_charpoly_eq_units hrank ρbar
    ((Units.map (f : ZMod ℓ →* k)).comp (cyclotomicCharacterModL ℓ))
  intro g
  obtain ⟨h1, h0⟩ := hDall g
  refine monic_quadratic_ext (LinearMap.charpoly_monic _)
    (monic_comparisonQuadratic _) ?_ (natDegree_comparisonQuadratic _) ?_ ?_
  · rw [LinearMap.charpoly_natDegree, hfr]
  · rw [h1, coeff_one_comparisonQuadratic]
    simp [Units.coe_map]
  · rw [h0, coeff_zero_comparisonQuadratic]
    simp [Units.coe_map]

/-- **The headline: no irreducible hardly ramified mod-`ℓ`
representation for `ℓ ≥ 5`** (PROVEN 2026-07-24 as an assembly over the
three pillars above and the PROVEN `3`-adic machinery) — the FLT
blueprint's ch. 4 reduction target ("there is no prime `ℓ ≥ 5` and
hardly-ramified irreducible 2-dimensional Galois representation"),
stated over a general finite coefficient field.

Assembly: lift `ρbar` (pillar α), spread the lift into a compatible
system with a hardly ramified `3`-adic member `τ` (pillar β); by the
PROVEN classification (`IsHardlyRamified.exists_frobenius_triangular`,
`Threeadic.lean`: in some basis the local Frobenius at `q ≥ 5` acts by
`[[q, *], [0, 1]]`), the member's Frobenius characteristic polynomials
are the Eisenstein quadratics `X² − (q+1)X + q`
(`LinearMap.charpoly_toMatrix` + `Matrix.charpoly_fin_two`); the
`E`-linkage transports them back — `ψ₃` is injective (a ring
homomorphism out of the field `E`), so the family polynomials `Pv` are
Eisenstein over `E`; `ιO` is injective, so the lift's characteristic
polynomials are Eisenstein over `O`; the reduction `π` carries them to
`ρbar` — whence `ρbar` is reducible by Chebotarev–Brauer–Nesbitt
(pillar γ), refuting irreducibility.

Relation to `Reducible.lean`'s B5 (`not_isIrreducible_of_isHardlyRamified`,
same statement over `ZMod ℓ`): B5 is the TREE's consumer node and its
route runs through `Family.lean`'s compatible-family machinery, which
consumes the modularity interface; this assembly is the Family-free
copy of the same argument, existing precisely so that the interface's
residual-modularity leaf can be discharged without a cycle. The two
routes share their proven 3-adic and Chebotarev ingredients and are
intended to share the lifting proof after the `Lift.lean` refactor
described on pillar α. -/
theorem not_isIrreducible_of_isHardlyRamified_of_five_le
    {ℓ : ℕ} (hℓodd : Odd ℓ) [Fact ℓ.Prime] (hℓ5 : 5 ≤ ℓ)
    {k : Type u} [Field k] [Finite k] [Algebra ℤ_[ℓ] k]
    [TopologicalSpace k] [DiscreteTopology k]
    {W : Type v} [AddCommGroup W] [Module k W] [Module.Finite k W]
    [Module.Free k W]
    (hW : Module.rank k W = 2) {ρbar : GaloisRep ℚ k W}
    (hρbar : IsHardlyRamified hℓodd hW ρbar) :
    ¬ ρbar.IsIrreducible := by
  classical
  intro hirr
  -- pillar α: the hardly ramified `ℓ`-adic lift
  obtain ⟨O, iO1, iO2, iO3, iO4, iO5, iO6, iO7, iO8, hZinj, ρ, hrank, hρ,
    π, hπsurj, hπ⟩ :=
    exists_hardlyRamified_lift_residual_of_five_le hℓodd hℓ5 hW hρbar hirr
  letI := iO1; letI := iO2; letI := iO3; letI := iO4; letI := iO5
  letI := iO6; letI := iO7; letI := iO8
  -- pillar β: the compatible system and its `3`-adic member
  obtain ⟨E, iE1, iE2, S₀, Pv, ψℓ, ιO, hιO, A, iA1, iA2, iA3, iA4, iA5,
    iA6, iA7, iA8, τ, hrankA, hτ, ψ₃, ιA, hιA, hcompat⟩ :=
    exists_threeadic_compatible_member_of_five_le hℓodd hℓ5 hZinj hrank hρ
      hW hρbar hirr π hπsurj hπ
  letI := iE1; letI := iE2
  letI := iA1; letI := iA2; letI := iA3; letI := iA4; letI := iA5
  letI := iA6; letI := iA7; letI := iA8
  -- pillar γ on the transported Eisenstein polynomials
  refine (not_isIrreducible_of_charFrob_eisenstein (ℓ := ℓ)
    (insert (Nat.prime_two.toHeightOneSpectrumRingOfIntegersRat)
      (insert (Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat) S₀))
    ?_) hirr
  intro q hq hqS hqℓ
  -- unpack the exceptional-set membership
  have hq2 : q ≠ 2 := by
    rintro rfl
    exact hqS (Finset.mem_insert.mpr (Or.inl rfl))
  have hq3 : q ≠ 3 := by
    rintro rfl
    exact hqS (Finset.mem_insert.mpr (Or.inr (Finset.mem_insert.mpr
      (Or.inl rfl))))
  have hqS₀ : hq.toHeightOneSpectrumRingOfIntegersRat ∉ S₀ := fun hmem =>
    hqS (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hmem))
  have hq5 : 5 ≤ q := by
    rcases Nat.lt_or_ge q 5 with h5 | h5
    · interval_cases q
      · exact absurd hq (by decide)
      · exact absurd hq (by decide)
      · omega
      · omega
      · exact absurd hq (by decide)
    · exact h5
  obtain ⟨hcompℓ, hcomp₃⟩ := hcompat q hq hqS₀ hq2 hq3 hqℓ
  -- the `3`-adic member's Frobenius characteristic polynomial is the
  -- Eisenstein quadratic: the PROVEN classification gives a basis in
  -- which the local Frobenius acts by the triangular matrix
  -- `[[q, *], [0, 1]]`, whose characteristic polynomial is
  -- `X² − (q+1)X + q`
  obtain ⟨b, cUp, hb⟩ :=
    IsHardlyRamified.exists_frobenius_triangular (Fin 2 → A) hrankA hτ
      q hq hq5
  have hcpA : τ.charFrob hq.toHeightOneSpectrumRingOfIntegersRat =
      X ^ 2 - C ((q : A) + 1) * X + C (q : A) := by
    have h1 : τ.charFrob hq.toHeightOneSpectrumRingOfIntegersRat =
        (LinearMap.toMatrix b b
          (τ.toLocal hq.toHeightOneSpectrumRingOfIntegersRat
            (Field.AbsoluteGaloisGroup.adicArithFrob
              hq.toHeightOneSpectrumRingOfIntegersRat))).charpoly := by
      rw [LinearMap.charpoly_toMatrix]
      rfl
    rw [h1, hb, Matrix.charpoly_fin_two]
    norm_num [Matrix.trace_fin_two, Matrix.det_fin_two, add_comm]
  -- descend the Eisenstein shape to the number field `E` …
  have hPvq : Pv hq.toHeightOneSpectrumRingOfIntegersRat =
      X ^ 2 - C ((q : E) + 1) * X + C (q : E) := by
    apply Polynomial.map_injective ψ₃ ψ₃.injective
    rw [← hcomp₃, hcpA]
    simp [Polynomial.map_sub, Polynomial.map_add, Polynomial.map_mul,
      Polynomial.map_pow, Polynomial.map_X, map_natCast, map_add, map_one]
  -- … transport it to the `ℓ`-adic lift's coefficients …
  have hcpO : ρ.charFrob hq.toHeightOneSpectrumRingOfIntegersRat =
      X ^ 2 - C ((q : O) + 1) * X + C (q : O) := by
    apply Polynomial.map_injective ιO hιO
    rw [hcompℓ, hPvq]
    simp [Polynomial.map_sub, Polynomial.map_add, Polynomial.map_mul,
      Polynomial.map_pow, Polynomial.map_X, map_natCast, map_add, map_one]
  -- … and reduce through `π` to `ρbar`
  have hred := hπ q hq hq2 hqℓ
  rw [hcpO] at hred
  rw [← hred]
  simp [Polynomial.map_sub, Polynomial.map_add, Polynomial.map_mul,
    Polynomial.map_pow, Polynomial.map_X, map_natCast, map_add, map_one]

end GaloisRepresentation.Modularity
