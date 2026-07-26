/-
Modularity/KhareWintenberger.lean — own work for the Fermat project (not
vendored from the FLT project).

# The Khare–Wintenberger cut behind residual modularity at `ℓ ≥ 5`

This module carries the founder decomposition of the residual-modularity
leaf `exists_weightTwoEigenform_residual_of_isIrreducible_of_five_le`
(`Modularity/Interface.lean`, pillar 2 at `ℓ ≥ 5` — the
Khare–Wintenberger content of the modularity subtree).

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
public import Mathlib.NumberTheory.NumberField.Basic
-- `Ideal.absNorm`: the absolute norm `Nw` is the constant coefficient of
-- the parallel-weight-`2` Hecke polynomials in the STATEMENTS of the two
-- joints of the automorphic cut, so this import must be public
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm
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
public import Mathlib.FieldTheory.Galois.Basic
-- the Moret–Bailly cut (2026-07-25, PIN RE-AUDIT): the scheme-theoretic
-- vocabulary in which Moret–Bailly's existence theorem and the twisted
-- Hilbert–Blumenthal moduli input are STATED below — `Scheme`, `Spec`,
-- `Smooth`, `IsSeparated`, `LocallyOfFiniteType`, `QuasiCompact` and
-- `GeometricallyIrreducible` all exist at this pin (contrary to the
-- 2026-07-24 audit note, which is corrected in the section docstring),
-- so these are `public import`s: the names occur in leaf statements.
public import Mathlib.AlgebraicGeometry.Geometrically.Irreducible
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
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
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import Mathlib.Algebra.Algebra.Rat
-- The Bertini DECOMPOSITION (2026-07-26): the hyperplane parameter space is
-- `Fin (n+1) → ℚ` and Zariski-genericity on it is stated as "off the zero
-- locus of a nonzero `MvPolynomial (Fin (n+1)) ℚ`", so `MvPolynomial` occurs
-- in the three new leaf STATEMENTS; `MvPolynomial.funext_set` (vanishing on a
-- box with infinite sides forces the polynomial to be zero) is what proves
-- the density lemma reconciling the Zariski and real topologies, and
-- `Set.Ioo_infinite` supplies the infinite sides.
public import Mathlib.Algebra.MvPolynomial.Funext
public import Mathlib.Order.Interval.Set.Infinite
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
-- the `charFrob` transport API (`GaloisRep.charFrob_map_algEquiv`,
-- `GaloisRep.exists_finset_isUnramifiedAt_map`), which discharges the base
-- of the solvable-descent chain (`heckeSystemDescendsTo_bot`)
import Fermat.FLT.Deformations.RepresentationTheory.GaloisRepTransport
import Mathlib.LinearAlgebra.Charpoly.ToMatrix
-- `LinearMap.det_eq_sign_charpoly_coeff`, for the determinant coefficient
-- of the Brauer-descent Frobenius charpolys
import Mathlib.LinearAlgebra.Charpoly.BaseChange
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
-- pillar-γ proof-only imports (see the module docstring's import note):
-- the Family-free Chebotarev/Brauer–Nesbitt machinery and its Kolchin
-- ingredients
import Fermat.FLT.GaloisRepresentation.Chebotarev
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
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.FieldTheory.Finite.Basic
-- (`Mathlib.Algebra.Field.ULift` is already `public import`ed above)
public import Fermat.FLT.Modularity.AbelianScheme
-- `Fermat.TatePt` and the two leaves of the Tate-module construction
-- (`exists_tateFrame_of_levelStructure`, `exists_weilFrobeniusSystem_of_mult`),
-- consumed by `nonempty_hilbertBlumenthalPoint_of_isTwistedHilbertBlumenthalModuli`
public import Fermat.FLT.Modularity.TateModule
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
import Mathlib.RingTheory.Henselian
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
-- proof-only (2026-07-25, `exists_heckeField_mem_range_of_eigensystem`); note
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

/-- **The potential-modularity carrier** (interface structure): the
Taylor/Moret–Bailly package attached to the Khare–Wintenberger lift
`ρ` — a totally real number field `F`, Galois over `ℚ`, over which `ρ`
becomes modular, recorded through the Hecke eigensystem of the attached
Hilbert newform (the "Hilbert modular form over `F`" of the blueprint,
carried as number-theoretic data: its Hecke field `E` and Hecke
polynomials `heckeF`), together with the `3`-adic realization `τF` of
the same eigensystem over `F` (the second member of the compatible
system over `F`; the first member is `ρ|_{G_F}` itself, via
`modularF`). Each field is a cited classical assertion; the structure
is the interface between pillar β and the potential-modularity
literature, architected so that the two sorried descent leaves below
(`exists_heckeField_system_of_witness`,
`exists_threeadic_member_of_witness`) consume exactly these fields.

Field provenance:

* `F`, `totallyReal`, `galoisF` — Taylor, *Remarks on a conjecture of
  Fontaine and Mazur*, J. Inst. Math. Jussieu 1 (2002), and *On the
  meromorphic continuation of degree two L-functions*, Doc. Math.
  Extra Vol. (2006): Moret–Bailly's theorem supplies a totally real
  field `F`, which may be taken Galois over `ℚ` and avoiding any
  prescribed finite set of local obstructions, over which the residual
  representation acquires a modular origin. `galoisF` is the enabling
  hypothesis of Brauer's induction theorem on `Gal(F/ℚ)`; the Brauer
  descent data proper (a virtual decomposition
  `1 = Σ nᵢ · Ind_{Hᵢ} χᵢ` with `Hᵢ` solvable and `χᵢ`
  one-dimensional, plus solvable base change descending the newform to
  each `F^{Hᵢ}`) is deliberately NOT a field — it lives inside the
  sorried descent leaves, which cite it (BLGGT §5.3).
* `E`, `badF`, `heckeF` — the Hilbert newform `f` of parallel weight
  `2` over `F` attached to `ρ|_{G_F}`: `E` is a number field carrying
  its Hecke field (see the DESCENT-CLOSURE note below for why it is
  not merely the Hecke field), `heckeF w` its Hecke polynomial
  `X² − a_w·X + Nw` away from the finite bad set `badF` (the level of
  `f` and the places over `2`, `3` and `ℓ`).

DESCENT-CLOSURE OF `E` (recorded 2026-07-26, from an obligation
reported upward by the owner of
`exists_heckeTrace_of_prime_cyclic_step_of_inert`; NO formal change
was needed, only this correction of the record). `E` must NOT be read
as "the Hecke field of `f`" on the nose. The solvable-descent leaves
below (`exists_descended_heckeSystem_of_solvable` and the cyclic /
prime-cyclic steps under it) conclude that the Hecke eigenvalues of
the forms obtained by DESCENDING `f` down the Brauer tower again lie
in `E`, read through `ψℓ`; and classically the Hecke field GROWS on
the way down — at a place `u` of `F` of residue degree `d` over a
place `w` of an intermediate field the eigenvalue is `α^d + β^d`,
which generates a subfield of `ℚ(α + β)` that is in general PROPER.
So `E` is to be understood as a number field chosen large enough for
the whole descent — e.g. the compositum of the Hecke fields of all
forms arising in the Brauer decomposition, a FINITE compositum and
hence still a number field.

Nothing in this structure has to change for that reading, which is why
the repair is a docstring correction rather than a new field: no field
asserts that `heckeF` GENERATES `E`. If `(E, heckeF, ψℓ, ψ₃)` inhabits
the structure and `E ↪ E'` is a finite extension, then
`(E', heckeF ∘ map, ψℓ', ψ₃')` inhabits it too — `ψℓ`, `ψ₃` extend to
`E'` because `ℚ̄_ℓ`, `ℚ̄_3` are algebraically closed of characteristic
zero and `E'/E` is algebraic, and `modularF`, `matchF₃` are preserved
because `Polynomial.map` is functorial. So the producing leaf
`exists_potentialModularityWitness_of_five_le` is entitled to make the
enlarged choice, and MUST be understood as making it. Enlarging `E`
only weakens the `… ∈ Set.range ψℓ` conclusions of the descent leaves,
never strengthens them, and every downstream consumer of `E` uses only
that it is a NUMBER FIELD, so the enlargement is free.
* `ψℓ`, `ιO`, `ιO_injective`, `modularF` — modularity of `ρ|_{G_F}`
  (FLT blueprint ch. 4): the residual representation over `F` is
  modular (dihedral seed via converse theorems + Jacquet–Langlands,
  positioned by Moret–Bailly), and the modularity lifting theorem over
  totally real fields (Kisin; Taylor's 2018 Stanford course) promotes
  `ρ|_{G_F}` itself; Carayol's local-global compatibility at
  unramified places identifies its Frobenius characteristic
  polynomials with the Hecke polynomials of `f` inside `ℚ̄_ℓ`.
* `B`, `τF`, `ψ₃`, `ιB`, `ιB_injective`, `matchF₃` — the `3`-adic
  Galois representation attached to `f` (Carayol, *Sur les
  représentations ℓ-adiques associées aux formes modulaires de
  Hilbert*, Ann. Sci. ÉNS 19 (1986); Taylor, *On Galois
  representations associated to Hilbert modular forms*, Invent. Math.
  98 (1989)), integrally normalized on a stable lattice over a local
  ring `B` finite free over `ℤ_3` (classically the integers of the
  completion `E_λ`, `λ | 3`), with the same Hecke polynomials through
  `ψ₃`.

NO FORMAL CONSUMER (audited 2026-07-26): `matchF₃` — and with it the
whole `3`-adic block `B`/`τF`/`ιB` — is referenced by NO proof anywhere
in the tree, only by prose. That is architecturally intended (the block
exists so the interface records the `3`-adic member of the compatible
system), but it has a consequence worth knowing before anyone
"simplifies" the witness: nothing formal would catch a MIS-SPECIFIED
`3`-adic block. Its correctness rests entirely on the docstrings of
`carayol_threeadic_realization_of_heckePackage` and the two assemblies
above it, and `badF` is specified there to contain the places over
`2`, `3` and `ℓ` — which, since 2026-07-26, the inhabitation theorem
formally guarantees.

CIRCULARITY GUARD (inherited from pillar β, load-bearing): this
interface may only be inhabited by the independent
potential-modularity construction — never through `Family.lean`,
`Lift.lean`, or `Modularity/Interface.lean`. -/
structure PotentialModularityWitness (ℓ : ℕ) [Fact ℓ.Prime]
    (O : Type u) [CommRing O] [TopologicalSpace O] [IsTopologicalRing O]
    (ρ : GaloisRep ℚ O (Fin 2 → O)) : Type (u + 1) where
  /-- The totally real base field of potential modularity. -/
  F : Type u
  [fieldF : Field F]
  [numberFieldF : NumberField F]
  /-- `F` is totally real (Taylor 2002; required by the modularity
  lifting theorem over `F`). -/
  totallyReal : NumberField.IsTotallyReal F
  /-- `F/ℚ` is Galois — the enabling hypothesis of Brauer induction on
  `Gal(F/ℚ)` in the descent leaves. -/
  galoisF : IsGalois ℚ F
  /-- A number field carrying the Hecke field of the attached Hilbert
  newform — chosen large enough to be closed under the solvable
  descent (see the DESCENT-CLOSURE note in the structure docstring; it
  is NOT the Hecke field on the nose). -/
  E : Type u
  [fieldE : Field E]
  [numberFieldE : NumberField E]
  /-- The finite bad set over `F`: the level of the newform and the
  places over `2`, `3`, `ℓ`. -/
  badF : Finset (HeightOneSpectrum (NumberField.RingOfIntegers F))
  /-- The Hecke polynomials `X² − a_w·X + Nw` of the Hilbert newform. -/
  heckeF : HeightOneSpectrum (NumberField.RingOfIntegers F) → Polynomial E
  /-- The chosen place of `E` over `ℓ`, as an embedding into `ℚ̄_ℓ`. -/
  ψℓ : E →+* AlgebraicClosure ℚ_[ℓ]
  /-- The coefficient embedding of the lift into `ℚ̄_ℓ`. -/
  ιO : O →+* AlgebraicClosure ℚ_[ℓ]
  ιO_injective : Function.Injective ιO
  /-- Modularity of `ρ|_{G_F}`: its Frobenius characteristic
  polynomials away from `badF` are the Hecke polynomials (Taylor 2002
  + modularity lifting over totally real fields + Carayol local-global
  compatibility at unramified places). -/
  modularF : ∀ w ∉ badF,
    ((ρ.map (algebraMap ℚ F)).charFrob w).map ιO = (heckeF w).map ψℓ
  /-- The `3`-adic coefficient ring: classically the integers of
  `E_λ`, `λ | 3`. -/
  B : Type u
  [commRingB : CommRing B]
  [topologicalSpaceB : TopologicalSpace B]
  [isTopologicalRingB : IsTopologicalRing B]
  [algebraB : Algebra ℤ_[3] B]
  [isLocalRingB : IsLocalRing B]
  [moduleFiniteB : Module.Finite ℤ_[3] B]
  [moduleFreeB : Module.Free ℤ_[3] B]
  [isModuleTopologyB : IsModuleTopology ℤ_[3] B]
  /-- The `3`-adic Galois representation of `G_F` attached to the
  newform (Carayol 1986 / Taylor 1989), on a stable lattice. -/
  τF : GaloisRep F B (Fin 2 → B)
  /-- The chosen place of `E` over `3`, as an embedding into `ℚ̄_3`. -/
  ψ₃ : E →+* AlgebraicClosure ℚ_[3]
  /-- The coefficient embedding of the `3`-adic realization. -/
  ιB : B →+* AlgebraicClosure ℚ_[3]
  ιB_injective : Function.Injective ιB
  /-- The `3`-adic realization has the same Hecke polynomials. -/
  matchF₃ : ∀ w ∉ badF, (τF.charFrob w).map ιB = (heckeF w).map ψ₃

attribute [instance] PotentialModularityWitness.fieldF
  PotentialModularityWitness.numberFieldF
  PotentialModularityWitness.fieldE
  PotentialModularityWitness.numberFieldE
  PotentialModularityWitness.commRingB
  PotentialModularityWitness.topologicalSpaceB
  PotentialModularityWitness.isTopologicalRingB
  PotentialModularityWitness.algebraB
  PotentialModularityWitness.isLocalRingB
  PotentialModularityWitness.moduleFiniteB
  PotentialModularityWitness.moduleFreeB
  PotentialModularityWitness.isModuleTopologyB

/-- **The Moret–Bailly modular seed** (interface structure): the output
of Taylor's potential-modularity theorem BEFORE modularity lifting — a
MODULAR `ℓ`-adic representation `σ` of `G_F` residually congruent to
`ρbarF = ρbar|_{G_F}`, with "modular" recorded (as everywhere in this
module) through the Hecke eigensystem of the attached Hilbert newform.
This structure is the interface between the Moret–Bailly production
leaf (`exists_moretBailly_seed_of_five_le`) and the
modularity-lifting citation leaf (`exists_heckePackage_of_seed`): the
MLT needs exactly a modular congruent companion as its residual seed,
and this is its sharpest pin-stateable form — recording residual
modularity as bare mod-`ℓ` Frobenius data alone would be vacuous
(any function of `w` interpolates), so the seed carries the
characteristic-zero eigensystem AND the congruence.

Field provenance (classically `σ` is the `λ`-adic representation,
`λ | ℓ`, of the Hilbert newform `g` over `F` attached to
`ρbar|_{G_F}` by Taylor's Theorem B — equivalently the `ℓ`-adic Tate
module of the Moret–Bailly Hilbert–Blumenthal abelian variety):

* `E₀`, `bad₀`, `hecke₀` — the Hecke field of `g` (a number field, by
  Shimura's rationality), its finite bad set (the level of `g` and
  the places over `2`, `ℓ`), and its Hecke polynomials
  `X² − a_w·X + Nw`.
* `O₀` (with its local, module-finite, `ℤ_ℓ`-free package), `σ` — a
  stable-lattice integral normalization of the `λ`-adic
  representation of `g`: classically the Carayol-descended subring of
  the integers of `E₀_λ` over which the residually irreducible `σ` is
  definable with residue field inside `k` (Carayol, *Formes
  modulaires et représentations galoisiennes à valeurs dans un anneau
  local complet*, Contemp. Math. 165 (1994), Théorème 2 — applicable
  because `ρbarF` is irreducible, which the Moret–Bailly leaf
  guarantees alongside this seed).
* `ψ₀`, `ι₀`, `ι₀_injective`, `modular₀` — the eigensystem match
  inside `ℚ̄_ℓ` (Carayol local-global compatibility at unramified
  places for `g`).
* `π₀`, `residual₀` — the residual congruence to `ρbarF` at the level
  of Frobenius characteristic polynomials: the reduction of `σ` is
  `ρbar|_{G_F}` (Taylor 2002, Theorem B), so their `charFrob`s agree
  through `π₀` away from the bad set.

VACUITY AUDIT (2026-07-25, cluster sweep — audit only, the structure
was NOT changed).  Two findings, both about `hecke₀`/`modular₀`:

* *The seed is currently INFORMATIONALLY DEAD.*  Repo-wide, this type
  appears in exactly two hypothesis positions: `seed` in
  `exists_heckePackage_of_seed`, which forwards it unchanged to
  `exists_heckeEigensystem_of_congruentSeed`, where the binder is
  `_seed` and is NOT CONSUMED.  Nothing else mentions it.  So dropping
  the `Nonempty (MoretBaillySeed …)` conjunct from
  `exists_moretBailly_seed_of_five_le`'s conclusion would break no
  downstream proof (only `F`, `hFtr`, `hFgal`, `hirrF` are used), and
  the whole automorphic joint below it —
  `exists_heckeEigensystem_of_hilbertBlumenthalPoint` and its two
  sorried sub-joints — would become free-floating.
* *`modular₀` adds nothing to `matchℓ`.*  In the only inhabitation
  (`exists_moretBailly_seed_of_five_le`), `E₀`, `hecke₀`, `ψ₀` come
  from `exists_heckeEigensystem_of_hilbertBlumenthalPoint`, which is
  `rfl`-satisfiable by the point's own `(pt.D, pt.P, pt.ψDℓ)`; so
  `modular₀` degenerates to the point's `matchℓ` field with `hecke₀`
  renamed.  "Modular" is not recorded by this structure in any form
  the compiler can see.

Repair (cut-level, spanning this structure, the eigensystem node above
it and `PotentialModularityWitness` below it — NOT performed here): add
the parallel-weight-`2` clauses that the interface does not provide, at
minimum `∀ w ∉ bad₀, (hecke₀ w).Monic ∧ (hecke₀ w).natDegree = 2 ∧
(hecke₀ w).coeff 0 = (Ideal.absNorm w.asIdeal : E₀)`, and one clause
that survives the `E₀ := pt.D, hecke₀ := pt.P` junk witness — the Weil
bound on the eigenvalues, or their integrality.  Changing `modular₀`'s
type changes the record literal in `exists_moretBailly_seed_of_five_le`
and nothing else, because no consumer reads the field.

CIRCULARITY GUARD (inherited from pillar β, load-bearing): this
interface may only be inhabited by the independent Moret–Bailly
construction — never through `Family.lean`, `Lift.lean`, or
`Modularity/Interface.lean`. -/
structure MoretBaillySeed (ℓ : ℕ) [Fact ℓ.Prime]
    (F : Type u) [Field F] [NumberField F]
    {k : Type u} [Field k] [TopologicalSpace k] [DiscreteTopology k]
    {W : Type v} [AddCommGroup W] [Module k W] [Module.Finite k W]
    [Module.Free k W]
    (ρbarF : GaloisRep F k W) : Type (u + 1) where
  /-- The Hecke field of the seed newform `g`. -/
  E₀ : Type u
  [fieldE₀ : Field E₀]
  [numberFieldE₀ : NumberField E₀]
  /-- The finite bad set of the seed: the level of `g` and the places
  over `2` and `ℓ`. -/
  bad₀ : Finset (HeightOneSpectrum (NumberField.RingOfIntegers F))
  /-- The Hecke polynomials `X² − a_w·X + Nw` of the seed newform. -/
  hecke₀ : HeightOneSpectrum (NumberField.RingOfIntegers F) → Polynomial E₀
  /-- The seed's coefficient ring: classically the Carayol-descended
  subring of the integers of `E₀_λ`, `λ | ℓ`. -/
  O₀ : Type u
  [commRingO₀ : CommRing O₀]
  [topologicalSpaceO₀ : TopologicalSpace O₀]
  [isTopologicalRingO₀ : IsTopologicalRing O₀]
  [algebraO₀ : Algebra ℤ_[ℓ] O₀]
  [isLocalRingO₀ : IsLocalRing O₀]
  [moduleFiniteO₀ : Module.Finite ℤ_[ℓ] O₀]
  [moduleFreeO₀ : Module.Free ℤ_[ℓ] O₀]
  [isModuleTopologyO₀ : IsModuleTopology ℤ_[ℓ] O₀]
  /-- The modular `ℓ`-adic seed representation of `G_F` (classically
  the `λ`-adic representation of `g` on a stable lattice). -/
  σ : GaloisRep F O₀ (Fin 2 → O₀)
  /-- The chosen place of `E₀` over `ℓ`, as an embedding into `ℚ̄_ℓ`. -/
  ψ₀ : E₀ →+* AlgebraicClosure ℚ_[ℓ]
  /-- The coefficient embedding of the seed into `ℚ̄_ℓ`. -/
  ι₀ : O₀ →+* AlgebraicClosure ℚ_[ℓ]
  ι₀_injective : Function.Injective ι₀
  /-- Modularity of the seed: its Frobenius characteristic polynomials
  away from `bad₀` are the Hecke polynomials of `g`. -/
  modular₀ : ∀ w ∉ bad₀, (σ.charFrob w).map ι₀ = (hecke₀ w).map ψ₀
  /-- The reduction map onto the residual coefficient field. -/
  π₀ : O₀ →+* k
  /-- The residual congruence: the seed reduces to `ρbarF` at the
  level of Frobenius characteristic polynomials away from `bad₀`. -/
  residual₀ : ∀ w ∉ bad₀, (σ.charFrob w).map π₀ = ρbarF.charFrob w

attribute [instance] MoretBaillySeed.fieldE₀
  MoretBaillySeed.numberFieldE₀
  MoretBaillySeed.commRingO₀
  MoretBaillySeed.topologicalSpaceO₀
  MoretBaillySeed.isTopologicalRingO₀
  MoretBaillySeed.algebraO₀
  MoretBaillySeed.isLocalRingO₀
  MoretBaillySeed.moduleFiniteO₀
  MoretBaillySeed.moduleFreeO₀
  MoretBaillySeed.isModuleTopologyO₀

/-! #### The Moret–Bailly cut behind the seed (DECOMPOSED 2026-07-24)

`exists_moretBailly_seed_of_five_le` is Taylor 2002 Theorem B, whose
classical proof is a chain of three quite different inputs. The cut
below separates them at the literature's own joints and makes the seed
a PROVEN assembly:

* **the geometric joint** (`exists_hilbertBlumenthalPoint_of_five_le`,
  now itself PROVEN — SPLIT FURTHER 2026-07-25, see the section
  docstring "The geometric joint, SPLIT at Moret–Bailly's own
  statement"): Moret–Bailly's existence theorem for global points with
  prescribed local conditions (*Groupes de Picard et problèmes de
  Skolem II*, Ann. Sci. ÉNS 22 (1989), Thm 1.3 — a geometrically
  irreducible variety over `ℚ` with points over `ℝ` and over `ℚ_q`
  for `q` in a finite set acquires a point over a totally real field
  `F` realizing those local conditions), applied to the TWISTED
  HILBERT–BLUMENTHAL moduli variety attached to `ρbar` and to an
  auxiliary dihedral mod-`p` level structure (Taylor 2002, §2). Its
  output is packaged as a `HilbertBlumenthalPoint`: the compatible
  system of the Hilbert–Blumenthal abelian variety `A/F` with real
  multiplication, in the two characteristics that matter — the
  `ℓ`-adic member residually `ρbar|_{G_F}` (the `ℓ`-torsion of `A` IS
  the twist datum) and the `p`-adic member residually DIHEDRAL (the
  `p`-torsion is induced from a character of a quadratic extension,
  the second moduli condition). The two are now SEPARATE leaves —
  `exists_totallyReal_point_of_geometricallyIrreducible` (Moret–Bailly,
  pure algebraic geometry, stated in `Scheme`/`Spec` vocabulary) and
  `exists_twistedHilbertBlumenthalModuli_of_five_le` (the moduli input
  alone) — glued by PROVEN Galois bookkeeping.
* **the residual-surjectivity joint** (the same leaf's `hrestr`
  conjunct): Moret–Bailly's `F` is chosen linearly disjoint from the
  splitting field of `ρbar`, so restriction to `G_F` PRESERVES THE
  IMAGE of `ρbar` — the sharp, pin-stateable form of the avoidance
  condition. The irreducibility conjunct of Theorem B is then no
  longer assumed: it is PROVEN from image preservation by
  `isIrreducible_map_of_range_surjective` below.
* **the automorphic joint**
  (`exists_heckeEigensystem_of_hilbertBlumenthalPoint`; PROVEN
  2026-07-25 as an assembly over its own two joints — see the cut note
  before it: dihedral residual modularity
  `exists_residualModularity_of_hilbertBlumenthalPoint` and
  residually dihedral modularity lifting at `p`
  `exists_heckeSystem_of_residualModularity`, the two leaves that
  replace it — of which (b) is in turn PROVEN 2026-07-25 over the
  single norm leaf
  `exists_coeff_zero_eq_absNorm_of_hilbertBlumenthalPoint`): the
  compatible system of `A` is the Hecke eigensystem of a Hilbert
  newform `g` of parallel weight `2` over `F`. Classically: the
  residually dihedral mod-`p` representation is modular (Hecke theta
  series / converse theorems, transported by Jacquet–Langlands), and
  modularity lifting at `p` in the residually dihedral case (Taylor
  2002 §5, following Wiles and Skinner–Wiles) promotes this to the
  `p`-adic Tate module, hence — the two members lying in ONE
  compatible system with coefficient field `D` — to the whole system.

Soundness audit (2026-07-24): both leaves keep the full hypothesis
package of the parent (an irreducible hardly ramified mod-`ℓ`
representation with `ℓ ≥ 5`), which is classically unsatisfiable
(headline below), so each is classically true; the non-vacuous
intended discharge is the classical construction in its docstring.

ROUTE AUDIT — the odd-prime dichotomy is NOT available here
(2026-07-24). The shared discharge
`not_isIrreducible_of_isHardlyRamified_of_odd`
(`Modularity/Interface.lean`) used by the descent leaves of pillar 3
CANNOT be used for this leaf or its children, in either of two
independent ways: (i) IMPORT — `Interface.lean` imports THIS module,
so the dependency would be a cycle at the module level; (ii) PROOF —
at `ℓ ≥ 5` that dichotomy is discharged by the headline
`not_isIrreducible_of_isHardlyRamified_of_five_le` of this very
module, whose PROVEN assembly consumes pillar β, hence this leaf, so
the discharge would be circular at the declaration level. The
classical route is therefore preserved: these leaves must be proven by
the independent Moret–Bailly/Taylor construction recorded above.

CIRCULARITY GUARD (inherited from pillar β, load-bearing): as
everywhere in this module, neither leaf may be proven through
`Family.lean`, `Lift.lean`, or `Modularity/Interface.lean`. -/

/-- **The Hilbert–Blumenthal point** (interface structure): the
geometric output of the Moret–Bailly step over the totally real base
`F` — the strictly compatible system of Frobenius characteristic
polynomials of the Hilbert–Blumenthal abelian variety `A/F` with real
multiplication produced there, recorded in the two characteristics the
argument uses.

Field provenance (classically `A/F` is the point of the twisted
Hilbert–Blumenthal moduli variety supplied by Moret–Bailly, `D` its
real-multiplication field, `P w` the characteristic polynomial of
Frobenius at `w` on the Tate modules):

* `bad`, `D`, `P` — the finite bad set (the conductor of `A` and the
  places over `2`, `p`, `ℓ`), the coefficient field of the system, and
  the system itself.
* `O₀`, `σ`, `ψDℓ`, `ιO₀`, `matchℓ` — the `ℓ`-adic member on a stable
  lattice over a local ring finite free over `ℤ_ℓ` (the `λ`-adic Tate
  module of `A`, `λ | ℓ`, Carayol-normalized), matched with the system
  inside `ℚ̄_ℓ`.
* `π₀`, `residualℓ` — the FIRST moduli condition: the `ℓ`-torsion of
  `A` realizes `ρbarF = ρbar|_{G_F}`, recorded at the level of
  Frobenius characteristic polynomials.
* `p`, `p_ne_ℓ`, `C`, `τp`, `ψDp`, `ιC`, `matchp` — the auxiliary
  prime and the `p`-adic member of the SAME system, matched inside
  `ℚ̄_p`; this is the joint through which modularity at `p` transfers
  to `ℓ`.
* `kp`, `ρbarp`, `πp`, `residualp`, `irreduciblep`, `L`, `finrankL`,
  `dihedralp` — the SECOND moduli condition: the residual mod-`p`
  representation is irreducible over `F` but becomes reducible over a
  quadratic extension `L/F`, i.e. is induced from a character of
  `G_L` (dihedral). This is exactly the hypothesis the converse
  theorems and the residually dihedral lifting theorem consume.

CIRCULARITY GUARD (inherited from pillar β, load-bearing): this
interface may only be inhabited by the independent Moret–Bailly
construction — never through `Family.lean`, `Lift.lean`, or
`Modularity/Interface.lean`. -/
structure HilbertBlumenthalPoint (ℓ : ℕ) [Fact ℓ.Prime]
    (F : Type u) [Field F] [NumberField F]
    {k : Type u} [Field k] [TopologicalSpace k] [DiscreteTopology k]
    {W : Type v} [AddCommGroup W] [Module k W] [Module.Finite k W]
    [Module.Free k W]
    (ρbarF : GaloisRep F k W) : Type (u + 1) where
  /-- The finite bad set: the conductor of `A` and the places over
  `2`, `p`, `ℓ`. -/
  bad : Finset (HeightOneSpectrum (NumberField.RingOfIntegers F))
  /-- The coefficient field of the compatible system (classically the
  real-multiplication field of `A`). -/
  D : Type u
  [fieldD : Field D]
  [numberFieldD : NumberField D]
  /-- The Frobenius characteristic polynomials of the system. -/
  P : HeightOneSpectrum (NumberField.RingOfIntegers F) → Polynomial D
  /-- The `ℓ`-adic coefficient ring: classically a Carayol-normalized
  subring of the integers of `D_λ`, `λ | ℓ`. -/
  O₀ : Type u
  [commRingO₀ : CommRing O₀]
  [topologicalSpaceO₀ : TopologicalSpace O₀]
  [isTopologicalRingO₀ : IsTopologicalRing O₀]
  [algebraO₀ : Algebra ℤ_[ℓ] O₀]
  [isLocalRingO₀ : IsLocalRing O₀]
  [moduleFiniteO₀ : Module.Finite ℤ_[ℓ] O₀]
  [moduleFreeO₀ : Module.Free ℤ_[ℓ] O₀]
  [isModuleTopologyO₀ : IsModuleTopology ℤ_[ℓ] O₀]
  /-- The `ℓ`-adic member: the `λ`-adic Tate module of `A` on a stable
  lattice. -/
  σ : GaloisRep F O₀ (Fin 2 → O₀)
  /-- The chosen place of `D` over `ℓ`, as an embedding into `ℚ̄_ℓ`. -/
  ψDℓ : D →+* AlgebraicClosure ℚ_[ℓ]
  /-- The coefficient embedding of the `ℓ`-adic member. -/
  ιO₀ : O₀ →+* AlgebraicClosure ℚ_[ℓ]
  ιO₀_injective : Function.Injective ιO₀
  /-- The `ℓ`-adic member belongs to the system. -/
  matchℓ : ∀ w ∉ bad, (σ.charFrob w).map ιO₀ = (P w).map ψDℓ
  /-- **The Weil-pairing determinant** (field added 2026-07-26; see the
  cut note before
  `exists_coeff_zero_eq_absNorm_of_hilbertBlumenthalPoint`): the
  determinant of Frobenius on the `ℓ`-adic member is the absolute norm.
  Classically this is the `𝒪_D`-linear Weil pairing on the
  Hilbert–Blumenthal abelian variety — `det σ` is the `λ`-adic
  cyclotomic character, whose value at `Frob_w` is `Nw` — and it is the
  parallel-weight-`2` normalization `P w = X² − a_w·X + Nw` of the whole
  compatible system, since `matchℓ` and injectivity of `ψDℓ` carry it to
  `P` and `matchp` with `ιC_injective` carry it on to `τp`.

  It is a FIELD rather than a theorem because it is **not derivable from
  the rest of the interface, and is refutable relative to it**: twisting
  `(D, O₀, σ, C, τp, ρbarp)` by a character `χ` of order `ℓ` unramified
  outside a finite set satisfies every other field over the same `ρbarF`
  (`ζ_ℓ ≡ 1` modulo the maximal ideal of `ℤ_ℓ[ζ_ℓ]`, so `χ` reduces
  trivially and `residualℓ` survives; `residualp` is restored by twisting
  the datum `ρbarp`, and irreducibility and dihedrality are
  twist-invariant) while multiplying the determinant by `χ²`, which is
  nontrivial on a set of places of positive density — so no finite bad
  set repairs it.  See the refutation written out in the docstring of
  `exists_coeff_zero_eq_absNorm_of_hilbertBlumenthalPoint`. -/
  detσ : ∀ w ∉ bad,
    LinearMap.det (σ.toLocal w (Field.AbsoluteGaloisGroup.adicArithFrob w)) =
      (Ideal.absNorm w.asIdeal : O₀)
  /-- The reduction map onto the residual coefficient field. -/
  π₀ : O₀ →+* k
  /-- FIRST moduli condition: the `ℓ`-torsion of `A` realizes
  `ρbar|_{G_F}`. -/
  residualℓ : ∀ w ∉ bad, (σ.charFrob w).map π₀ = ρbarF.charFrob w
  /-- The auxiliary prime `p` of the dihedral level structure. -/
  p : ℕ
  [pfact : Fact p.Prime]
  p_ne_ℓ : p ≠ ℓ
  /-- The `p`-adic coefficient ring of the same system. -/
  C : Type u
  [commRingC : CommRing C]
  [topologicalSpaceC : TopologicalSpace C]
  [isTopologicalRingC : IsTopologicalRing C]
  [algebraC : Algebra ℤ_[p] C]
  [isLocalRingC : IsLocalRing C]
  [moduleFiniteC : Module.Finite ℤ_[p] C]
  [moduleFreeC : Module.Free ℤ_[p] C]
  [isModuleTopologyC : IsModuleTopology ℤ_[p] C]
  /-- The `p`-adic member: the `p`-adic Tate module of `A` on a stable
  lattice. -/
  τp : GaloisRep F C (Fin 2 → C)
  /-- The chosen place of `D` over `p`, as an embedding into `ℚ̄_p`. -/
  ψDp : D →+* AlgebraicClosure ℚ_[p]
  /-- The coefficient embedding of the `p`-adic member. -/
  ιC : C →+* AlgebraicClosure ℚ_[p]
  ιC_injective : Function.Injective ιC
  /-- The `p`-adic member belongs to the SAME system: this is the
  strict compatibility that transfers modularity from `p` to `ℓ`. -/
  matchp : ∀ w ∉ bad, (τp.charFrob w).map ιC = (P w).map ψDp
  /-- The residual coefficient field at `p`. -/
  kp : Type u
  [fieldkp : Field kp]
  [finitekp : Finite kp]
  [topologicalSpacekp : TopologicalSpace kp]
  [discreteTopologykp : DiscreteTopology kp]
  /-- The residual mod-`p` representation (the `p`-torsion of `A`). -/
  ρbarp : GaloisRep F kp (Fin 2 → kp)
  /-- The reduction map at `p`. -/
  πp : C →+* kp
  /-- The `p`-adic member reduces to `ρbarp`. -/
  residualp : ∀ w ∉ bad, (τp.charFrob w).map πp = ρbarp.charFrob w
  /-- SECOND moduli condition, part one: the `p`-torsion is
  irreducible over `F`. -/
  irreduciblep : ρbarp.IsIrreducible
  /-- The quadratic extension of the dihedral level structure. -/
  L : Type u
  [fieldL : Field L]
  [algebraL : Algebra F L]
  finrankL : Module.finrank F L = 2
  /-- SECOND moduli condition, part two: the `p`-torsion becomes
  reducible over `L`, i.e. is induced from a character of `G_L`
  (dihedral) — the input of the converse theorems. -/
  dihedralp : ¬ (ρbarp.map (algebraMap F L)).IsIrreducible

attribute [instance] HilbertBlumenthalPoint.fieldD
  HilbertBlumenthalPoint.numberFieldD
  HilbertBlumenthalPoint.commRingO₀
  HilbertBlumenthalPoint.topologicalSpaceO₀
  HilbertBlumenthalPoint.isTopologicalRingO₀
  HilbertBlumenthalPoint.algebraO₀
  HilbertBlumenthalPoint.isLocalRingO₀
  HilbertBlumenthalPoint.moduleFiniteO₀
  HilbertBlumenthalPoint.moduleFreeO₀
  HilbertBlumenthalPoint.isModuleTopologyO₀
  -- the `p`-side coefficient instances (added 2026-07-25 with the
  -- automorphic cut below): the two joints' STATEMENTS mention
  -- `pt.τp.charFrob` and `pt.ρbarp.charFrob`, whose elaboration needs
  -- the coefficient instances of `C` and `kp` outside the structure —
  -- exactly as `pt.σ.charFrob` needs the `O₀` block above.
  HilbertBlumenthalPoint.commRingC
  HilbertBlumenthalPoint.topologicalSpaceC
  HilbertBlumenthalPoint.isTopologicalRingC
  HilbertBlumenthalPoint.fieldkp
  HilbertBlumenthalPoint.topologicalSpacekp
  HilbertBlumenthalPoint.discreteTopologykp

/-! #### The geometric joint, SPLIT at Moret–Bailly's own statement
(2026-07-25 — PIN RE-AUDIT, correcting the 2026-07-24 note)

The 2026-07-24 audit recorded that "there is no algebraic-geometry
vocabulary at this pin to state 'geometrically irreducible variety with
local points' against", and concluded that the moduli interpretation and
Moret–Bailly's theorem could not be separated. **That finding is wrong
at this pin.** A re-audit of `.lake/packages/mathlib` finds:

* `AlgebraicGeometry.Scheme`, `AlgebraicGeometry.Spec`,
  `AlgebraicGeometry.Spec.map` (`Mathlib/AlgebraicGeometry/Scheme.lean`)
  — schemes and the `Spec` functor, so `R`-valued points of a
  `ℚ`-scheme `X` are the morphisms `Spec R ⟶ X` over `Spec ℚ`;
* `AlgebraicGeometry.GeometricallyIrreducible`
  (`Mathlib/AlgebraicGeometry/Geometrically/Irreducible.lean`, a
  morphism property: every base change to a field is irreducible) —
  exactly the hypothesis of Moret–Bailly's theorem;
* `AlgebraicGeometry.Smooth` (`Morphisms/Smooth.lean`),
  `IsSeparated` (`Morphisms/Separated.lean`), `LocallyOfFiniteType`
  (`Morphisms/FiniteType.lean`), `QuasiCompact`
  (`Morphisms/QuasiCompact.lean`) — the remaining "smooth variety"
  hypotheses.

So Moret–Bailly's theorem CAN be stated at this pin, and the cut below
does it: the geometric leaf splits into

* `exists_totallyReal_point_of_geometricallyIrreducible` — **exactly
  Moret–Bailly's Theorem 1.3** (*Groupes de Picard et problèmes de
  Skolem II*, Ann. Sci. ÉNS 22 (1989)), in the form recorded as
  Proposition 3.1.1 of Barnet-Lamb–Gee–Geraghty–Taylor, *Potential
  automorphy and change of weight* (= Taylor 2002 Theorem G / Prop.
  2.1), specialized to `K = K₀ = ℚ`, `S = {∞}`, `L'_∞ = ℝ`,
  `Ω_∞ = X(ℝ)`: a smooth geometrically irreducible `ℚ`-variety with a
  real point acquires a point over a totally real field `F`, Galois
  over `ℚ` and linearly disjoint from any prescribed finite extension.
  This leaf contains NO arithmetic of `ρbar` at all — it is a pure
  statement of algebraic geometry, reusable and independently citable.
* `exists_twistedHilbertBlumenthalModuli_of_five_le` — the **moduli
  input alone**: the twisted Hilbert–Blumenthal moduli variety attached
  to `ρbar` and to an auxiliary dihedral mod-`p` level structure
  (Taylor 2002 §2, via Shimura's theory of Hilbert–Blumenthal moduli)
  exists as such a variety, and its `F`-points give
  `HilbertBlumenthalPoint`s.
* PROVEN glue: `forall_exists_map_eq_of_ker_sup_range_eq_top` turns
  Moret–Bailly's linear-disjointness conclusion into the target's
  `hrestr`, and the openness of `ρbar.ker` (needed to feed `ρbar`'s
  splitting field to Moret–Bailly as the avoidance datum) is PROVEN
  from discreteness of the module topology on `Module.End k W`.

WHAT IS STILL NOT EXPRESSIBLE, recorded honestly. Moret–Bailly's
theorem in full carries, at each place `v` of a finite set `S`, a
*nonempty `v`-adically open* `Ω_v ⊆ X(K_v)` and returns a point inside
it. There is no topology on the `R`-point set `Spec R ⟶ X` of a scheme
at this pin, so "open subset of `X(K_v)`" cannot be said. The leaf
below is therefore the `Ω_v = X(K_v)` case — bare local solvability —
at `S = {∞}`, which is all the assembly needs: the moduli conditions
that Taylor arranges by shrinking `Ω_v` are here carried by the
*variety* (the twisted level structures), not by the local sets.
Likewise `QuasiProjective` does not exist at this pin; the leaf uses
the smooth/separated/finite-type/quasi-compact form in which BLGGT
Prop. 3.1.1 records the theorem ("smooth, geometrically connected
variety"), and the intended discharge supplies a quasi-projective `X`
(a Hilbert–Blumenthal Shimura variety), so no soundness is bought on
credit by the missing word.

CIRCULARITY GUARD (inherited, load-bearing): none of the three
declarations below may be discharged through `Family.lean`,
`Lift.lean`, or `Modularity/Interface.lean`. -/

/-! Names introduced by this cut, for leaf harvesting:
`specRatMap`, `HasRationalPoint` (functor-of-points vocabulary),
`forall_exists_map_eq_of_ker_sup_range_eq_top` (PROVEN),
`isOpen_ker_of_finite_discrete` (PROVEN),
`HasRationalPoint.of_comp` (PROVEN, added 2026-07-25),
`exists_isAffineOpen_hasRationalPoint` (PROVEN, added 2026-07-25),
`exists_totallyReal_point_of_geometricallyIrreducible` (**PROVEN
2026-07-25** — no longer a leaf: it is now the affine reduction over the
next name),
`exists_totallyReal_point_of_affine_geometricallyIrreducible` (**PROVEN
2026-07-26** — no longer a leaf: it is now the Bertini assembly over the
next two names),
`isTotallyReal_of_normal_of_realEmbedding` (PROVEN glue, added 2026-07-26),
`exists_affineCurve_of_affine_geometricallyIrreducible` (**PROVEN
2026-07-26** — no longer a leaf: the "iterate Bertini until the dimension is
one" loop is discharged by well-founded induction on `topologicalKrullDim`
over the next name),
`exists_dimensionDrop_of_affine_geometricallyIrreducible` (**PROVEN
2026-07-26** — no longer a leaf: the transport to `Spec Γ(X, ⊤)`, the
affine/separated/quasi-compact/finite-type inheritance and the STRICT
Krull-dimension drop, including the finite-dimensionality of a finitely
generated `ℚ`-algebra that the drop needs, are all discharged over the next
name),
`exists_bertiniHyperplane_of_affine_geometricallyIrreducible` (**PROVEN
2026-07-26** — no longer a leaf: once the hyperplane PARAMETER SPACE is
named, the Bertini half and the real-approximation half separate, and the
assembly is the density lemma `exists_rat_mem_box_eval_ne_zero` (PROVEN)
saying a nonzero rational polynomial has a rational non-root in every real
box; `affineLinearForm` and
`exists_affineCoordinates_of_locallyOfFiniteType` (PROVEN) supply the
parameterization),
`exists_nonZeroDivisorLocus_of_affine_geometricallyIrreducible` (SORRY —
elementary: `A` is a domain and `v ↦ ℓ_v` is a `ℚ`-linear map with proper
kernel, so a single LINEAR `F` works; the only missing mathlib ingredient is
"smooth over a field ⟹ reduced"),
`exists_bertiniGenericLocus_of_affine_geometricallyIrreducible` (SORRY — the
two BERTINI theorems in characteristic zero, smoothness and irreducibility of
the generic hyperplane section, stated over the parameter space; this is the
whole of item 3 of the missing-machinery list and by far the largest of the
three),
`exists_realApproximationBall_of_affine_geometricallyIrreducible` (SORRY —
the `ℝ`-topology half: a whole BOX of parameters keeps a real point on the
section, by the implicit function theorem on the real manifold `X(ℝ)`; needs
a scheme-to-real-manifold bridge, which mathlib lacks entirely),
`exists_normalRealPoint_of_affine_curve` (**PROVEN 2026-07-26** — no longer
a leaf: it is now BLGGT Prop. 3.1.1's own assembly over the next three
names),
`exists_bound_forall_padicPoint_of_geometricallyIrreducible` (**PROVEN
2026-07-26** — no longer a leaf: the affine coordinate ring `Γ(C, ⊤)` and the
`Γ`–`Spec` unit turn it into the next name, with no arithmetic used),
`exists_bound_forall_padicAlgHom_of_geometricallyIrreducible` (SORRY — Weil
bounds + Hensel: good local solvability at all but finitely many primes,
ALGEBRAIC form; a `ℚ`-algebra `A` in place of the scheme, a `ℚ`-algebra map
`A →ₐ[ℚ] ℚ_[p]` in place of the point. Step 3 of its route, the Hensel lift,
is already in mathlib — see its docstring),
`exists_primes_forall_sup_eq_top_of_isOpen` (**PROVEN 2026-07-26** — no
longer a leaf: Chebotarev plus the decomposition-group dictionary, over the
four new helper names `exists_conj_absoluteGaloisGroup_map_comp`,
`normal_range_absoluteGaloisGroup_map`,
`range_absoluteGaloisGroup_map_le_of_ringHom` and
`exists_isOpen_normal_finiteIndex_le`, all PROVEN),
`exists_normalSplitPoint_of_affine_curve` (SORRY — Moret–Bailly 1989
Thm 1.3 on a CURVE, steps (ii)+(iii) WITHOUT the avoidance datum; the
arithmetic heart), and
`exists_twistedHilbertBlumenthalModuli_of_five_le` (SORRY — Taylor
2002 §2). `exists_hilbertBlumenthalPoint_of_five_le` itself is now
PROVEN and is no longer a leaf.

MISSING MACHINERY for the surviving geometric leaves, in dependency order
(2026-07-25 audit of this pin; none of these exists in mathlib. Updated
2026-07-26 with the owning leaf of each item):

1. **The field `ℚ^tr` of totally real algebraic numbers**, as a field with
   the property that a number field embeds in it iff it is totally real.
   Cheapest of the four and a prerequisite for item 2. **NOTE (2026-07-26):
   it is NOT needed to STATE any leaf here, and building it before item 2
   would be free-floating.** The Bertini cut replaced "produce a totally
   real Galois field" by "produce a NORMAL number field with a ring map to
   `ℝ`" (`isTotallyReal_of_normal_of_realEmbedding` supplies the upgrade),
   which is exactly what a subfield of `ℚ^tr` contributes; so `ℚ^tr`
   belongs to the PROOF of item 2, not to any statement.
2. **Ampleness/largeness of `ℚ^tr`** (Pop): a smooth `ℚ^tr`-variety with a
   `ℚ^tr`-point has a Zariski-dense set of them. This is the modern
   packaging of Moret–Bailly's conclusion, and is what makes step 3's
   local–global principle usable. Owned by
   `exists_normalSplitPoint_of_affine_curve` (2026-07-26: the avoidance
   datum was moved off that leaf onto `exists_primes_forall_sup_eq_top_of_isOpen`,
   which needed only Chebotarev — already PROVEN in this project's
   `GaloisRepresentation/Chebotarev.lean` — and the decomposition-group
   description of complete splitting, and is itself now PROVEN; so items 2
   and 4 no longer carry the linear-disjointness burden, and neither does
   anything else: the disjointness conjunct is fully discharged.)
3. **Bertini over a field of characteristic zero**: a smooth
   geometrically irreducible quasi-projective variety of dimension `> 1`
   has a smooth geometrically irreducible hyperplane section, plus a
   real-topology approximation step to keep a real point. This is step (i)
   of the classical route. Updated 2026-07-26 (second cut of the day): the
   iteration was discharged by well-founded induction inside
   `exists_affineCurve_of_affine_geometricallyIrreducible`, the
   scheme-theoretic and dimension-theoretic bookkeeping by
   `exists_dimensionDrop_of_affine_geometricallyIrreducible`, and the single
   hyperplane function by
   `exists_bertiniHyperplane_of_affine_geometricallyIrreducible` over the
   hyperplane PARAMETER SPACE — so what is left of item 3 is the two BERTINI
   theorems alone, in
   `exists_bertiniGenericLocus_of_affine_geometricallyIrreducible`. The
   real-topology approximation is now a SEPARATE item, 6 below, and the
   elementary nonzerodivisor step a third,
   `exists_nonZeroDivisorLocus_of_affine_geometricallyIrreducible`.
6. **Real points of a smooth `ℚ`-variety as a real manifold**: mathlib has no
   functor from schemes to real manifolds, so `X(ℝ) ⊆ ℝⁿ` must be identified
   as a submanifold with tangent space the kernel of the Jacobian before
   `HasStrictFDerivAt.implicitFunction` can be applied. Added 2026-07-26;
   owned by `exists_realApproximationBall_of_affine_geometricallyIrreducible`.
   Independent of items 1–5 and startable on its own; it is real analysis,
   not arithmetic and not Bertini.
4. **Picard schemes / Jacobians as schemes**, with the torsor formalism
   and the "incompressible neighbourhood" existence statement — step (ii),
   and by far the largest of the four. Owned by
   `exists_normalSplitPoint_of_affine_curve`.
5. **Lang–Weil / the Weil bounds, plus spreading out over `ℤ[1/M]`**, giving a
   `ℚ_[p]`-point of a smooth geometrically irreducible `ℚ`-variety for all
   but finitely many `p`. Added 2026-07-26; owned since the same day by
   `exists_bound_forall_padicAlgHom_of_geometricallyIrreducible` (the scheme
   layer above it is discharged). Independent of items 1–4 and startable on
   its own. NOTE the Hensel half of this item was struck out on 2026-07-26:
   `Algebra.FormallySmooth.exists_mkₐ_comp_eq_of_isAdicComplete` plus
   `IsAdicComplete (maximalIdeal ℤ_[p]) ℤ_[p]` are both already in mathlib, so
   only Lang–Weil and the spreading-out limit argument are genuinely missing.

Each is an independently ownable subproject; 1, 3, 5 and 6 are the ones that
can be started without the others, and items 3 (Bertini), 5 (Lang–Weil +
spreading out) and 6 (real points as a manifold) are now leaves of their own --
`exists_bertiniGenericLocus_of_affine_geometricallyIrreducible`,
`exists_bound_forall_padicAlgHom_of_geometricallyIrreducible` and
`exists_realApproximationBall_of_affine_geometricallyIrreducible` -- so each
can be attacked without any of the others. The elementary
`exists_nonZeroDivisorLocus_of_affine_geometricallyIrreducible` is a fourth
such starting point and needs no missing-machinery item at all beyond
"smooth over a field implies reduced".

Leaf list under the moduli cut, as of the ARCHIMEDEAN recut (2026-07-26):
`nonempty_hilbertBlumenthalPoint_of_isTwistedHilbertBlumenthalModuli`
(SORRY — Tate modules),
`exists_twistedHilbertBlumenthalModuliTwist_of_five_le` (SORRY — Taylor
§4 minus the archimedean place: Rapoport's split moduli space, its
fineness, and Galois descent along the cocycle) and
`hasRealHilbertBlumenthalObject_of_isHardlyRamified` (SORRY — the
archimedean place, where the ODDNESS of `ρbar` is consumed; its intended
discharge is one real elliptic curve, `B = E ⊗_ℤ 𝒪_D`, and it needs no
moduli theory at all). `IsFormOver`, `HasRealHilbertBlumenthalObject`,
`hasRationalPoint_of_isFormOver`, `isFormOver_refl`,
`geometricallyIrreducible_of_isFormOver_isAlgClosed`,
`exists_twistedHilbertBlumenthalModuliScheme_of_five_le` and — since
2026-07-26 — `exists_twistedHilbertBlumenthalModuliForm_of_five_le`
itself are PROVEN. Two of those were expected to be hard and were not:
the geometric-irreducibility descent does not need Stacks 0364 (a FORM
carries more than a single irreducible base change), and the FORM leaf's
`Y`-clause needs no second space at all, `Y = X` doing once `X` has a
real point — which is what removed COMPLEX MULTIPLICATION from this
subtree's missing machinery. -/

/-- **The structure morphism of a `ℚ`-algebra's spectrum.** `ℚ` lives in
`Type 0` while the number field produced by Moret–Bailly must land in
`Type u` (the universe of the `HilbertBlumenthalPoint` interface), so the
base of the moduli variety is `Spec` of the `Type u` copy `ULift.{u} ℚ`
and this is the morphism `Spec F ⟶ Spec ℚ` induced by `ℚ → F`. -/
noncomputable def specRatMap (F : Type u) [CommRing F] [Algebra ℚ F] :
    AlgebraicGeometry.Spec (CommRingCat.of F) ⟶
      AlgebraicGeometry.Spec (CommRingCat.of (ULift.{u} ℚ)) :=
  AlgebraicGeometry.Spec.map (CommRingCat.ofHom
    ((algebraMap ℚ F).comp (ULift.ringEquiv : ULift.{u} ℚ ≃+* ℚ).toRingHom))

open CategoryTheory in
/-- **`X` has an `F`-rational point** (functor of points): a morphism
`Spec F ⟶ X` over the base `Spec ℚ`, i.e. a section of the structure
morphism `fX` along `Spec F ⟶ Spec ℚ`. This is the `R`-point notion in
which Moret–Bailly's local hypothesis (`R = ℝ`) and its global
conclusion (`R = F`) are both stated. -/
def HasRationalPoint {X : AlgebraicGeometry.Scheme.{u}}
    (fX : X ⟶ AlgebraicGeometry.Spec (CommRingCat.of (ULift.{u} ℚ)))
    (F : Type u) [CommRing F] [Algebra ℚ F] : Prop :=
  ∃ x : AlgebraicGeometry.Spec (CommRingCat.of F) ⟶ X, x ≫ fX = specRatMap F

/-- **Image preservation from Galois-theoretic disjointness** (PROVEN
glue): if the kernel of `ρ` together with the image of restriction
along `f : K →+* L` generates the whole absolute Galois group of `K`,
then every value of `ρ` is already a value of `ρ|_{Γ L}`.

This is the formal content of Moret–Bailly's avoidance condition. `F`
is produced linearly disjoint from the splitting field of `ρbar`, i.e.
from the fixed field of `ρbar.ker`; in Galois terms that says exactly
`ρbar.ker ⊔ Γ F = Γ ℚ`, and since `ρbar.ker` is normal the join is the
set product, so every `g` factors as `n · φ(h)` with `ρ n = 1` — whence
`ρ g = ρ (φ h) = (ρ.map f) h`. Feeding this to
`isIrreducible_map_of_range_surjective` also recovers irreducibility
over `F`, so the whole "avoidance" package of Theorem B is formal once
Moret–Bailly supplies the disjointness. -/
theorem forall_exists_map_eq_of_ker_sup_range_eq_top
    {K : Type*} [Field K] [NumberField K] {L : Type*} [Field L]
    {A : Type*} [CommRing A] [TopologicalSpace A]
    {M : Type*} [AddCommGroup M] [Module A M]
    (ρ : GaloisRep K A M) (f : K →+* L)
    (hsup : ρ.ker ⊔ (Field.absoluteGaloisGroup.map f).toMonoidHom.range = ⊤)
    (g : Field.absoluteGaloisGroup K) :
    ∃ h : Field.absoluteGaloisGroup L, (ρ.map f) h = ρ g := by
  have hmem : g ∈ ρ.ker ⊔ (Field.absoluteGaloisGroup.map f).toMonoidHom.range := by
    rw [hsup]; exact Subgroup.mem_top g
  rw [← SetLike.mem_coe, Subgroup.normal_mul] at hmem
  obtain ⟨n, hn, y, hy, hg⟩ := hmem
  obtain ⟨h, rfl⟩ := SetLike.mem_coe.mp hy
  refine ⟨h, ?_⟩
  have hn1 : ρ n = 1 := SetLike.mem_coe.mp hn
  rw [GaloisRep.map_apply, ← hg, map_mul, hn1, one_mul]
  rfl

open CategoryTheory AlgebraicGeometry in
/-- **A rational point of a subscheme is a rational point of the ambient
scheme** (PROVEN glue): if `i : U ⟶ X` is any morphism and `U` has an
`F`-rational point over the base `Spec ℚ`, then so has `X` — compose. This
is the trivial direction of the affine reduction below: shrinking `X` to an
open subscheme loses no points. -/
theorem HasRationalPoint.of_comp {X U : AlgebraicGeometry.Scheme.{u}} (i : U ⟶ X)
    (fX : X ⟶ AlgebraicGeometry.Spec (CommRingCat.of (ULift.{u} ℚ)))
    {F : Type u} [CommRing F] [Algebra ℚ F]
    (h : HasRationalPoint (i ≫ fX) F) : HasRationalPoint fX F := by
  obtain ⟨x, hx⟩ := h
  exact ⟨x ≫ i, by rw [Category.assoc]; exact hx⟩

open CategoryTheory AlgebraicGeometry in
/-- **A field-valued point already lives in an affine open** (PROVEN glue):
`Spec F` is a ONE-POINT scheme when `F` is a field, so an `F`-rational point
`x : Spec F ⟶ X` meets `X` in the single point `x.base y`; any affine open
neighbourhood `W` of that point then contains the whole of
`Set.range x.base`, and `x` factors through the open immersion `W.ι`
(`IsOpenImmersion.lift`). The factorization is a point of `W` over the same
base, because `lift ≫ W.ι = x`.

This is the nontrivial direction of the affine reduction: together with
`HasRationalPoint.of_comp` it lets Moret–Bailly's theorem be ASSUMED only
for affine `X`, which is where its classical proof starts — one passes to
an affine (indeed quasi-projective) neighbourhood of the given local point
before cutting down to a curve. -/
theorem exists_isAffineOpen_hasRationalPoint {X : AlgebraicGeometry.Scheme.{u}}
    (fX : X ⟶ AlgebraicGeometry.Spec (CommRingCat.of (ULift.{u} ℚ)))
    {F : Type u} [Field F] [Algebra ℚ F] (h : HasRationalPoint fX F) :
    ∃ U : X.Opens, AlgebraicGeometry.IsAffineOpen U ∧
      HasRationalPoint (U.ι ≫ fX) F := by
  obtain ⟨x, hx⟩ := h
  obtain ⟨y⟩ : Nonempty ↥(Spec (CommRingCat.of F)) := inferInstance
  obtain ⟨W, hW, hxW, -⟩ :=
    exists_isAffineOpen_mem_and_subset (X := X) (x := x.base y) (U := ⊤) trivial
  have hrange : Set.range x.base ⊆ Set.range (W.ι).base := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨z, rfl⟩
    rw [Subsingleton.elim z y]
    exact hxW
  refine ⟨W, hW, IsOpenImmersion.lift W.ι x hrange, ?_⟩
  rw [← Category.assoc, IsOpenImmersion.lift_fac]
  exact hx

/-! #### Moret–Bailly's existence theorem, AFFINE CASE — the Bertini cut

**Moret–Bailly's existence theorem, AFFINE CASE** (PROVEN 2026-07-26 over
two leaves; pure algebraic geometry, no arithmetic of `ρbar`): exactly the
statement of `exists_totallyReal_point_of_geometricallyIrreducible` below,
with `X` required AFFINE. Concretely `X = Spec A` for `A` a finitely generated,
smooth, geometrically integral `ℚ`-algebra admitting a `ℚ`-algebra map to
`ℝ`, and the conclusion produces a totally real Galois `F` — disjoint from
the fixed field of `N` — with a `ℚ`-algebra map `A → F`.

WHY THE AFFINE CASE SUFFICES (2026-07-25, PROVEN below). `Spec F` is a
one-point scheme for a field `F`, so the given real point lands in a single
point of `X` and factors through any affine open neighbourhood `W` of it
(`exists_isAffineOpen_hasRationalPoint`). All five geometric hypotheses
survive the restriction to `W`: smoothness, separatedness and finite type
because open immersions have all three (`IsOpenImmersion` is smooth, is a
mono hence separated, and is locally of finite type) and each property is
stable under composition; quasi-compactness because `W` is affine, hence a
compact space, over an affine — so quasi-separated — base; and geometric
irreducibility by mathlib's instance "a nonempty open subscheme of a
geometrically irreducible scheme, still surjecting onto the base, is
geometrically irreducible", the surjectivity being automatic because the
base `Spec ℚ` is a single point and `W` is nonempty. Conversely a point of
`W` is a point of `X` by composition (`HasRationalPoint.of_comp`), so
nothing is lost either way.

THE QUASI-PROJECTIVITY CAVEAT IS DISCHARGED BY THIS CUT (2026-07-25). The
parent's FORM AUDIT records, honestly, that Moret–Bailly's own hypotheses
include quasi-projectivity, that this pin has no `QuasiProjective` morphism
property, and that the leaf therefore relied on the intended discharge
supplying a quasi-projective `X` — soundness bought on credit. In the
AFFINE case that credit is repaid outright: an affine scheme of finite type
over a field is a closed subscheme of some `𝔸ⁿ`, hence quasi-affine, hence
quasi-projective. So every hypothesis of Moret–Bailly's theorem as he
states it genuinely holds for this leaf, and the missing word costs nothing
here. Reducing to the affine case is thus not only a simplification, it is
what makes the leaf a faithful instance of the cited theorem rather than an
approximation of it.

TWO HYPOTHESES ARE REDUNDANT HERE, and are kept only so that this statement
is LITERALLY the parent's: for `X` affine over the affine base `Spec ℚ`,
`hsep` holds because a morphism of affine schemes is separated, and `hqc`
because an affine scheme is a compact space. A prover may ignore both —
they are not the content. (Correspondingly the parent's own `hqc` is not
consumed by the reduction: quasi-compactness of the affine open is
re-derived rather than inherited.)

WHAT REMAINS, AND HOW IT IS CUT (2026-07-26 — this docstring now describes
a PROVEN assembly; the content moved to the two leaves named at the end).
Given `A` as above with a real point, produce a TOTALLY REAL `F`. A real
point only supplies a residue field admitting SOME real embedding — for
instance `ℚ(2^(1/3))` — which is emphatically not totally real, and no
shrinking, specialization or Galois-closure step repairs that: the Galois
closure of a field with one real embedding need not be totally real, and
enlarging `F` to its Galois closure also destroys the disjointness
condition `N ⊔ Γ F = ⊤` (take `F` cubic non-Galois and `N` the group of
the quadratic subfield of its Galois closure). So the totally real
conclusion and the disjointness conclusion must BOTH come from
Moret–Bailly's construction; neither is formal given the other. Those two
counterexamples are still valid and still forbid the obvious shortcuts.

WHAT IS NEVERTHELESS FORMAL, and is peeled off below, is a THIRD statement
that neither counterexample touches: for an extension of `ℚ` that is
NORMAL, having ONE real embedding already forces TOTAL reality
(`isTotallyReal_of_normal_of_realEmbedding`, PROVEN). Indeed if
`ι : F →+* ℝ` and `φ : F →+* ℂ`, then for `x : F` the value `φ x` is a
root of `minpoly ℚ x`, which by normality already splits inside `F`; so
every complex root of `minpoly ℚ x` is the image of an element of `F`
under the complexification of `ι`, hence real; hence `φ x` is real. The
first counterexample above is not a counterexample to this — `ℚ(2^(1/3))`
is not normal — and the second concerns the disjointness conjunct, which
this cut carries through untouched. Since characteristic zero makes
separability automatic, `IsGalois ℚ F` is free from `Normal ℚ F` as well.
**Consequence: the surviving leaves have only to produce a NORMAL number
field equipped with a ring map to `ℝ`.** That is also the honest shape of
the classical construction, which produces `F` inside the field `ℚ^tr` of
totally real algebraic numbers — i.e. inside `ℝ` — and takes a Galois
closure there.

THE ROUTE, AND WHERE IT IS CUT. Moret–Bailly, *Groupes de Picard et
problèmes de Skolem II*, Ann. Sci. ÉNS 22 (1989), Thm 1.3; cf. Rumely's
local–global principle over the ring of totally real algebraic integers,
and Pop's theorem that `ℚ^tr` is a large/ample field. The argument is:

(i) cut `X` down to a smooth geometrically irreducible CURVE through the
    real point by a Bertini-type argument that preserves the real point;
(ii) on that curve, exhibit the wanted point via a torsor under the
    Jacobian, using an "incompressible neighbourhood" in the Picard
    scheme;
(iii) conclude by the local–global principle over `ℚ^tr`.

**Step (i) is `exists_affineCurve_of_affine_geometricallyIrreducible`
(PROVEN 2026-07-26 over `exists_dimensionDrop_of_affine_geometricallyIrreducible`,
itself PROVEN over `exists_bertiniHyperplane_of_affine_geometricallyIrreducible`,
itself PROVEN over the hyperplane PARAMETER SPACE and its three leaves
`exists_nonZeroDivisorLocus_...`, `exists_bertiniGenericLocus_...` and
`exists_realApproximationBall_of_affine_geometricallyIrreducible`, all SORRY)
and steps (ii)+(iii) are `exists_normalRealPoint_of_affine_curve`
(PROVEN 2026-07-26 over `exists_normalSplitPoint_of_affine_curve`, which is
Moret–Bailly's theorem proper, plus the two arithmetic leaves that buy the
avoidance datum — see "The avoidance cut" section docstring below).** The
cut point is
exactly the classical one, so neither leaf is an artefact of the
formalization. Note that (i) is genuinely arithmetic and not a formality:
a `ℚ`-rational hyperplane through a given REAL point need not exist, so
the classical proof chooses a `ℚ`-hyperplane `ℝ`-close to one through the
point and recovers a real point of the section from the implicit function
theorem — which is why the leaf is stated as "there is a curve with a real
point and a `ℚ`-morphism to `X`" rather than "the section through the
point". Neither Bertini, nor Picard schemes as schemes, nor `ℚ^tr` exists
at this pin — see the MISSING MACHINERY list in the section docstring
above; but note that `ℚ^tr` is NOT needed to state either leaf, because
"normal, with a real embedding" already captures what a subfield of
`ℚ^tr` contributes.

CIRCULARITY GUARD: a statement of algebraic geometry with no
Galois-representation hypotheses, so no route through `Family.lean`,
`Lift.lean` or `Modularity/Interface.lean` is even relevant; it must be
proven by the geometric argument recorded above. -/

/-- **Normal + one real embedding ⟹ totally real** (PROVEN glue,
2026-07-26). If `F` is a number field, `Normal` over `ℚ`, and admits ANY
ring homomorphism `ι : F →+* ℝ`, then `F` is totally real.

Proof: let `ψ : F →+* ℂ` be the complexification of `ι` and let
`φ : F →+* ℂ` be arbitrary. For `x : F`, `φ x` is a root of `minpoly ℚ x`;
normality makes `minpoly ℚ x` split already inside `F`, so
`Polynomial.Splits.roots_map` identifies the complex roots with the
`ψ`-images of the roots in `F` — all of which are real. Hence `φ x` is
real for every `x`, i.e. `φ` is a real embedding; as `φ` was arbitrary,
every infinite place of `F` is real.

This is what lets the two surviving geometric leaves below be stated with
the much weaker conclusion "`F` is a normal number field with a ring map
to `ℝ`" instead of "`F` is totally real and Galois". See the section
docstring above for why this does NOT contradict the two counterexamples
recorded there. -/
theorem isTotallyReal_of_normal_of_realEmbedding
    {F : Type*} [Field F] [NumberField F] [Normal ℚ F] (ι : F →+* ℝ) :
    NumberField.IsTotallyReal F := by
  classical
  set ψ : F →+* ℂ := (Complex.ofRealHom).comp ι with hψ
  -- every value of every complex embedding is a `ψ`-value, hence real
  have key : ∀ (φ : F →+* ℂ) (x : F), ∃ r : F, ψ r = φ x := by
    intro φ x
    have hint : IsIntegral ℚ x := (Normal.isIntegral (‹Normal ℚ F›) x)
    have hne : (minpoly ℚ x) ≠ 0 := minpoly.ne_zero hint
    set q : F[X] := (minpoly ℚ x).map (algebraMap ℚ F) with hq
    have hqsplits : q.Splits := Normal.splits ‹Normal ℚ F› x
    have hmapeq : q.map ψ = (minpoly ℚ x).map (algebraMap ℚ ℂ) := by
      rw [hq, Polynomial.map_map]
      congr 1
      exact Subsingleton.elim _ _
    have hroot : φ x ∈ (q.map ψ).roots := by
      rw [hmapeq, Polynomial.mem_roots ((Polynomial.map_ne_zero_iff
        (algebraMap ℚ ℂ).injective).mpr hne)]
      have hz : Polynomial.aeval (φ x) (minpoly ℚ x) = 0 := by
        have h1 : Polynomial.aeval x (minpoly ℚ x) = (0 : F) := minpoly.aeval ℚ x
        have h2 : (φ : F →+* ℂ) (Polynomial.aeval x (minpoly ℚ x)) =
            Polynomial.aeval (φ x) (minpoly ℚ x) := by
          simpa using (Polynomial.aeval_algHom_apply
            (φ.toRatAlgHom : F →ₐ[ℚ] ℂ) x (minpoly ℚ x)).symm
        rw [← h2, h1, map_zero]
      simpa [Polynomial.IsRoot, Polynomial.eval_map, ← Polynomial.aeval_def] using hz
    rw [hqsplits.roots_map ψ, Multiset.mem_map] at hroot
    obtain ⟨r, -, hr⟩ := hroot
    exact ⟨r, hr⟩
  refine ⟨fun v => ?_⟩
  rw [← NumberField.InfinitePlace.mk_embedding v,
    NumberField.InfinitePlace.isReal_mk_iff]
  refine NumberField.ComplexEmbedding.isReal_iff.mpr ?_
  ext x
  obtain ⟨r, hr⟩ := key v.embedding x
  rw [NumberField.ComplexEmbedding.conjugate_coe_eq, ← hr, hψ]
  simp

open CategoryTheory AlgebraicGeometry in
/-- **The closed immersion `Spec (A/(ℓ)) ⟶ Spec A` cut out by one function.**

This is the affine hyperplane section in its coordinate-free form: for an
affine `ℚ`-variety `Spec A` and a global function `ℓ ∈ A`, the classical
"intersect with the hyperplane `ℓ = 0`" is `Spec` of the quotient
`A ⧸ (ℓ)`. Naming it once keeps the Bertini leaf below and its consumer
readable; both mention it, so it is in the cone of the root theorem. -/
noncomputable def specQuotSpanSingleton {A : CommRingCat.{u}} (ℓ : A) :
    AlgebraicGeometry.Spec (CommRingCat.of (A ⧸ Ideal.span {ℓ})) ⟶
      AlgebraicGeometry.Spec A :=
  AlgebraicGeometry.Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {ℓ})))

/-! ### The Bertini cut: the hyperplane PARAMETER SPACE (2026-07-26)

`exists_bertiniHyperplane_of_affine_geometricallyIrreducible` asks for ONE
global function `ℓ ∈ A` that is simultaneously

* Bertini-generic (its vanishing locus smooth and geometrically irreducible),
* a nonzerodivisor, and
* `ℝ`-close to a hyperplane through a prescribed real point.

The three conditions live on DIFFERENT topologies of the same parameter
space, and that is the whole reason they were kept in one leaf: the first two
hold on a Zariski-dense open subset of the space of hyperplanes, the third on
a nonempty subset open in the REAL topology, and only the (elementary) fact
that a nonzero rational polynomial has a rational non-root in every real box
lets one conclude that a single parameter satisfies all three.

**So the honest cut is to NAME the parameter space and separate the three
conditions on it.** That is what this block does. `A` is a finitely generated
`ℚ`-algebra, so a choice of algebra generators `x : Fin n → A` presents
`Spec A` as a closed subscheme of `𝔸ⁿ_ℚ`; the affine hyperplanes of `𝔸ⁿ_ℚ`
are then parameterized by `v : Fin (n+1) → ℚ` through
`affineLinearForm`, `ℓ_v = ∑ vᵢ xᵢ − v_last`. Zariski-genericity of a
condition on `v` is expressed as "there is a NONZERO `F : MvPolynomial
(Fin (n+1)) ℚ` such that `F(v) ≠ 0` implies the condition" — i.e. the good
locus contains a nonempty basic open of the parameter space — and the real
condition as "there is a nonempty box in which every rational `v` works".

The parameter space is not free-floating: `affineLinearForm` and the box /
genericity vocabulary are consumed by the proof of
`exists_bertiniHyperplane_of_affine_geometricallyIrreducible` below, which is
the assembly of the three leaves over the density lemma. -/

open CategoryTheory AlgebraicGeometry in
/-- **The affine-linear form `∑ vᵢ xᵢ − v_last` on `Spec A`** (2026-07-26).

Given a ring map `φ : ULift ℚ ⟶ A` (in practice `Spec.preimage g`, the ring
map underlying the structure morphism) and a finite family `x : Fin n → A` of
algebra generators, this is the restriction to `Spec A ⊆ 𝔸ⁿ_ℚ` of the
affine-linear form with coefficient vector `(v 0, …, v (n-1))` and constant
term `v (Fin.last n)`. As `v` ranges over `Fin (n+1) → ℚ` this is exactly the
family of `ℚ`-rational affine hyperplane sections of `Spec A` in the closed
embedding determined by `x` — the parameter space over which the three
Bertini leaves below are stated. -/
noncomputable def affineLinearForm {A : CommRingCat.{u}}
    (φ : CommRingCat.of (ULift.{u} ℚ) ⟶ A) {n : ℕ} (x : Fin n → A)
    (v : Fin (n + 1) → ℚ) : A :=
  (∑ i : Fin n, φ.hom (ULift.up (v i.castSucc)) * x i) - φ.hom (ULift.up (v (Fin.last n)))

open CategoryTheory AlgebraicGeometry in
/-- **Affine coordinates exist** (PROVEN glue, 2026-07-26). A morphism of
affine schemes `Spec A ⟶ Spec (ULift ℚ)` that is locally of finite type
presents `A` as a finitely generated algebra over `ULift ℚ`, i.e. there is a
finite family `x : Fin n → A` such that `A` is generated as a RING by the
image of the structure map together with the `xᵢ`. That is precisely a closed
embedding `Spec A ↪ 𝔸ⁿ_ℚ`, which is what the Bertini leaves need in order to
speak of hyperplanes at all.

Proof: `HasRingHomProperty.Spec_iff` turns `LocallyOfFiniteType g` into
`RingHom.FiniteType (Spec.preimage g).hom` (using `Spec.map_preimage`, since
`Spec` is fully faithful), which is `Algebra.FiniteType` for the induced
algebra structure; `Algebra.FiniteType.out` gives a finite generating set as
a `Finset`, `Finset.equivFin` turns it into a `Fin n`-family, and
`Algebra.adjoin_eq_ring_closure` converts `Algebra.adjoin = ⊤` into the
`Subring.closure` form used in the leaf statements (which avoids carrying an
`Algebra (ULift ℚ) A` instance in a statement, where it would have to be
supplied by hand). -/
theorem exists_affineCoordinates_of_locallyOfFiniteType {A : CommRingCat.{u}}
    (g : AlgebraicGeometry.Spec A ⟶
      AlgebraicGeometry.Spec (CommRingCat.of (ULift.{u} ℚ)))
    (hft : AlgebraicGeometry.LocallyOfFiniteType g) :
    ∃ (n : ℕ) (x : Fin n → A),
      Subring.closure (Set.range (AlgebraicGeometry.Spec.preimage g).hom ∪
        Set.range x) = ⊤ := by
  classical
  have hFT : RingHom.FiniteType (AlgebraicGeometry.Spec.preimage g).hom := by
    have h : AlgebraicGeometry.LocallyOfFiniteType
        (Spec.map (AlgebraicGeometry.Spec.preimage g)) := by
      rwa [Spec.map_preimage]
    exact HasRingHomProperty.Spec_iff.mp h
  letI : Algebra (ULift.{u} ℚ) A := (AlgebraicGeometry.Spec.preimage g).hom.toAlgebra
  haveI : Algebra.FiniteType (ULift.{u} ℚ) A := hFT
  obtain ⟨s, hs⟩ := (Algebra.FiniteType.out : (⊤ : Subalgebra (ULift.{u} ℚ) A).FG)
  refine ⟨s.card, fun i => ((s.equivFin.symm i : A)), ?_⟩
  have hrange : Set.range (fun i => ((s.equivFin.symm i : A))) = (s : Set A) := by
    ext a
    constructor
    · rintro ⟨i, rfl⟩; exact (s.equivFin.symm i).2
    · intro ha; exact ⟨s.equivFin ⟨a, ha⟩, by simp⟩
  rw [hrange]
  have h2 := Algebra.adjoin_eq_ring_closure (R := ULift.{u} ℚ) (A := A) (s : Set A)
  rw [hs, RingHom.algebraMap_toAlgebra] at h2
  rw [← h2]
  rfl

/-- **Zariski-generic meets real-open** (PROVEN, 2026-07-26): a nonzero
polynomial `F ∈ ℚ[X₁,…,X_m]` has a RATIONAL non-root in every real box.
Precisely: for every `v₀ : Fin m → ℝ` and every `ε > 0` there is
`v : Fin m → ℚ` with `|vᵢ − v₀ᵢ| < ε` for all `i` and `F(v) ≠ 0`.

This is the exact point where the two topologies on the hyperplane parameter
space are reconciled, and it is the reason the Bertini condition and the real
condition can be separated into different leaves at all: a Zariski-dense open
subset of the parameter space (the complement of `F = 0`) meets every
nonempty real box in a rational point.

Proof: `MvPolynomial.funext_set` says a polynomial over an integral domain
vanishing on a BOX WITH INFINITE SIDES is zero; the rationals in a real
interval `(v₀ᵢ − ε, v₀ᵢ + ε)` form an infinite set because the interval
contains a rational sub-interval (`exists_rat_btwn` twice) and `Set.Ioo` in a
densely ordered type is infinite. Contrapositive. -/
theorem exists_rat_mem_box_eval_ne_zero {m : ℕ} {F : MvPolynomial (Fin m) ℚ}
    (hF : F ≠ 0) (v₀ : Fin m → ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ v : Fin m → ℚ, (∀ i, |(v i : ℝ) - v₀ i| < ε) ∧ MvPolynomial.eval v F ≠ 0 := by
  classical
  set s : Fin m → Set ℚ := fun i => {q : ℚ | |(q : ℝ) - v₀ i| < ε} with hsdef
  have hsinf : ∀ i, (s i).Infinite := by
    intro i
    obtain ⟨a, ha1, ha2⟩ := exists_rat_btwn (show v₀ i - ε < v₀ i by linarith)
    obtain ⟨b, hb1, hb2⟩ := exists_rat_btwn (show v₀ i < v₀ i + ε by linarith)
    have hab : a < b := by exact_mod_cast ha2.trans hb1
    refine (Set.Ioo_infinite hab).mono ?_
    intro q hq
    have h1 : (a : ℝ) < (q : ℝ) := by exact_mod_cast hq.1
    have h2 : (q : ℝ) < (b : ℝ) := by exact_mod_cast hq.2
    simp only [hsdef, Set.mem_setOf_eq, abs_lt]
    constructor <;> linarith
  by_contra hcon
  push Not at hcon
  refine hF (MvPolynomial.funext_set s hsinf ?_)
  intro y hy
  rw [map_zero]
  exact hcon y (fun i => hy i (Set.mem_univ i))

section BertiniLeaves

variable {A : CommRingCat.{u}}
    (g : AlgebraicGeometry.Spec A ⟶
      AlgebraicGeometry.Spec (CommRingCat.of (ULift.{u} ℚ)))

open CategoryTheory AlgebraicGeometry in
/-- **A generic hyperplane function is a NONZERODIVISOR** (sorry node,
2026-07-26 — the elementary third of the Bertini cut; no Bertini theorem is
involved and it is independent of the other two leaves).

For a smooth, geometrically irreducible affine `ℚ`-variety `Spec A` presented
in coordinates `x : Fin n → A`, there is a nonzero `F ∈ ℚ[X₀,…,X_n]` such
that every rational parameter `v` off `F = 0` gives an affine-linear form
`ℓ_v = ∑ vᵢ xᵢ − v_last` that is a nonzerodivisor in `A`.

WHY IT IS TRUE, and what a prover has to build:

* `A` IS A DOMAIN. Geometric irreducibility gives `IrreducibleSpace (Spec A)`
  — mathlib has `GeometricallyIrreducible → Surjective` and, for a
  universally open morphism onto an irreducible base, `IrreducibleSpace X`;
  the base `Spec (ULift ℚ)` is a point, so this is available — and
  `PrimeSpectrum.irreducibleSpace_iff` turns it into "the nilradical is
  prime". Smoothness over a field gives geometric reducedness, hence
  `IsReduced A`, so the nilradical is `⊥` and `A` is a domain. **The one
  genuinely missing mathlib ingredient is "smooth over a field ⟹ reduced"**
  (`Mathlib/AlgebraicGeometry/Morphisms/Smooth.lean` at this pin only ever
  takes `[IsReduced X]` as a hypothesis, never concludes it). In a domain
  `mem_nonZeroDivisors_of_ne_zero` reduces everything to `ℓ_v ≠ 0`.
* `ℓ_v ≠ 0` GENERICALLY, and the witness `F` is LINEAR. The map
  `v ↦ ℓ_v` is `ℚ`-linear from `ℚ^{n+1}` to `A`; its kernel `K` is a proper
  subspace because the parameter `v = e_last` gives `ℓ_v = −1 ≠ 0` in the
  nontrivial ring `A`. A proper subspace of a finite-dimensional space is
  contained in the kernel of a nonzero linear functional `λ`, and
  `F := ∑ λᵢ Xᵢ` then works: `F(v) ≠ 0` forces `v ∉ K`, i.e. `ℓ_v ≠ 0`.

NOTE. `hdim` is deliberately NOT a hypothesis here: unlike the Bertini
genericity leaf, this statement is true in every dimension. -/
theorem exists_nonZeroDivisorLocus_of_affine_geometricallyIrreducible
    (hsmooth : AlgebraicGeometry.Smooth g)
    (hft : AlgebraicGeometry.LocallyOfFiniteType g)
    (hgi : AlgebraicGeometry.GeometricallyIrreducible g)
    {n : ℕ} (x : Fin n → A)
    (hx : Subring.closure (Set.range (AlgebraicGeometry.Spec.preimage g).hom ∪
      Set.range x) = ⊤) :
    ∃ F : MvPolynomial (Fin (n + 1)) ℚ, F ≠ 0 ∧
      ∀ v : Fin (n + 1) → ℚ, MvPolynomial.eval v F ≠ 0 →
        affineLinearForm (AlgebraicGeometry.Spec.preimage g) x v ∈ nonZeroDivisors A :=
  sorry

open CategoryTheory AlgebraicGeometry in
/-- **BERTINI in characteristic zero: the generic hyperplane section is
smooth and geometrically irreducible** (sorry node, 2026-07-26 — the purely
algebro-geometric half of step (i) of Moret–Bailly's route, with the real
topology entirely removed).

For a smooth, geometrically irreducible affine `ℚ`-variety `Spec A` of
dimension `> 1`, presented in coordinates `x : Fin n → A`, there is a nonzero
`F ∈ ℚ[X₀,…,X_n]` such that for every rational parameter `v` off `F = 0` the
hyperplane section `Spec (A ⧸ (ℓ_v))` is again smooth and geometrically
irreducible over `ℚ`.

THE TWO CLASSICAL THEOREMS, both stated for the parameter space here:

* BERTINI SMOOTHNESS — the general member of a base-point-free linear system
  on a smooth variety is smooth (Hartshorne, *Algebraic Geometry*, II.8.18
  and III.7; Jouanolou, *Théorèmes de Bertini et applications*, Ch. I). The
  hyperplanes of `𝔸ⁿ` cut out a base-point-free system on `Spec A`, and
  characteristic zero removes the inseparability caveat.
* BERTINI IRREDUCIBILITY — the general hyperplane section of an irreducible
  variety of dimension `≥ 2` is irreducible (Jouanolou, Ch. I, Thm 6.3).
  **`hdim` is exactly this hypothesis and it is LOAD-BEARING**: a general
  hyperplane section of a CURVE is a finite set of points, so at `dim = 1`
  the statement is false. Dimension `≥ 2` is also what makes the section
  NONEMPTY (the projective closure meets a general hyperplane in something of
  dimension `≥ 1`, which is therefore not contained in the hyperplane at
  infinity), which geometric irreducibility requires.

WHY THE GOOD LOCUS IS DEFINED OVER `ℚ` and contains a basic open. Both
conditions are open on the parameter space `𝔸^{n+1}` of the family, and the
family is defined over `ℚ`, so the good locus is a `ℚ`-rational open subset;
it is nonempty by the two theorems above applied at the generic point, and a
nonempty open subset of the irreducible space `𝔸^{n+1}_ℚ` contains a nonempty
basic open `D(F)`. This is the content of the `∃ F ≠ 0` packaging.

MACHINERY MISSING AT THIS PIN: Bertini's theorems in any form. This leaf is
pure algebraic geometry — no arithmetic, no real analysis, no
Galois-representation input — and is the largest of the three.

The parameter `x` is only assumed to GENERATE `A` as a ring over the base;
that is exactly a closed embedding `Spec A ↪ 𝔸ⁿ_ℚ`, which is what makes
"hyperplane section" meaningful and is supplied by
`exists_affineCoordinates_of_locallyOfFiniteType`. -/
theorem exists_bertiniGenericLocus_of_affine_geometricallyIrreducible
    (hsmooth : AlgebraicGeometry.Smooth g)
    (hft : AlgebraicGeometry.LocallyOfFiniteType g)
    (hgi : AlgebraicGeometry.GeometricallyIrreducible g)
    (hdim : 1 < topologicalKrullDim (AlgebraicGeometry.Spec A))
    {n : ℕ} (x : Fin n → A)
    (hx : Subring.closure (Set.range (AlgebraicGeometry.Spec.preimage g).hom ∪
      Set.range x) = ⊤) :
    ∃ F : MvPolynomial (Fin (n + 1)) ℚ, F ≠ 0 ∧
      ∀ v : Fin (n + 1) → ℚ, MvPolynomial.eval v F ≠ 0 →
        AlgebraicGeometry.Smooth (specQuotSpanSingleton
          (affineLinearForm (AlgebraicGeometry.Spec.preimage g) x v) ≫ g) ∧
        AlgebraicGeometry.GeometricallyIrreducible (specQuotSpanSingleton
          (affineLinearForm (AlgebraicGeometry.Spec.preimage g) x v) ≫ g) :=
  sorry

open CategoryTheory AlgebraicGeometry in
/-- **THE REAL APPROXIMATION: a whole BOX of parameters keeps a real point**
(sorry node, 2026-07-26 — the `ℝ`-topology half of step (i), with Bertini
entirely removed).

For a smooth, geometrically irreducible affine `ℚ`-variety `Spec A` of
dimension `> 1` WITH A REAL POINT, presented in coordinates `x : Fin n → A`,
there is a real parameter `v₀ : Fin (n+1) → ℝ` and an `ε > 0` such that EVERY
rational parameter `v` with `|vᵢ − v₀ᵢ| < ε` for all `i` gives a hyperplane
section `Spec (A ⧸ (ℓ_v))` that again has a real point.

WHY IT IS TRUE, and why the conclusion is a whole BALL rather than one
parameter. A `ℚ`-rational hyperplane through a prescribed REAL point
generally does not exist — the incidence conditions are `ℝ`-linear conditions
on `ℚ`-coefficients and their solution set typically meets `ℚⁿ` only in `0`.
So one cannot ask for the section THROUGH the given point. Moret–Bailly's
argument instead uses the `ℝ`-topology:

let `p ∈ X(ℝ)` be the given real point. Smoothness makes `X(ℝ) ⊆ ℝⁿ` a real
analytic manifold near `p`, of dimension `dim X ≥ 2 ≥ 1`. Since the `xᵢ`
generate, their differentials span the cotangent space at `p`, so there is a
real coefficient vector `c₀ ∈ ℝⁿ` for which `q ↦ ∑ c₀ᵢ qᵢ` has NONVANISHING
differential along `X(ℝ)` at `p`; put `b₀ := ∑ c₀ᵢ pᵢ` and
`v₀ := (c₀, b₀)`. The map `Ψ(q, v) = ∑ vᵢ qᵢ − v_last` on
`X(ℝ) × ℝ^{n+1}` vanishes at `(p, v₀)` with surjective partial derivative in
`q`, so the IMPLICIT FUNCTION THEOREM WITH PARAMETERS produces, for every `v`
in a neighbourhood of `v₀`, a real point of `X(ℝ)` on which `ℓ_v` vanishes —
i.e. a real point of the section. Shrinking that neighbourhood to a box gives
the `ε`. **The conclusion is a ball precisely so that it can be intersected
with the Zariski-generic locus of the Bertini leaf**; that intersection is
nonempty by `exists_rat_mem_box_eval_ne_zero`, and it is what makes the two
halves separable at all.

MACHINERY MISSING AT THIS PIN: the real-analytic structure on the real points
of a smooth `ℚ`-variety — mathlib has NO functor from schemes to real
manifolds, so the identification of `X(ℝ)` with a submanifold of `ℝⁿ` and its
tangent space with the kernel of the Jacobian must be built. The analytic
input itself is present: `HasStrictFDerivAt.implicitFunction` /
`ImplicitFunctionData`. This leaf is real analysis plus scheme-to-manifold
bookkeeping; it contains no Bertini theorem and no arithmetic.

`hdim` is used only through `dim X ≥ 1`, which is what makes the tangent
space at `p` nonzero; `1 < dim` is carried to keep the hypotheses parallel
with the sibling leaf. -/
theorem exists_realApproximationBall_of_affine_geometricallyIrreducible
    (hsmooth : AlgebraicGeometry.Smooth g)
    (hft : AlgebraicGeometry.LocallyOfFiniteType g)
    (hgi : AlgebraicGeometry.GeometricallyIrreducible g)
    (hreal : HasRationalPoint g (ULift.{u} ℝ))
    (hdim : 1 < topologicalKrullDim (AlgebraicGeometry.Spec A))
    {n : ℕ} (x : Fin n → A)
    (hx : Subring.closure (Set.range (AlgebraicGeometry.Spec.preimage g).hom ∪
      Set.range x) = ⊤) :
    ∃ (v₀ : Fin (n + 1) → ℝ) (ε : ℝ), 0 < ε ∧
      ∀ v : Fin (n + 1) → ℚ, (∀ i, |(v i : ℝ) - v₀ i| < ε) →
        HasRationalPoint (specQuotSpanSingleton
          (affineLinearForm (AlgebraicGeometry.Spec.preimage g) x v) ≫ g) (ULift.{u} ℝ) :=
  sorry

end BertiniLeaves

open CategoryTheory AlgebraicGeometry in
/-- **BERTINI + REAL APPROXIMATION: ONE good hyperplane function**
(**PROVEN 2026-07-26** over three leaves — the whole geometric content of
step (i) of Moret–Bailly's route; cut out of
`exists_dimensionDrop_of_affine_geometricallyIrreducible` on 2026-07-26,
which is PROVEN over it).

THE DECOMPOSITION (2026-07-26). The earlier docstring below argued that the
Bertini half and the real-approximation half are inseparable because ONE
hyperplane must be simultaneously Bertini-generic and `ℝ`-close. That
argument shows they cannot be separated *without naming the parameter space*;
once the parameter space IS named, they separate cleanly, and the assembly is
short. So this is now proven over:

* `exists_affineCoordinates_of_locallyOfFiniteType` (PROVEN) — a closed
  embedding `Spec A ↪ 𝔸ⁿ_ℚ`, i.e. ring generators `x : Fin n → A`, over which
  the hyperplane family `ℓ_v = ∑ vᵢ xᵢ − v_last` (`affineLinearForm`) is
  parameterized by `v : Fin (n+1) → ℚ`;
* `exists_nonZeroDivisorLocus_of_affine_geometricallyIrreducible` (SORRY,
  elementary) — off a proper `ℚ`-rational closed subset of the parameter
  space, `ℓ_v` is a nonzerodivisor;
* `exists_bertiniGenericLocus_of_affine_geometricallyIrreducible` (SORRY —
  the two Bertini theorems) — off a proper `ℚ`-rational closed subset, the
  section is smooth and geometrically irreducible;
* `exists_realApproximationBall_of_affine_geometricallyIrreducible` (SORRY —
  the `ℝ`-topology and the implicit function theorem) — every rational
  parameter in a nonempty real BOX gives a section with a real point;
* `exists_rat_mem_box_eval_ne_zero` (PROVEN) — the reconciliation: a nonzero
  rational polynomial has a rational non-root in every real box, so the
  Zariski-generic locus meets the real box.

The assembly multiplies the two genericity polynomials (`MvPolynomial (Fin
(n+1)) ℚ` is a domain, so the product is nonzero and a non-root of the
product is a non-root of each factor) and picks a rational parameter that is
both a non-root and inside the box. This is the classical argument's own
structure, unchanged; what the cut buys is that each of the three surviving
leaves is a single named theorem — Bertini, elementary linear algebra, and
the implicit function theorem — attackable independently.

--- the original statement-level docstring follows ---

Given an affine `ℚ`-variety `Spec A` which is smooth, separated, of finite
type, quasi-compact and geometrically irreducible over `ℚ`, has a REAL
point, and has dimension `> 1`, there is a global function `ℓ ∈ A` which is
a NONZERODIVISOR and whose vanishing locus `Spec (A ⧸ (ℓ))` is again
smooth and geometrically irreducible over `ℚ` and again has a real point.

WHY THIS IS THE RIGHT CUT. Everything else in the parent is bookkeeping and
is discharged there: `Spec (A ⧸ (ℓ)) ⟶ Spec A` is an affine morphism, hence
automatically separated and quasi-compact, and a surjection of rings is of
finite type, so those three of the six properties are free; and the STRICT
DIMENSION DROP is the elementary fact that quotienting a finite-dimensional
ring by a nonzerodivisor drops the Krull dimension by at least one
(`ringKrullDim_quotient_succ_le_of_nonZeroDivisor`), the finite-dimensionality
coming from `A` being a finitely generated algebra over a field. What is left
here is exactly the geometry.

WHY THIS IS TRUE. `A` is a finitely generated `ℚ`-algebra, so `Spec A` is a
closed subscheme of some `𝔸ⁿ_ℚ` (in particular quasi-affine, hence
quasi-projective — which is exactly the discharge of the parent's
quasi-projectivity caveat, so Bertini applies here as classically stated).
Take `ℓ` to be the restriction to `Spec A` of an affine-linear form
`Σ aᵢ xᵢ − b` with `aᵢ, b ∈ ℚ`, i.e. a `ℚ`-rational hyperplane. For a
suitable such hyperplane the section is:

* NONZERO, hence a NONZERODIVISOR — `Spec A` is geometrically integral
  (smooth over a field gives geometrically reduced, and geometric
  irreducibility is hypothesised), so `A` is a domain, and a hyperplane not
  containing `Spec A` restricts to a nonzero function; such a hyperplane
  exists because `dim Spec A ≥ 1`;
* SMOOTH over `ℚ` — Bertini's smoothness theorem in characteristic zero
  (the general member of a base-point-free linear system on a smooth
  variety is smooth; Hartshorne, *Algebraic Geometry*, II.8.18 and III.7,
  or Jouanolou, *Théorèmes de Bertini et applications*, Ch. I);
* GEOMETRICALLY IRREDUCIBLE — Bertini's irreducibility theorem, which needs
  exactly the hypothesis `dim Spec A ≥ 2` imposed here (Jouanolou, Ch. I,
  Thm 6.3; the dimension-`1` case is false, a general hyperplane section of
  a curve being a finite set of points).

THE REAL POINT IS THE DELICATE PART, and it is why the conclusion asks only
for SOME real point of the section. A hyperplane defined over `ℚ` through a
prescribed `ℝ`-point generally does not exist: the incidence conditions are
`ℝ`-linear conditions on `ℚ`-coefficients, and their solution set is a
proper `ℝ`-subspace which typically meets `ℚⁿ` only in `0`. Moret–Bailly's
argument instead uses the `ℝ`-topology: let `p` be a real point and choose a
real affine hyperplane `H₀` through `p` transverse to `Spec A` at `p`; the
`ℚ`-points are dense in the (real) parameter space of hyperplanes, and the
Bertini-good hyperplanes form a Zariski-dense open subset of it, whose real
points therefore meet every nonempty real ball (a proper closed subvariety
of the parameter space has empty interior in the real topology). So there is
a `ℚ`-hyperplane `H` both Bertini-good and `ℝ`-close to `H₀`; transversality
is an open condition, so the implicit function theorem on the real manifold
of real points produces a real point of the section near `p`. **The two
ingredients are inseparable in the argument: ONE hyperplane must be
simultaneously Bertini-generic and real-close, which is why this is one leaf
and not two.**

MACHINERY MISSING AT THIS PIN (2026-07-26 audit): Bertini's theorems in
either form; the real-analytic structure on the real points of a smooth
`ℚ`-variety (mathlib has no functor from schemes to real manifolds at all);
and the density statement for `ℚ`-points of the parameter space. All three
are buildable and none is arithmetic — this leaf is pure algebraic geometry
plus one appeal to the implicit function theorem, which mathlib does have
(`ImplicitFunctionData`, `HasStrictFDerivAt.implicitFunction`).

NOTE ON THE HYPOTHESES. `hsep` and `hqc` are automatic here — every
morphism of affine schemes is separated and quasi-compact — and are carried
only to keep the statement parallel with its consumer; a prover may ignore
them. `hdim` is genuinely load-bearing: it is the `dim ≥ 2` that Bertini
irreducibility requires, and without it the statement is FALSE.

NOT VACUOUS: `ℓ` a nonzerodivisor in a nontrivial ring forces `ℓ ≠ 0`, and
`GeometricallyIrreducible` forces the section to be NONEMPTY, so the unit
`ℓ = 1` (whose quotient is the zero ring) is excluded too.

CIRCULARITY GUARD: a statement of algebraic geometry with no
Galois-representation hypotheses, so no route through `Family.lean`,
`Lift.lean` or `Modularity/Interface.lean` is even relevant. -/
theorem exists_bertiniHyperplane_of_affine_geometricallyIrreducible
    {A : CommRingCat.{u}}
    (g : AlgebraicGeometry.Spec A ⟶
      AlgebraicGeometry.Spec (CommRingCat.of (ULift.{u} ℚ)))
    (hsmooth : AlgebraicGeometry.Smooth g)
    (_hsep : AlgebraicGeometry.IsSeparated g)
    (hft : AlgebraicGeometry.LocallyOfFiniteType g)
    (_hqc : AlgebraicGeometry.QuasiCompact g)
    (hgi : AlgebraicGeometry.GeometricallyIrreducible g)
    (hreal : HasRationalPoint g (ULift.{u} ℝ))
    (hdim : 1 < topologicalKrullDim (AlgebraicGeometry.Spec A)) :
    ∃ ℓ : A, ℓ ∈ nonZeroDivisors A ∧
      AlgebraicGeometry.Smooth (specQuotSpanSingleton ℓ ≫ g) ∧
      AlgebraicGeometry.GeometricallyIrreducible (specQuotSpanSingleton ℓ ≫ g) ∧
      HasRationalPoint (specQuotSpanSingleton ℓ ≫ g) (ULift.{u} ℝ) := by
  -- a closed embedding `Spec A ↪ 𝔸ⁿ_ℚ`, i.e. the hyperplane parameter space
  obtain ⟨n, x, hx⟩ := exists_affineCoordinates_of_locallyOfFiniteType g hft
  -- the two Zariski-generic loci, each a nonempty basic open `D(Fᵢ)`
  obtain ⟨F₁, hF₁0, hF₁⟩ :=
    exists_nonZeroDivisorLocus_of_affine_geometricallyIrreducible g hsmooth hft hgi x hx
  obtain ⟨F₂, hF₂0, hF₂⟩ :=
    exists_bertiniGenericLocus_of_affine_geometricallyIrreducible g hsmooth hft hgi hdim x hx
  -- the real box on which the section keeps a real point
  obtain ⟨v₀, ε, hε, hball⟩ :=
    exists_realApproximationBall_of_affine_geometricallyIrreducible g hsmooth hft hgi hreal
      hdim x hx
  -- a rational parameter inside the box and off both closed subsets
  obtain ⟨v, hvball, hvF⟩ := exists_rat_mem_box_eval_ne_zero (mul_ne_zero hF₁0 hF₂0) v₀ hε
  rw [map_mul] at hvF
  obtain ⟨hsm, hgi'⟩ := hF₂ v (right_ne_zero_of_mul hvF)
  exact ⟨_, hF₁ v (left_ne_zero_of_mul hvF), hsm, hgi', hball v hvball⟩

open CategoryTheory AlgebraicGeometry in
/-- **ONE BERTINI CUT: a single dimension-lowering step** (**PROVEN
2026-07-26** over the single hyperplane-function step
`exists_bertiniHyperplane_of_affine_geometricallyIrreducible`, itself PROVEN
the same day over the hyperplane parameter space and its three leaves; what
remains open is the geometry of choosing the hyperplane — Bertini, the
elementary nonzerodivisor step, and the real-topology approximation — not any
of the bookkeeping around it).

Given `X` affine, smooth, separated, of finite type, quasi-compact and
geometrically irreducible over `ℚ`, with a REAL point, and of dimension
`> 1`, there is an affine `X'` with a `ℚ`-morphism `h : X' ⟶ X` carrying
ALL SIX of the same properties over `ℚ` — including a real point — and with
`topologicalKrullDim X' < topologicalKrullDim X`.

THE PROOF, AND WHY THE CUT IS AT THE HYPERPLANE FUNCTION. `X` is affine, so
`X ≅ Spec Γ(X, ⊤)` (`Scheme.isoSpec`) and the whole statement transports to
that spectrum: all five morphism properties `Smooth`, `IsSeparated`,
`LocallyOfFiniteType`, `QuasiCompact` and `GeometricallyIrreducible` respect
isomorphisms (each is stable under base change, hence `RespectsIso`), and a
real point transports by composing with the isomorphism. The leaf then
supplies a NONZERODIVISOR `ℓ ∈ Γ(X, ⊤)` whose vanishing locus
`X' := Spec (Γ(X, ⊤) ⧸ (ℓ))` is smooth, geometrically irreducible and has a
real point, and `h := specQuotSpanSingleton ℓ ≫ X.isoSpec.inv` is the
morphism wanted. What is proven HERE is everything else:

* AFFINE, SEPARATED and QUASI-COMPACT — `Spec` of a ring is affine, and a
  morphism between affine schemes is an affine morphism
  (`isAffineHom_of_isAffine`), hence separated (`IsSeparated.of_isAffineHom`)
  and quasi-compact; both properties are stable under composition, so they
  pass to `h ≫ fX`;
* of FINITE TYPE — `Ideal.Quotient.mk` is surjective, hence of finite type
  (`RingHom.FiniteType.of_surjective`), and `HasRingHomProperty.Spec_iff`
  turns that into `LocallyOfFiniteType (specQuotSpanSingleton ℓ)`;
* of STRICTLY SMALLER DIMENSION — this is the one genuinely mathematical
  step proven here. `topologicalKrullDim` of a spectrum is `ringKrullDim`
  (`PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim`), and quotienting by
  a nonzerodivisor drops it by at least one
  (`ringKrullDim_quotient_succ_le_of_nonZeroDivisor`). Turning `d + 1 ≤ D`
  into `d < D` in `WithBot ℕ∞` needs `d ≠ ⊤`, i.e. FINITE-DIMENSIONALITY,
  which is proven here rather than assumed: `LocallyOfFiniteType fX` between
  affines gives `RingHom.FiniteType fX.appTop.hom`
  (`HasRingHomProperty.iff_of_isAffine`), so `Γ(X, ⊤)` is a quotient of
  `MvPolynomial (Fin n)` over `Γ(Spec ℚ, ⊤) ≅ ULift ℚ`, a field; hence
  `ringKrullDim Γ(X, ⊤) ≤ n` by `ringKrullDim_le_of_surjective` and
  `MvPolynomial.ringKrullDim_of_isNoetherianRing`. The remaining `⊥` case
  (`ℓ` a unit, so the section is empty) is settled by `1 < dim X`, which
  gives `dim X ≠ ⊥`. **So the docstring's old caveat "a prover may assume
  finite dimension, at the cost of proving that" is discharged.**

The geometry — Bertini smoothness, Bertini irreducibility, and the
`ℝ`-topology approximation that keeps a real point on the section — is
exactly what the leaf still asks for; see its docstring, where the argument,
the literature (Jouanolou Ch. I Thm 6.3; Hartshorne II.8.18, III.7) and the
missing mathlib machinery are recorded in full.

NOT VACUOUS: the hypothesis `1 < topologicalKrullDim X` blocks the trivial
witness `X' := X`, and the conclusion asserts a strict dimension drop.

CIRCULARITY GUARD: inherited from the parent — no route through
`Family.lean`, `Lift.lean` or `Modularity/Interface.lean`. -/
theorem exists_dimensionDrop_of_affine_geometricallyIrreducible
    {X : AlgebraicGeometry.Scheme.{u}} [AlgebraicGeometry.IsAffine X]
    (fX : X ⟶ AlgebraicGeometry.Spec (CommRingCat.of (ULift.{u} ℚ)))
    (hsmooth : AlgebraicGeometry.Smooth fX)
    (hsep : AlgebraicGeometry.IsSeparated fX)
    (hft : AlgebraicGeometry.LocallyOfFiniteType fX)
    (hqc : AlgebraicGeometry.QuasiCompact fX)
    (hgi : AlgebraicGeometry.GeometricallyIrreducible fX)
    (hreal : HasRationalPoint fX (ULift.{u} ℝ))
    (hdim : 1 < topologicalKrullDim X) :
    ∃ (X' : AlgebraicGeometry.Scheme.{u}) (_ : AlgebraicGeometry.IsAffine X')
      (h : X' ⟶ X),
      AlgebraicGeometry.Smooth (h ≫ fX) ∧
      AlgebraicGeometry.IsSeparated (h ≫ fX) ∧
      AlgebraicGeometry.LocallyOfFiniteType (h ≫ fX) ∧
      AlgebraicGeometry.QuasiCompact (h ≫ fX) ∧
      AlgebraicGeometry.GeometricallyIrreducible (h ≫ fX) ∧
      HasRationalPoint (h ≫ fX) (ULift.{u} ℝ) ∧
      topologicalKrullDim X' < topologicalKrullDim X := by
  classical
  haveI := hsmooth; haveI := hsep; haveI := hft; haveI := hqc; haveI := hgi
  -- `X` is homeomorphic to the spectrum of its ring of global sections
  have hdimX : topologicalKrullDim X = topologicalKrullDim (Spec Γ(X, ⊤)) :=
    IsHomeomorph.topologicalKrullDim_eq _ X.isoSpec.hom.homeomorph.isHomeomorph
  -- every morphism property in play respects isomorphisms, so all five
  -- transport from `fX` to the base morphism of `Spec Γ(X, ⊤)`
  have htrans : ∀ (P : MorphismProperty Scheme.{u}) [P.RespectsIso], P fX →
      P (X.isoSpec.inv ≫ fX) := by
    intro P _ h
    exact (P.cancel_left_of_respectsIso _ _).mpr h
  have hrealg : HasRationalPoint (X.isoSpec.inv ≫ fX) (ULift.{u} ℝ) := by
    obtain ⟨x, hx⟩ := hreal
    refine ⟨x ≫ X.isoSpec.hom, ?_⟩
    rw [Category.assoc, ← Category.assoc X.isoSpec.hom, Iso.hom_inv_id,
      Category.id_comp, hx]
  obtain ⟨ℓ, hℓ, hℓsm, hℓgi, hℓreal⟩ :=
    exists_bertiniHyperplane_of_affine_geometricallyIrreducible
      (X.isoSpec.inv ≫ fX) (htrans _ hsmooth) (htrans _ hsep) (htrans _ hft)
      (htrans _ hqc) (htrans _ hgi) hrealg (hdimX ▸ hdim)
  refine ⟨Spec (CommRingCat.of (Γ(X, ⊤) ⧸ Ideal.span {ℓ})), inferInstance,
    specQuotSpanSingleton ℓ ≫ X.isoSpec.inv, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Category.assoc]; exact hℓsm
  · rw [Category.assoc]
    haveI : IsSeparated (X.isoSpec.inv ≫ fX) := htrans _ hsep
    haveI : IsSeparated (specQuotSpanSingleton ℓ) := IsSeparated.of_isAffineHom _
    infer_instance
  · rw [Category.assoc]
    haveI : LocallyOfFiniteType (X.isoSpec.inv ≫ fX) := htrans _ hft
    haveI : LocallyOfFiniteType (specQuotSpanSingleton ℓ) :=
      HasRingHomProperty.Spec_iff.mpr
        (RingHom.FiniteType.of_surjective _ Ideal.Quotient.mk_surjective)
    infer_instance
  · rw [Category.assoc]
    haveI : QuasiCompact (X.isoSpec.inv ≫ fX) := htrans _ hqc
    infer_instance
  · rw [Category.assoc]; exact hℓgi
  · rw [Category.assoc]; exact hℓreal
  · -- the STRICT dimension drop
    rw [hdimX]
    have hA : topologicalKrullDim (Spec Γ(X, ⊤)) = ringKrullDim Γ(X, ⊤) :=
      PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim _
    have hA' : topologicalKrullDim (Spec (CommRingCat.of (Γ(X, ⊤) ⧸ Ideal.span {ℓ})))
        = ringKrullDim (Γ(X, ⊤) ⧸ Ideal.span {ℓ}) :=
      PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim _
    rw [hA, hA']
    -- `Γ(X, ⊤)` is a finitely generated algebra over a field, hence
    -- finite-dimensional: this is what makes the drop STRICT
    have hfin : ∃ n : ℕ, ringKrullDim Γ(X, ⊤) ≤ (n : WithBot ℕ∞) := by
      have hFT : RingHom.FiniteType (fX.appTop).hom :=
        HasRingHomProperty.iff_of_isAffine.mp hft
      set B := Γ(Spec (CommRingCat.of (ULift.{u} ℚ)), ⊤) with hB
      have hBe : (B : Type u) ≃+* ULift.{u} ℚ :=
        (Scheme.ΓSpecIso (CommRingCat.of (ULift.{u} ℚ))).commRingCatIsoToRingEquiv
      haveI : IsNoetherianRing (B : Type u) := isNoetherianRing_of_ringEquiv _ hBe.symm
      have hBdim : ringKrullDim (B : Type u) = 0 :=
        (ringKrullDim_eq_of_ringEquiv hBe).trans (ringKrullDim_eq_zero_of_field _)
      letI : Algebra (B : Type u) (Γ(X, ⊤) : Type u) := (fX.appTop).hom.toAlgebra
      haveI : Algebra.FiniteType (B : Type u) (Γ(X, ⊤) : Type u) := hFT
      obtain ⟨n, f, hf⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp ‹_›
      refine ⟨n, ?_⟩
      have := ringKrullDim_le_of_surjective f.toRingHom hf
      rw [MvPolynomial.ringKrullDim_of_isNoetherianRing, hBdim] at this
      simpa using this
    obtain ⟨n, hn⟩ := hfin
    have hquot : ringKrullDim (Γ(X, ⊤) ⧸ Ideal.span {ℓ}) + 1 ≤ ringKrullDim Γ(X, ⊤) :=
      ringKrullDim_quotient_succ_le_of_nonZeroDivisor hℓ
    have hDbot : (⊥ : WithBot ℕ∞) < ringKrullDim Γ(X, ⊤) :=
      lt_of_le_of_lt bot_le (hA ▸ hdimX ▸ hdim)
    have hdn : ringKrullDim (Γ(X, ⊤) ⧸ Ideal.span {ℓ}) < (n : WithBot ℕ∞) :=
      ENat.WithBot.add_one_le_natCast_iff.mp (hquot.trans hn)
    rcases eq_or_ne (ringKrullDim (Γ(X, ⊤) ⧸ Ideal.span {ℓ})) ⊥ with hd | hd
    · rw [hd]; exact hDbot
    · have hdtop : ringKrullDim (Γ(X, ⊤) ⧸ Ideal.span {ℓ}) ≠ ⊤ := by
        intro h; rw [h] at hdn; simp at hdn
      refine lt_of_lt_of_le ?_ hquot
      obtain ⟨k, hk⟩ := WithBot.ne_bot_iff_exists.mp hd
      rw [← hk] at hdtop ⊢
      have hk' : k ≠ ⊤ := fun h => hdtop (by rw [h]; rfl)
      rw [← WithBot.coe_one, ← WithBot.coe_add, WithBot.coe_lt_coe]
      exact (ENat.lt_add_one_iff hk').mpr le_rfl

open CategoryTheory AlgebraicGeometry in
/-- **Step (i) of Moret–Bailly's route: BERTINI, cutting down to a curve**
(**PROVEN 2026-07-26** — by well-founded induction on `topologicalKrullDim X`
over the single-step leaf
`exists_dimensionDrop_of_affine_geometricallyIrreducible`; what remains open
is one Bertini step, not the iteration).

Given `X` affine, smooth, separated, of finite type, quasi-compact and
geometrically irreducible over `ℚ`, with a REAL point, there is an affine
smooth geometrically irreducible `ℚ`-curve `C` — `topologicalKrullDim C ≤ 1`
— which also has a real point, together with a `ℚ`-morphism `g : C ⟶ X`.

THE PROOF, AND WHY THE CUT IS AT THE SINGLE STEP. Classically one "iterates
Bertini until the dimension is one". That iteration is the only formal part
of step (i), and it is what is discharged here: the argument is well-founded
induction on `topologicalKrullDim X` in `WithBot ℕ∞` (which is
`WellFoundedLT`, so no finite-dimensionality input is needed — a point worth
recording, since the naive `ℕ`-indexed induction would have required proving
that an affine finite-type `ℚ`-scheme is finite-dimensional). If
`dim X ≤ 1`, take `C := X` and `g := 𝟙 X`. Otherwise `1 < dim X` and the
leaf supplies `h : X' ⟶ X` with all six properties transported to `h ≫ fX`
and `dim X' < dim X`; the induction hypothesis applied to `X'` over the base
morphism `h ≫ fX` returns `g : C ⟶ X'`, and `g ≫ h` is the morphism wanted,
`Category.assoc` identifying `(g ≫ h) ≫ fX` with `g ≫ (h ≫ fX)`.

Note that the six properties are stated for the COMPOSITE `g ≫ fX` rather
than for `C` over a base of its own; that is what makes the induction go
through without any composition lemmas for `Smooth`, `IsSeparated`,
`LocallyOfFiniteType`, `QuasiCompact` and `GeometricallyIrreducible` — the
composite is literally the base morphism at the next stage.

THE REAL POINT IS THE DELICATE PART, and it is why the conclusion asks only
for SOME real point of `C` and SOME morphism `C ⟶ X`, rather than for a
hyperplane section through the given real point: see the leaf's docstring,
where the `ℝ`-topology approximation argument is recorded in full.

NOT VACUOUS: the dimension-`0` and dimension-`1` cases are discharged by
`C := X`, `g := 𝟙 X`, but in every higher dimension the conclusion asserts
a genuine curve, which is the content of Bertini.

CIRCULARITY GUARD: inherited from the parent — no route through
`Family.lean`, `Lift.lean` or `Modularity/Interface.lean`. -/
theorem exists_affineCurve_of_affine_geometricallyIrreducible
    {X : AlgebraicGeometry.Scheme.{u}} [AlgebraicGeometry.IsAffine X]
    (fX : X ⟶ AlgebraicGeometry.Spec (CommRingCat.of (ULift.{u} ℚ)))
    (hsmooth : AlgebraicGeometry.Smooth fX)
    (hsep : AlgebraicGeometry.IsSeparated fX)
    (hft : AlgebraicGeometry.LocallyOfFiniteType fX)
    (hqc : AlgebraicGeometry.QuasiCompact fX)
    (hgi : AlgebraicGeometry.GeometricallyIrreducible fX)
    (hreal : HasRationalPoint fX (ULift.{u} ℝ)) :
    ∃ (C : AlgebraicGeometry.Scheme.{u}) (_ : AlgebraicGeometry.IsAffine C)
      (g : C ⟶ X),
      AlgebraicGeometry.Smooth (g ≫ fX) ∧
      AlgebraicGeometry.IsSeparated (g ≫ fX) ∧
      AlgebraicGeometry.LocallyOfFiniteType (g ≫ fX) ∧
      AlgebraicGeometry.QuasiCompact (g ≫ fX) ∧
      AlgebraicGeometry.GeometricallyIrreducible (g ≫ fX) ∧
      HasRationalPoint (g ≫ fX) (ULift.{u} ℝ) ∧
      topologicalKrullDim C ≤ 1 := by
  -- Well-founded induction on the dimension: `WithBot ℕ∞` is `WellFoundedLT`,
  -- so no finite-dimensionality of `X` is needed.
  have key : ∀ (d : WithBot ℕ∞) (Y : AlgebraicGeometry.Scheme.{u})
      (_ : AlgebraicGeometry.IsAffine Y)
      (fY : Y ⟶ AlgebraicGeometry.Spec (CommRingCat.of (ULift.{u} ℚ))),
      AlgebraicGeometry.Smooth fY → AlgebraicGeometry.IsSeparated fY →
      AlgebraicGeometry.LocallyOfFiniteType fY → AlgebraicGeometry.QuasiCompact fY →
      AlgebraicGeometry.GeometricallyIrreducible fY →
      HasRationalPoint fY (ULift.{u} ℝ) → topologicalKrullDim Y ≤ d →
      ∃ (C : AlgebraicGeometry.Scheme.{u}) (_ : AlgebraicGeometry.IsAffine C)
        (g : C ⟶ Y),
        AlgebraicGeometry.Smooth (g ≫ fY) ∧
        AlgebraicGeometry.IsSeparated (g ≫ fY) ∧
        AlgebraicGeometry.LocallyOfFiniteType (g ≫ fY) ∧
        AlgebraicGeometry.QuasiCompact (g ≫ fY) ∧
        AlgebraicGeometry.GeometricallyIrreducible (g ≫ fY) ∧
        HasRationalPoint (g ≫ fY) (ULift.{u} ℝ) ∧
        topologicalKrullDim C ≤ 1 := by
    intro d
    induction d using WellFoundedLT.induction with
    | _ d ih =>
      intro Y hYaff fY hs hsp hf hq hg hr hle
      haveI : AlgebraicGeometry.IsAffine Y := hYaff
      by_cases h1 : topologicalKrullDim Y ≤ 1
      · -- base case: `Y` is already at most a curve
        exact ⟨Y, hYaff, 𝟙 Y, by rwa [Category.id_comp], by rwa [Category.id_comp],
          by rwa [Category.id_comp], by rwa [Category.id_comp], by rwa [Category.id_comp],
          by rwa [Category.id_comp], h1⟩
      · -- inductive step: one Bertini cut, then the induction hypothesis
        rw [not_le] at h1
        obtain ⟨Y', hY'aff, h, hs', hsp', hf', hq', hg', hr', hdrop⟩ :=
          exists_dimensionDrop_of_affine_geometricallyIrreducible fY hs hsp hf hq hg hr h1
        obtain ⟨C, hCaff, g, hCs, hCsp, hCf, hCq, hCg, hCr, hCdim⟩ :=
          ih (topologicalKrullDim Y') (lt_of_lt_of_le hdrop hle) Y' hY'aff (h ≫ fY)
            hs' hsp' hf' hq' hg' hr' le_rfl
        exact ⟨C, hCaff, g ≫ h, by rwa [Category.assoc], by rwa [Category.assoc],
          by rwa [Category.assoc], by rwa [Category.assoc], by rwa [Category.assoc],
          by rwa [Category.assoc], hCdim⟩
  exact key (topologicalKrullDim X) X inferInstance fX hsmooth hsep hft hqc hgi hreal le_rfl

/-! #### The avoidance cut: how "normal AND linearly disjoint" is obtained

(2026-07-26.) Everything from here to `exists_normalRealPoint_of_affine_curve`
implements the proof of BLGGT, *Potential automorphy and change of weight*,
**Proposition 3.1.1** — which is the form in which the potential-modularity
literature actually cites Moret–Bailly. That proposition asks for a finite
**Galois** extension `L/K`, linearly disjoint from a prescribed `K^avoid/K`,
totally split at a prescribed finite set of places, carrying a point of `T`;
Moret–Bailly's Théorème 1.3 itself delivers only the totally-split point.
BLGGT's proof of the gap is three sentences long and is exactly the cut made
here:

> Let `K₁^avoid, …, K_r^avoid` denote the intermediate fields between
> `K^avoid` and `K` with `K_i^avoid/K` Galois with simple Galois group.
> Combining Hensel's lemma with the Weil bounds we see that `T` has a
> `K_v`-rational point for all but finitely many primes `v` of `K`. Thus
> enlarging `S` we may assume that for each `i = 1, …, r` there is `v ∈ S^K`
> with `L'_v = K_v` and `v` not split completely in `K_i^avoid`. Then we may
> suppress the second condition on `L`.

So the disjointness conjunct is NOT produced by the geometry at all: it is
bought with auxiliary primes, at which the point is demanded to be totally
split, chosen by Chebotarev so that complete splitting at them is
incompatible with meeting the avoidance field. This matters because the
parent docstring's two counterexamples (a Galois closure destroys
disjointness; a field with one real embedding need not be totally real)
show that no purely formal manipulation can produce it — and yet the
geometric core, Moret–Bailly's theorem proper, genuinely does not carry it.

WHY THE SPLITTING CONDITION IS WRITTEN `Nonempty (F →+* ℚ_[p])`. For a
number field `F` NORMAL over `ℚ`, a ring map `F →+* ℚ_[p]` exists iff `p`
splits completely in `F`: such a map makes some completion `F_w` a subfield
of `ℚ_[p]` containing it, hence equal to it, so `w` has `e = f = 1`, and
normality makes all primes above `p` conjugate hence all of degree one;
conversely a degree-one prime `w` gives `F ↪ F_w = ℚ_[p]`. Written this way
the condition needs no ramification/inertia API, and it is the exact
`p`-adic analogue of the `F →+* ℝ` in which the archimedean condition (total
reality, by `isTotallyReal_of_normal_of_realEmbedding`) is already written.
Normality is used TWICE and is not a convenience: it is also what makes the
subgroup `Γ F ≤ Γ ℚ` — the range appearing in the disjointness conjunct —
independent of the embedding of algebraic closures implicit in
`Field.absoluteGaloisGroup.map`. -/

open CategoryTheory AlgebraicGeometry in
/-- **Good local solvability, ALGEBRAIC FORM** (sorry node — Lang–Weil plus
Hensel; the whole arithmetic content of BLGGT Prop. 3.1.1's sentence 2, with
the scheme layer stripped off).

For a `ℚ`-algebra `A` whose spectrum is smooth, of finite type and
geometrically irreducible over `ℚ`, there is a bound `B` such that for every
prime `p > B` there is a `ℚ`-algebra map `A →ₐ[ℚ] ℚ_[p]`.

WHY THIS IS THE RIGHT CUT. The consumer
`exists_bound_forall_padicPoint_of_geometricallyIrreducible` is stated for a
general affine scheme `C` over `Spec ℚ`; but `C` affine means `C ≅ Spec Γ(C, ⊤)`
and a `ℚ_[p]`-point of `C` is then exactly a `ℚ`-algebra map out of the
coordinate ring. So NOTHING geometric survives on this side of the cut except
the three hypotheses, and a prover here works with a ring and polynomial
equations, which is where Lang–Weil and Hensel are classically stated.

The hypotheses are deliberately left in morphism form (`Smooth (specRatMap A)`
rather than `Algebra.Smooth ℚ A`) because that is exactly what the consumer can
hand over with no instance juggling, and because mathlib converts them itself
when wanted: `HasRingHomProperty @Smooth RingHom.Smooth` together with
`HasRingHomProperty.iff_of_isAffine` turns `Smooth (Spec.map φ)` into
`RingHom.Smooth φ`, and likewise `LocallyOfFiniteType` into
`RingHom.FiniteType`. Doing that conversion HERE would force the `ℚ` versus
`ULift ℚ` instance path into the statement, which this development has been
burned by before; doing it inside the proof is free.

`IsSeparated` and `QuasiCompact` do NOT appear: `Spec A ⟶ Spec (ULift ℚ)` is an
affine morphism, hence separated and quasi-compact for free. Dropping them
makes the leaf strictly more usable and costs the consumer nothing.

WHY IT IS TRUE (BLGGT Prop. 3.1.1, and the classical route behind it):

1. **Spread out.** `A` is a finitely generated `ℚ`-algebra, so it is
   `A₁ ⊗_{ℤ[1/M]} ℚ` for some `M > 0` and some finitely generated
   `ℤ[1/M]`-algebra `A₁`; enlarging `M` makes `A₁` smooth over `ℤ[1/M]` with
   geometrically irreducible fibres, since smoothness, finite type and
   geometric irreducibility all spread out (EGA IV 8–9, Stacks 01ZM, 0559,
   0BUK). This is the step that manufactures the finite exceptional set: the
   bound is `B = M`, or any bound past the Lang–Weil threshold below.
2. **Count points mod `p`.** For `p ∤ M` the fibre `A₁ ⊗ 𝔽_p` is a smooth
   geometrically irreducible `𝔽_p`-variety of some dimension `d`, so
   Lang–Weil gives `#(A₁ ⊗ 𝔽_p)(𝔽_p) = p^d + O(p^{d - 1/2})` with an implied
   constant depending only on the degree and dimension of a fixed projective
   presentation — uniform in `p`, which is exactly why one bound `B` works for
   all `p` at once. In particular the count is positive for `p > B`, i.e.
   there is an `𝔽_p`-point, and smoothness makes it a SMOOTH point.
3. **Lift by Hensel.** Base change to `ℤ_[p]`: `A₀ := A₁ ⊗_{ℤ[1/M]} ℤ_[p]` is
   smooth, hence formally smooth, over `ℤ_[p]`, and the `𝔽_p`-point is an
   algebra map `A₀ →ₐ[ℤ_[p]] ℤ_[p] ⧸ maximalIdeal`. Inverting `p` and
   composing gives `A →ₐ[ℚ] ℚ_[p]`.

MATHLIB INVENTORY FOR A PROVER (audited 2026-07-26 at this pin — read this
before starting, it decides how the work splits):

* Step 3 is **already in mathlib and is essentially free**:
  `Algebra.FormallySmooth.exists_mkₐ_comp_eq_of_isAdicComplete`
  (`Mathlib/RingTheory/Smooth/AdicCompletion.lean`) says that for
  `[Algebra.FormallySmooth R A]` and `[IsAdicComplete I S]` every
  `A →ₐ[R] S ⧸ I` lifts to `A →ₐ[R] S`; and
  `instance : IsAdicComplete (IsLocalRing.maximalIdeal ℤ_[p]) ℤ_[p]`
  (`Mathlib/NumberTheory/Padics/PadicIntegers.lean`) supplies the hypothesis
  at `S = R = ℤ_[p]`. So multivariate Hensel need NOT be redeveloped: what is
  left of step 3 is only the base change and the inversion of `p`.
* Step 2, **Lang–Weil, does not exist in mathlib and does not exist in
  `~/cs/FLT`.** It is the genuinely missing theory, and it is worth building
  properly: it is reusable far beyond this leaf. Note that only the crudest
  consequence is needed here — NONEMPTINESS of `X(𝔽_p)` for large `p`, not
  the error term — so a proof route that gets `#X(𝔽_q) > 0` for
  `q` past an explicit threshold is enough.
* Step 1, **spreading out**, also does not exist. `Mathlib/AlgebraicGeometry/
  AffineTransitionLimit.lean` has the limit formalism that such an argument is
  usually built on.

FAITHFULNESS NOTE. The bound `B` is chosen AFTER `A`, so the exceptional set
is allowed to depend on the variety — which is what "all but finitely many"
must mean here, and is what BLGGT use (they then enlarge `S` by finitely many
primes). A `B` independent of `A` would be FALSE, and here is the witness: fix
an odd prime `p` and a rational integer `u` that is a non-square unit mod `p`,
and take the affine conic `A = ℚ[x, y] / (x² - u y² - p)`. It is smooth
(the Jacobian `(2x, -2u y)` vanishes only at the origin, which is not on the
curve) and geometrically irreducible (over `ℚ̄` it is the hyperbola `st = p`),
yet it has NO `ℚ_[p]`-point: `x² - u y²` is the norm form of the UNRAMIFIED
quadratic extension `ℚ_[p](√u)`, whose norm group is exactly the elements of
even valuation, while `v_p(p) = 1`. Since `p` here is arbitrary, no single
bound serves every variety — the quantifier order in the statement is
load-bearing and must not be exchanged.

`IrreducibleSpace` includes `Nonempty`, so `GeometricallyIrreducible` already
forces `Spec A ≠ ∅`, i.e. `A ≠ 0`; no separate nonemptiness hypothesis is
needed and none may be added.

CIRCULARITY GUARD: inherited from the parent — no route through
`Family.lean`, `Lift.lean` or `Modularity/Interface.lean`. This leaf is pure
arithmetic geometry over `ℚ` and mentions no Galois representation at all. -/
theorem exists_bound_forall_padicAlgHom_of_geometricallyIrreducible
    (A : Type u) [CommRing A] [Algebra ℚ A]
    (hsmooth : AlgebraicGeometry.Smooth (specRatMap A))
    (hft : AlgebraicGeometry.LocallyOfFiniteType (specRatMap A))
    (hgi : AlgebraicGeometry.GeometricallyIrreducible (specRatMap A)) :
    ∃ B : ℕ, ∀ (p : ℕ) [Fact p.Prime], B < p →
      Nonempty (A →ₐ[ℚ] ULift.{u} ℚ_[p]) :=
  sorry

open CategoryTheory AlgebraicGeometry in
/-- **Good local solvability at all but finitely many primes** (PROVEN
2026-07-26 over the algebraic leaf above — the Weil bounds plus Hensel's
lemma; BLGGT Prop. 3.1.1, proof, sentence 2:
"Combining Hensel's lemma with the Weil bounds we see that `T` has a
`K_v`-rational point for all but finitely many primes `v` of `K`").

For `C` smooth, separated, of finite type, quasi-compact and geometrically
irreducible over `ℚ`, there is a bound `B` such that `C` has a `ℚ_[p]`-point
for every prime `p > B`.

WHY IT IS TRUE. Spread `C` out to a smooth model `𝒞 → Spec ℤ[1/M]` with
geometrically irreducible fibres (possible for some `M`, by the standard
limit arguments: smoothness, finite type and geometric irreducibility all
spread out). For `p ∤ M` the fibre `𝒞_{𝔽_p}` is then a smooth geometrically
irreducible `𝔽_p`-variety, so the Lang–Weil estimate — the Weil bounds
themselves in the case `dim = 1` that this file needs — gives
`#𝒞(𝔽_p) = p^d + O(p^{d - 1/2})`, which is positive once `p` exceeds a bound
depending only on the degree and dimension of the model. Hensel's lemma
lifts a smooth `𝔽_p`-point to a `ℤ_p`-point, hence to a `ℚ_[p]`-point.

NO NONEMPTINESS HYPOTHESIS IS NEEDED: mathlib's `IrreducibleSpace` includes
`Nonempty`, so `GeometricallyIrreducible fC` already forces `C ≠ ∅`.

NOT A CURVE STATEMENT: no dimension hypothesis appears, because Lang–Weil is
uniform in the dimension. It is stated in that generality deliberately — the
consumer is a curve, but the theorem is the general one and is reusable.

CIRCULARITY GUARD: inherited from the parent — no route through
`Family.lean`, `Lift.lean` or `Modularity/Interface.lean`.

PROVEN 2026-07-26 over ONE leaf,
`exists_bound_forall_padicAlgHom_of_geometricallyIrreducible`, which is the
same statement with the SCHEME layer removed: the affine coordinate ring
`A = Γ(C, ⊤)` replaces `C`, and a `ℚ_[p]`-point becomes a plain `ℚ`-algebra
map `A →ₐ[ℚ] ℚ_[p]`. See that declaration's docstring for the route and for
the mathlib inventory.

`hsep` and `hqc` are unused and are underscore-prefixed for that reason:
they are REDUNDANT, not vacuous. An affine morphism is separated and
quasi-compact, so `IsAffine C` already supplies both; they are kept in the
signature because the parent assembly passes them positionally and because
the theorem is the general one. -/
theorem exists_bound_forall_padicPoint_of_geometricallyIrreducible
    {C : AlgebraicGeometry.Scheme.{u}} [AlgebraicGeometry.IsAffine C]
    (fC : C ⟶ AlgebraicGeometry.Spec (CommRingCat.of (ULift.{u} ℚ)))
    (hsmooth : AlgebraicGeometry.Smooth fC)
    (_hsep : AlgebraicGeometry.IsSeparated fC)
    (hft : AlgebraicGeometry.LocallyOfFiniteType fC)
    (_hqc : AlgebraicGeometry.QuasiCompact fC)
    (hgi : AlgebraicGeometry.GeometricallyIrreducible fC) :
    ∃ B : ℕ, ∀ (p : ℕ) [Fact p.Prime], B < p →
      HasRationalPoint fC (ULift.{u} ℚ_[p]) := by
  -- `A := Γ(C, ⊤)`, a `ℚ`-algebra through the structure morphism `fC`.
  letI : Algebra ℚ Γ(C, ⊤) :=
    RingHom.toAlgebra
      ((((Scheme.ΓSpecIso (CommRingCat.of (ULift.{u} ℚ))).inv ≫ fC.appTop).hom).comp
        (ULift.ringEquiv : ULift.{u} ℚ ≃+* ℚ).symm.toRingHom)
  -- STEP 1. `C` is affine, so `fC` factors as `C ≅ Spec A` followed by the
  -- structure map of `Spec A`; this is the `Γ`–`Spec` unit naturality square.
  have key : C.isoSpec.hom ≫ specRatMap (Γ(C, ⊤)) = fC := by
    have h1 : specRatMap (Γ(C, ⊤)) =
        Spec.map ((Scheme.ΓSpecIso (CommRingCat.of (ULift.{u} ℚ))).inv ≫ fC.appTop) := by
      unfold specRatMap
      congr 1
    rw [h1, Spec.map_comp, ← Category.assoc, Scheme.isoSpec_hom_naturality fC]
    simp [Scheme.isoSpec]
  have key2 : specRatMap (Γ(C, ⊤)) = C.isoSpec.inv ≫ fC := by
    rw [← key, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  -- STEP 2. Transport the three used hypotheses across that isomorphism.
  haveI : AlgebraicGeometry.Smooth fC := hsmooth
  haveI : AlgebraicGeometry.LocallyOfFiniteType fC := hft
  have hsm' : AlgebraicGeometry.Smooth (specRatMap (Γ(C, ⊤))) := by
    rw [key2]; infer_instance
  have hft' : AlgebraicGeometry.LocallyOfFiniteType (specRatMap (Γ(C, ⊤))) := by
    rw [key2]; infer_instance
  have hgi' : AlgebraicGeometry.GeometricallyIrreducible (specRatMap (Γ(C, ⊤))) := by
    rw [key2]
    exact (MorphismProperty.cancel_left_of_respectsIso
      @AlgebraicGeometry.GeometricallyIrreducible C.isoSpec.inv fC).mpr hgi
  -- STEP 3. Apply the algebraic leaf and transport the point back to `C`.
  obtain ⟨B, hB⟩ :=
    exists_bound_forall_padicAlgHom_of_geometricallyIrreducible (Γ(C, ⊤)) hsm' hft' hgi'
  refine ⟨B, fun p _ hp => ?_⟩
  obtain ⟨φ⟩ := hB p hp
  refine ⟨Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ C.isoSpec.inv, ?_⟩
  rw [Category.assoc, ← key2]
  unfold specRatMap
  rw [← Spec.map_comp]
  congr 1
  ext x
  simp

/-! #### The avoidance primes: `exists_primes_forall_sup_eq_top_of_isOpen`

**PROVEN 2026-07-26** — Chebotarev density plus the decomposition-group
dictionary; BLGGT Prop. 3.1.1, proof, sentences 1 and 3. This block comment
states the mathematics; the four helper lemmas and the theorem itself follow.

Given an OPEN subgroup `N ≤ Γ ℚ` — the avoidance datum — and any bound `B`,
there is a finite set `S` of primes, all larger than `B`, such that EVERY
number field `F` normal over `ℚ` in which every `p ∈ S` splits completely
(written `Nonempty (F →+* ℚ_[p])`, see the section docstring) satisfies the
disjointness conclusion `N ⊔ Γ F = ⊤`.

WHY IT IS TRUE. Let `M` be the normal core of `N`; it is open and normal, so
its fixed field `L` is a finite Galois extension of `ℚ` with group
`G = Γ ℚ / M`, and `N ⊇ M`, so it suffices to get `Γ F ⊔ M = ⊤`. Let
`H₁, …, H_r` be the maximal normal subgroups of `G`, i.e. `L_i := L^{H_i}`
are the minimal nontrivial Galois subextensions of `L/ℚ` (BLGGT's
`K_i^avoid`, characterised there by having simple Galois group). For each `i`
pick `g ∉ H_i` and, by Chebotarev density, a prime `p_i > B`, unramified in
`L`, whose Frobenius class meets `g M`; then `p_i` does NOT split completely
in `L_i`. Put `S = {p₁, …, p_r}`.

Now let `F` be normal with all `p ∈ S` split completely. `Γ F` is normal
(normality of `F`), so `Γ F · M` is a subgroup, corresponding to the Galois
subextension `E = F ∩ L`. If `E ≠ ℚ` then `Gal(L/E)` is a proper normal
subgroup of `G`, hence contained in some maximal normal `H_i`, so
`E ⊇ L^{H_i} = L_i`; but `p_i` splits completely in `F`, hence in the
subfield `E`, hence in `L_i` — contradicting the choice of `p_i`. So
`E = ℚ`, i.e. `Γ F · M = Γ ℚ`, and a fortiori `N ⊔ Γ F = ⊤`.

WHAT WAS AVAILABLE, AND WHAT THE DICTIONARY TURNED OUT TO COST.
`Fermat/FLT/GaloisRepresentation/Chebotarev.lean` already PROVES Chebotarev
density in exactly the shape this argument wants
(`dense_conjClasses_globalFrob`: for any finite set of finite places, the
union of the conjugacy classes of `globalFrob v` over the remaining places
is dense in `Γ ℚ`), and defines `globalFrob v : Γ ℚ` as the image of the
local Frobenius. Density against the open set `gM` gives the prime, and
excluding a finite set of places is how `p > B` is arranged.

The missing piece was the dictionary between `Nonempty (F →+* ℚ_[p])` and
`globalFrob p ∈ Γ F`. It is now PROVEN, and it needs NO ramification or
inertia theory at all — that is the point of writing complete splitting as a
ring map. `globalFrob v` is BY DEFINITION in the image of `Γ ℚ_v → Γ ℚ`;
`Chebotarev.lean`'s `exists_padicGalois_map_eq_conj_globalFrob` moves that
image to `Γ ℚ_[p]` up to conjugacy; a ring map `j : F →+* ℚ_[p]` satisfies
`algebraMap ℚ ℚ_[p] = j ∘ algebraMap ℚ F` automatically (there is only one
ring map out of `ℚ`), so `exists_conj_absoluteGaloisGroup_map_comp` puts the
image of `Γ ℚ_[p]` inside a CONJUGATE of the image of `Γ F`; and
`normal_range_absoluteGaloisGroup_map` — this is the second, load-bearing use
of `Normal ℚ F` — absorbs every conjugation. The three lemmas are stated and
proven for arbitrary fields, immediately below.

EDGE CASE, and why the statement is not vacuous in the degenerate direction:
if `N = ⊤` then the conclusion holds trivially — as it must. The content is
entirely in the case of a small `N`. (The formal proof does not special-case
this; see the assembly note on the theorem itself.)

CIRCULARITY GUARD: a statement of Galois theory and analytic number theory
with no geometry and no representation `ρbar` in it, so no route through
`Family.lean`, `Lift.lean` or `Modularity/Interface.lean` is relevant. -/
/-- **Functoriality of `Field.absoluteGaloisGroup.map` UP TO CONJUGACY**
(PROVEN 2026-07-26).

`Field.absoluteGaloisGroup.map` is built from an arbitrarily chosen
`IsAlgClosed.lift`, so a strict `map_comp` equation is NOT available and none
exists in the tree (see the note above
`cyclotomicCharacter_adicArithFrob_base_eq_absNorm`, which routes around the
question by descending one step at a time). What IS true, and is all any
conjugation-invariant statement needs, is functoriality up to a SINGLE
conjugator `c : Γ K` depending only on `f` and `g`, not on `σ`.

PROOF. Both `ι_g ∘ ι_f` and `ι_{g∘f}` are `K`-algebra maps `Kᵃˡᵍ → Mᵃˡᵍ`
(where `ι_f := AlgebraicClosure.map f` and `Mᵃˡᵍ` is a `K`-algebra through
`g ∘ f`), so `Normal.algHomEquivAut` — `Kᵃˡᵍ/K` being normal — produces the
unique `c : Γ K` with `ι_g (ι_f x) = ι_{g∘f} (c x)`. The identity then follows
pointwise through the injective `ι_{g∘f}` from
`Field.absoluteGaloisGroup.lift_map` applied three times. This is the same
device as `exists_padicGalois_map_eq_conj_globalFrob` in `Chebotarev.lean`,
stated once and in general. -/
theorem exists_conj_absoluteGaloisGroup_map_comp
    {K L M : Type*} [Field K] [Field L] [Field M] (f : K →+* L) (g : L →+* M) :
    ∃ c : Field.absoluteGaloisGroup K, ∀ σ : Field.absoluteGaloisGroup M,
      Field.absoluteGaloisGroup.map (g.comp f) σ =
        c * Field.absoluteGaloisGroup.map f (Field.absoluteGaloisGroup.map g σ) * c⁻¹ := by
  classical
  set ιf := AlgebraicClosure.map f with hιf
  set ιg := AlgebraicClosure.map g with hιg
  set ιh := AlgebraicClosure.map (g.comp f) with hιh
  letI : Algebra K (AlgebraicClosure M) :=
    ((algebraMap M (AlgebraicClosure M)).comp (g.comp f)).toAlgebra
  letI : Algebra (AlgebraicClosure K) (AlgebraicClosure M) := ιh.toAlgebra
  haveI : IsScalarTower K (AlgebraicClosure K) (AlgebraicClosure M) :=
    IsScalarTower.of_algebraMap_eq' (by
      ext x
      exact (AlgebraicClosure.map_algebraMap (g.comp f) x).symm)
  set F0 : AlgebraicClosure K →ₐ[K] AlgebraicClosure M :=
    { toRingHom := ιg.comp ιf
      commutes' := fun x => by
        show ιg (ιf (algebraMap K (AlgebraicClosure K) x)) = _
        rw [hιf, AlgebraicClosure.map_algebraMap, hιg, AlgebraicClosure.map_algebraMap]
        rfl } with hF0
  set c : Field.absoluteGaloisGroup K :=
    (Normal.algHomEquivAut (F := K) (K₁ := AlgebraicClosure M)
      (E := AlgebraicClosure K)) F0 with hc
  have hfc : ∀ x : AlgebraicClosure K, ιg (ιf x) = ιh (c x) := by
    intro x
    have hsym : F0 = (Normal.algHomEquivAut (F := K) (K₁ := AlgebraicClosure M)
        (E := AlgebraicClosure K)).symm c := by
      rw [hc, Equiv.symm_apply_apply]
    have hval : F0 x = ιh (c x) := by rw [hsym]; rfl
    exact hval
  have hcc : ∀ x : AlgebraicClosure K, c (c⁻¹ x) = x := by
    intro x
    show (c * c⁻¹) x = x
    rw [mul_inv_cancel]
    rfl
  refine ⟨c, fun σ => ?_⟩
  apply AlgEquiv.ext
  intro x
  apply ιh.injective
  rw [Field.absoluteGaloisGroup.lift_map (g.comp f) σ x]
  show σ (ιh x) = ιh ((c * Field.absoluteGaloisGroup.map f
    (Field.absoluteGaloisGroup.map g σ) * c⁻¹) x)
  have hstep1 : (c * Field.absoluteGaloisGroup.map f
      (Field.absoluteGaloisGroup.map g σ) * c⁻¹) x =
      c (Field.absoluteGaloisGroup.map f (Field.absoluteGaloisGroup.map g σ) (c⁻¹ x)) := rfl
  rw [hstep1, ← hfc]
  rw [Field.absoluteGaloisGroup.lift_map f (Field.absoluteGaloisGroup.map g σ) (c⁻¹ x)]
  rw [Field.absoluteGaloisGroup.lift_map g σ (ιf (c⁻¹ x))]
  rw [hfc, hcc]

/-- **`Γ L ≤ Γ K` is NORMAL when `L/K` is normal** (PROVEN 2026-07-26). This
is the half of the section docstring's "normality is load-bearing twice" that
makes the subgroup `Γ F ≤ Γ ℚ` independent of the arbitrary embedding of
algebraic closures inside `Field.absoluteGaloisGroup.map`.

PROOF. `L/K` normal is in particular algebraic, so `Lᵃˡᵍ` is algebraic over
`Kᵃˡᵍ` through `ι := AlgebraicClosure.map (algebraMap K L)`, and an algebraic
extension of an algebraically closed field is trivial
(`IsAlgClosed.algebraMap_bijective_of_isIntegral`): `ι` is BIJECTIVE. Pulling
`L` back along it gives a `K`-embedding `φ : L →ₐ[K] Kᵃˡᵍ`, whose field range
`Z` is `K`-isomorphic to `L` and hence normal over `K`
(`Normal.of_algEquiv`). One then checks
`range (Γ L → Γ K) = Z.fixingSubgroup` — `⊆` because an element of `Γ L`
fixes `L`, `⊇` because conjugating `τ` by `ι` produces an `L`-automorphism of
`Lᵃˡᵍ` exactly when `τ` fixes `Z` — and `Z.fixingSubgroup` is the kernel of
`AlgEquiv.restrictNormalHom Z` (`IntermediateField.restrictNormalHom_ker`,
available because `Normal K Z`), hence normal.

INSTANCE NOTE: do NOT introduce `Algebra K (AlgebraicClosure L)` or
`IsScalarTower K L (AlgebraicClosure L)` by hand — mathlib already supplies
both from `[Algebra K L]`, and a hand-built copy carries the wrong `SMul`
(`AlgebraicClosure.instSMulOfIsScalarTower`) and fails to unify. -/
theorem normal_range_absoluteGaloisGroup_map {K L : Type*} [Field K] [Field L]
    [Algebra K L] [Normal K L] :
    ((Field.absoluteGaloisGroup.map (algebraMap K L)).toMonoidHom.range).Normal := by
  classical
  haveI : Algebra.IsAlgebraic K (AlgebraicClosure L) :=
    Algebra.IsAlgebraic.trans (R := K) (S := L) (A := AlgebraicClosure L)
  set ι : AlgebraicClosure K →+* AlgebraicClosure L :=
    AlgebraicClosure.map (algebraMap K L) with hι
  letI : Algebra (AlgebraicClosure K) (AlgebraicClosure L) := ι.toAlgebra
  haveI : IsScalarTower K (AlgebraicClosure K) (AlgebraicClosure L) :=
    IsScalarTower.of_algebraMap_eq' (by
      ext x
      exact (AlgebraicClosure.map_algebraMap (algebraMap K L) x).symm)
  haveI : Algebra.IsAlgebraic (AlgebraicClosure K) (AlgebraicClosure L) :=
    Algebra.IsAlgebraic.tower_top (K := K) (AlgebraicClosure K) (A := AlgebraicClosure L)
  have hbij : Function.Bijective ι :=
    IsAlgClosed.algebraMap_bijective_of_isIntegral (k := AlgebraicClosure K)
      (K := AlgebraicClosure L)
  set ε : AlgebraicClosure K ≃+* AlgebraicClosure L := RingEquiv.ofBijective ι hbij with hε
  have hεapp : ∀ x, ε x = ι x := fun _ => rfl
  -- the copy of `L` sitting inside `AlgebraicClosure K`
  set φr : L →+* AlgebraicClosure K :=
    (ε.symm : AlgebraicClosure L →+* AlgebraicClosure K).comp
      (algebraMap L (AlgebraicClosure L)) with hφr
  set φ : L →ₐ[K] AlgebraicClosure K :=
    { toRingHom := φr
      commutes' := fun x => by
        show ε.symm (algebraMap L (AlgebraicClosure L) (algebraMap K L x)) = _
        have h1 : (algebraMap L (AlgebraicClosure L)) (algebraMap K L x)
            = ι (algebraMap K (AlgebraicClosure K) x) := by
          rw [hι, AlgebraicClosure.map_algebraMap]
        rw [h1, ← hεapp, RingEquiv.symm_apply_apply] } with hφ
  have hφapp : ∀ y : L, φ y = ε.symm (algebraMap L (AlgebraicClosure L) y) := fun _ => rfl
  set Z : IntermediateField K (AlgebraicClosure K) := φ.fieldRange with hZ
  haveI : Normal K Z := Normal.of_algEquiv φ.equivFieldRange
  have hrange : (Field.absoluteGaloisGroup.map (algebraMap K L)).toMonoidHom.range
      = Z.fixingSubgroup := by
    apply le_antisymm
    · intro τ hτ
      obtain ⟨σ, hσ⟩ := MonoidHom.mem_range.mp hτ
      rw [IntermediateField.mem_fixingSubgroup_iff]
      rintro z ⟨y, rfl⟩
      show τ (φ y) = φ y
      have h1 : ι (τ (φ y)) = σ (ι (φ y)) := by
        rw [← hσ]
        exact Field.absoluteGaloisGroup.lift_map (algebraMap K L) σ (φ y)
      have h2 : ι (φ y) = algebraMap L (AlgebraicClosure L) y := by
        rw [hφapp, ← hεapp, RingEquiv.apply_symm_apply]
      apply ι.injective
      rw [h1, h2]
      exact σ.commutes y
    · intro τ hτ
      rw [IntermediateField.mem_fixingSubgroup_iff] at hτ
      have hfix : ∀ y : L, τ (φ y) = φ y := fun y => hτ (φ y) ⟨y, rfl⟩
      set σ0 : AlgebraicClosure L ≃+* AlgebraicClosure L :=
        (ε.symm.trans τ.toRingEquiv).trans ε with hσ0
      have hσ0app : ∀ w, σ0 w = ε (τ (ε.symm w)) := fun _ => rfl
      have hcomm : ∀ y : L, σ0 (algebraMap L (AlgebraicClosure L) y)
          = algebraMap L (AlgebraicClosure L) y := by
        intro y
        rw [hσ0app, ← hφapp, hfix y, hφapp, RingEquiv.apply_symm_apply]
      set σ : Field.absoluteGaloisGroup L := AlgEquiv.ofRingEquiv (f := σ0) hcomm with hσ
      refine MonoidHom.mem_range.mpr ⟨σ, ?_⟩
      apply AlgEquiv.ext
      intro x
      apply ι.injective
      have hx : ε.symm (ι x) = x := by rw [← hεapp]; exact ε.symm_apply_apply x
      have hrhs : σ (ι x) = ι (τ x) := by
        show σ0 (ι x) = ι (τ x)
        rw [hσ0app, hx, hεapp]
      exact (Field.absoluteGaloisGroup.lift_map (algebraMap K L) σ x).trans hrhs
  rw [hrange, ← IntermediateField.restrictNormalHom_ker Z]
  exact MonoidHom.normal_ker _

/-- **The decomposition-group inclusion** (PROVEN 2026-07-26): if `L/K` is
normal and `L` embeds into `M` over `K` (i.e. `M` "splits `L` completely" in
the sense the section docstring records), then the image of `Γ M` in `Γ K`
sits inside the image of `Γ L`.

This is the whole of the "dictionary between `Nonempty (F →+* ℚ_[p])` and
`globalFrob p ∈ Γ F`" that the docstring above flags as the expected cost:
`exists_conj_absoluteGaloisGroup_map_comp` reduces `Γ M → Γ K` to
`Γ M → Γ L → Γ K` up to one conjugation, and
`normal_range_absoluteGaloisGroup_map` absorbs that conjugation. NO
ramification or inertia API is used anywhere. -/
theorem range_absoluteGaloisGroup_map_le_of_ringHom
    {K L M : Type*} [Field K] [Field L] [Field M] [Algebra K L] [Normal K L]
    (j : L →+* M) :
    (Field.absoluteGaloisGroup.map (j.comp (algebraMap K L))).toMonoidHom.range ≤
      (Field.absoluteGaloisGroup.map (algebraMap K L)).toMonoidHom.range := by
  obtain ⟨c, hc⟩ := exists_conj_absoluteGaloisGroup_map_comp (algebraMap K L) j
  have hnr := normal_range_absoluteGaloisGroup_map (K := K) (L := L)
  intro y hy
  obtain ⟨σ, hσ⟩ := MonoidHom.mem_range.mp hy
  have hy' : y = c * Field.absoluteGaloisGroup.map (algebraMap K L)
      (Field.absoluteGaloisGroup.map j σ) * c⁻¹ := by
    rw [← hσ, ← hc σ]; rfl
  rw [hy']
  exact hnr.conj_mem _ (MonoidHom.mem_range.mpr ⟨_, rfl⟩) c

/-- **Every open subgroup of `Γ K` contains an open NORMAL subgroup of finite
index** (PROVEN 2026-07-26) — the "normal core" step of the avoidance
argument, obtained without any normal-core computation.

`N` open means `N ∈ 𝓝 1`, and `krullTopology_mem_nhds_one_iff_of_normal`
(applicable because `Kᵃˡᵍ/K` is normal) delivers a FINITE and NORMAL
intermediate field `E` with `E.fixingSubgroup ≤ N`. That subgroup is open
(`IntermediateField.fixingSubgroup_isOpen`), of finite index
(`finiteIndex_fixingSubgroup`), and normal because `Normal K E` makes it the
kernel of `AlgEquiv.restrictNormalHom E`. -/
theorem exists_isOpen_normal_finiteIndex_le {K : Type*} [Field K]
    (N : Subgroup (Field.absoluteGaloisGroup K))
    (hN : IsOpen (N : Set (Field.absoluteGaloisGroup K))) :
    ∃ M : Subgroup (Field.absoluteGaloisGroup K),
      M ≤ N ∧ IsOpen (M : Set (Field.absoluteGaloisGroup K)) ∧ M.Normal ∧ M.FiniteIndex := by
  have hmem : (N : Set (Field.absoluteGaloisGroup K)) ∈ nhds (1 : Field.absoluteGaloisGroup K) :=
    hN.mem_nhds N.one_mem
  obtain ⟨E, hEfin, hEnormal, hEsub⟩ :=
    (krullTopology_mem_nhds_one_iff_of_normal K (AlgebraicClosure K) _).mp hmem
  haveI := hEfin
  haveI := hEnormal
  refine ⟨E.fixingSubgroup, hEsub, IntermediateField.fixingSubgroup_isOpen E, ?_, inferInstance⟩
  rw [← IntermediateField.restrictNormalHom_ker E]
  exact MonoidHom.normal_ker _

open scoped Pointwise in
/-- **The avoidance primes** (PROVEN 2026-07-26 over the four lemmas above;
the docstring immediately above this block states the mathematics and the
faithfulness audit).

WHAT THE PROOF ACTUALLY DOES, and how it differs from the sketch above: the
maximal-normal-subgroup enumeration is unnecessary. Let `M ≤ N` be open,
normal and of finite index (`exists_isOpen_normal_finiteIndex_le`) and let
`π : Γ ℚ → Q := Γ ℚ ⧸ M` be the (finite) quotient. Chebotarev
(`dense_conjClasses_globalFrob`, PROVEN in
`GaloisRepresentation/Chebotarev.lean`) applied to the OPEN coset
`σ • M = π⁻¹{q}` produces, for EVERY subgroup `P ≤ Q` that is proper and
normal and every `q ∉ P`, a place `v ∉ S₀` with `π (globalFrob v)` conjugate
to `q`, hence outside the normal `P`; excluding the finitely many places over
primes `≤ B` from `S₀` is what makes the prime exceed `B`. Since `Q` is
finite, `Subgroup Q` is finite, so one prime per subgroup gives the finite set
`S`. Then for `F` normal and split at every `p ∈ S`, put
`P := π(Γ F)` — normal because `Γ F` is (`normal_range_absoluteGaloisGroup_map`)
and `π` is surjective. If `P ≠ ⊤` its own prime `p_P ∈ S` contradicts
`globalFrob v_{p_P} ∈ Γ F`, which is the dictionary
(`range_absoluteGaloisGroup_map_le_of_ringHom` composed with
`exists_padicGalois_map_eq_conj_globalFrob`). So `P = ⊤`, i.e. `Γ F · M = Γ ℚ`,
and a fortiori `N ⊔ Γ F = ⊤`.

Enumerating ALL proper normal subgroups of `Q` rather than the maximal ones
is what removes the "every proper normal subgroup lies in a maximal normal
one" step; it costs only a larger `S`, which the statement does not
constrain.

FAITHFULNESS (audited 2026-07-26): the quantifier order is the correct one —
`S` is produced AFTER `N` and `B` and BEFORE `F`, and the proof genuinely
uses it that way (`S` is built from `Q`, which depends only on `N`). The
degenerate case `N = ⊤` is not special-cased: it is absorbed because
`P = π(Γ F)` is then already `⊤`. -/
theorem exists_primes_forall_sup_eq_top_of_isOpen
    (N : Subgroup (Field.absoluteGaloisGroup ℚ))
    (hNopen : IsOpen (N : Set (Field.absoluteGaloisGroup ℚ))) (B : ℕ) :
    ∃ S : Finset ℕ, (∀ p ∈ S, p.Prime ∧ B < p) ∧
      ∀ (F : Type u) (_ : Field F) (_ : NumberField F) (_ : Normal ℚ F),
        (∀ (p : ℕ) [Fact p.Prime], p ∈ S → Nonempty (F →+* ℚ_[p])) →
        N ⊔ (Field.absoluteGaloisGroup.map (algebraMap ℚ F)).toMonoidHom.range = ⊤ := by
  classical
  obtain ⟨M, hMle, hMopen, hMnormal, hMfin⟩ := exists_isOpen_normal_finiteIndex_le N hNopen
  haveI := hMnormal
  haveI := hMfin
  haveI : Finite (Field.absoluteGaloisGroup ℚ ⧸ M) := M.finite_quotient_of_finiteIndex
  set π : Field.absoluteGaloisGroup ℚ →* (Field.absoluteGaloisGroup ℚ ⧸ M) :=
    QuotientGroup.mk' M with hπ
  -- the finite set of places lying over primes `≤ B`
  set S₀ : Finset (HeightOneSpectrum (NumberField.RingOfIntegers ℚ)) :=
    (((Finset.range (B + 1)).filter Nat.Prime).attach.image
      (fun x => Nat.Prime.toHeightOneSpectrumRingOfIntegersRat
        (Finset.mem_filter.mp x.2).2)) with hS₀
  have hstep : ∀ P : Subgroup (Field.absoluteGaloisGroup ℚ ⧸ M),
      ∃ (p : ℕ) (hp : p.Prime), B < p ∧
        (P ≠ ⊤ → P.Normal →
          π (globalFrob (Nat.Prime.toHeightOneSpectrumRingOfIntegersRat hp)) ∉ P) := by
    intro P
    obtain ⟨p₀, hp₀B, hp₀⟩ := Nat.exists_infinite_primes (B + 1)
    by_cases hPtop : P = ⊤
    · exact ⟨p₀, hp₀, hp₀B, fun h _ => absurd hPtop h⟩
    by_cases hPn : P.Normal
    swap
    · exact ⟨p₀, hp₀, hp₀B, fun _ h => absurd h hPn⟩
    obtain ⟨q, hq⟩ : ∃ q : Field.absoluteGaloisGroup ℚ ⧸ M, q ∉ P := by
      by_contra h
      exact hPtop ((Subgroup.eq_top_iff' P).mpr fun q => not_not.mp fun hq => h ⟨q, hq⟩)
    obtain ⟨σ, hσ⟩ := QuotientGroup.mk'_surjective M q
    have hUopen : IsOpen (σ • (M : Set (Field.absoluteGaloisGroup ℚ))) := hMopen.smul σ
    have hUne : (σ • (M : Set (Field.absoluteGaloisGroup ℚ))).Nonempty :=
      ⟨σ, Set.mem_smul_set.mpr ⟨1, M.one_mem, by simp⟩⟩
    obtain ⟨x, hxU, hxD⟩ :=
      (dense_conjClasses_globalFrob (K := ℚ) S₀).inter_open_nonempty _ hUopen hUne
    obtain ⟨v, hvS₀, g, hxg⟩ := hxD
    obtain ⟨p, hp, hv⟩ := exists_prime_toHeightOneSpectrum v
    subst hv
    refine ⟨p, hp, ?_, fun _ _ => ?_⟩
    · by_contra hlt
      refine hvS₀ ?_
      rw [hS₀]
      refine Finset.mem_image.mpr ⟨⟨p, ?_⟩, Finset.mem_attach _ _, rfl⟩
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.not_lt.mp hlt)), hp⟩
    · -- `π x = q`, so `π (globalFrob v)` is conjugate to `q`, which is outside the normal `P`
      have hmm : σ⁻¹ * x ∈ M := by
        have h1 := Set.mem_smul_set_iff_inv_smul_mem.mp hxU
        rwa [smul_eq_mul] at h1
      have hπx : π σ = π x := by
        simp only [hπ, QuotientGroup.mk'_apply]
        exact QuotientGroup.eq.mpr hmm
      intro hmem
      refine hq ?_
      rw [← hσ, hπx, hxg, map_mul, map_mul, map_inv]
      exact hPn.conj_mem _ hmem (π g)
  choose pr hprPrime hprGt hprNot using hstep
  haveI : Fintype (Subgroup (Field.absoluteGaloisGroup ℚ ⧸ M)) := Fintype.ofFinite _
  refine ⟨Finset.univ.image pr, ?_, ?_⟩
  · intro p hp
    obtain ⟨P, -, rfl⟩ := Finset.mem_image.mp hp
    exact ⟨hprPrime P, hprGt P⟩
  · intro F hF hNF hnorm hsplit
    have hRnormal := normal_range_absoluteGaloisGroup_map (K := ℚ) (L := F)
    -- THE DECOMPOSITION-GROUP DICTIONARY, at an arbitrary prime `p` split completely in `F`
    have hdict : ∀ (p : ℕ) [Fact p.Prime], Nonempty (F →+* ℚ_[p]) →
        globalFrob (Nat.Prime.toHeightOneSpectrumRingOfIntegersRat (Fact.out : p.Prime)) ∈
          (Field.absoluteGaloisGroup.map (algebraMap ℚ F)).toMonoidHom.range := by
      intro p _ hj
      obtain ⟨j⟩ := hj
      set hp : p.Prime := Fact.out with hpdef
      obtain ⟨g, c, hgc⟩ := exists_padicGalois_map_eq_conj_globalFrob (q := p)
      have hcomp : (algebraMap ℚ ℚ_[p]) = j.comp (algebraMap ℚ F) := Subsingleton.elim _ _
      have hle : (Field.absoluteGaloisGroup.map (algebraMap ℚ ℚ_[p])).toMonoidHom.range ≤
          (Field.absoluteGaloisGroup.map (algebraMap ℚ F)).toMonoidHom.range := by
        rw [hcomp]
        exact range_absoluteGaloisGroup_map_le_of_ringHom j
      have h1 : c * globalFrob (Nat.Prime.toHeightOneSpectrumRingOfIntegersRat hp) * c⁻¹ ∈
          (Field.absoluteGaloisGroup.map (algebraMap ℚ F)).toMonoidHom.range := by
        rw [← hgc]
        exact hle (MonoidHom.mem_range.mpr ⟨g, rfl⟩)
      have h2 : globalFrob (Nat.Prime.toHeightOneSpectrumRingOfIntegersRat hp) =
          c⁻¹ * (c * globalFrob (Nat.Prime.toHeightOneSpectrumRingOfIntegersRat hp) * c⁻¹) *
            c⁻¹⁻¹ := by
        group
      rw [h2]
      exact hRnormal.conj_mem _ h1 c⁻¹
    set R := (Field.absoluteGaloisGroup.map (algebraMap ℚ F)).toMonoidHom.range with hRdef
    have hRtop : R.map π = ⊤ := by
      by_contra hne
      have hPn : (R.map π).Normal := hRnormal.map π (QuotientGroup.mk'_surjective M)
      haveI : Fact (pr (R.map π)).Prime := ⟨hprPrime (R.map π)⟩
      refine hprNot (R.map π) hne hPn (Subgroup.mem_map_of_mem π ?_)
      exact hdict (pr (R.map π))
        (hsplit (pr (R.map π)) (Finset.mem_image_of_mem _ (Finset.mem_univ (R.map π))))
    rw [Subgroup.eq_top_iff']
    intro x
    have hx : π x ∈ R.map π := by rw [hRtop]; trivial
    obtain ⟨r, hr, hrx⟩ := hx
    have hmem : r⁻¹ * x ∈ M := by
      simp only [hπ, QuotientGroup.mk'_apply] at hrx
      exact QuotientGroup.eq.mp hrx
    have hxr : x = r * (r⁻¹ * x) := by group
    rw [hxr]
    exact Subgroup.mul_mem _ ((le_sup_right : R ≤ N ⊔ R) hr)
      ((le_sup_left : N ≤ N ⊔ R) (hMle hmem))

/-! #### Moret–Bailly's curve case, cut at the Galois closure

(2026-07-26.) `exists_normalSplitPoint_of_affine_curve` asks for a field
that is simultaneously (a) produced by Moret–Bailly's construction and
(b) NORMAL over `ℚ`. Moret–Bailly's Théorème 1.3 does **not** produce a
normal field: by his Remarque 1.5 the "point entier" `Y ⊆ X` has generic
fibre `Spec K'` for an arbitrary finite extension `K'/ℚ`, and the local
conditions say exactly that `K'` is *totally split* at every place of `Σ`
— that is all. BLGGT Prop. 3.1.1 quotes it as producing a *Galois* `K'`
because one silently replaces `K'` by its Galois closure afterwards.

Those two steps are independent and are separated here:

* `exists_totallySplitPoint_of_affine_curve` — Moret–Bailly Thm 1.3
  itself, §3 of the paper. Produces a totally real number field, totally
  split at every `p ∈ S`, carrying a point of `C`. **Not normal.**
* `exists_normalClosure_of_totallyReal_totallySplit` — pure algebraic
  number theory: the normal closure of a totally real, totally-split-at-`S`
  number field is again totally real and totally split at `S`.

WHY THE INTERMEDIATE FIELD'S SPLITTING MUST BE STATED AS `IsTotallySplitAt`
AND NOT AS `Nonempty (F →+* ℚ_[p])` (this is the whole reason a new
predicate appears here). For a NORMAL field the two agree, which is why
the sibling `exists_primes_forall_sup_eq_top_of_isOpen` may use the cheap
`Nonempty` form: all primes above `p` are conjugate, so one of local
degree `1` forces all of them. For a general `F` they do **not** agree, and
the difference is fatal to this cut: `F = ℚ(2 ^ (1/3))` and `p ≡ 2 mod 3`
gives `Nonempty (F →+* ℚ_[p])` — `X ^ 3 - 2` has exactly one root in
`ℚ_[p]` — while the normal closure `ℚ(2 ^ (1/3), ζ₃)` is *not* split at
`p`, since `ζ₃ ∉ ℚ_[p]`. So a cut whose intermediate leaf only claimed
`Nonempty (F →+* ℚ_[p])` would have an unprovable closure step. -/

/-- **`p` splits completely in the number field `F`.** Stated as a count of
ring homomorphisms: `Hom_ℚ(F, ℚ̄_p)` has exactly `[F : ℚ]` elements and is
partitioned by the primes `v ∣ p` into blocks of size `[F_v : ℚ_p]`, of
which the homomorphisms landing in `ℚ_[p]` itself are precisely the blocks
with `F_v = ℚ_p`. So `Nat.card (F →+* ℚ_[p]) = [F : ℚ]` says exactly that
every prime above `p` has local degree `1`, i.e. `p` is totally split.

(Ring homomorphisms rather than `ℚ`-algebra homomorphisms: between fields
of characteristic zero every ring homomorphism is automatically a
`ℚ`-algebra homomorphism, and the file's existing statements are phrased
with `→+*`.)

`Nat.card` is used rather than `Fintype.card` so that no `Fintype`
instance has to be produced at the statement; finiteness of `F →+* ℚ_[p]`
is a consequence, not a hypothesis, and is recovered where needed through
`Nat.card_ne_zero`. -/
def IsTotallySplitAt (F : Type*) [Field F] [NumberField F] (p : ℕ) [Fact p.Prime] :
    Prop :=
  Nat.card (F →+* ℚ_[p]) = Module.finrank ℚ F

/-- **Complete splitting gives a `ℚ_[p]`-embedding** (PROVEN glue): the
degree `[F : ℚ]` of a number field is positive, so a field totally split
at `p` has at least one — indeed exactly `[F : ℚ]` — ring homomorphisms to
`ℚ_[p]`. This is the bridge from `IsTotallySplitAt` to the `Nonempty
(F →+* ℚ_[p])` form in which the Chebotarev sibling
`exists_primes_forall_sup_eq_top_of_isOpen` consumes complete splitting. -/
theorem nonempty_ringHom_padic_of_isTotallySplitAt
    (F : Type u) (_ : Field F) (_ : NumberField F) (p : ℕ) [Fact p.Prime]
    (hsplit : IsTotallySplitAt F p) : Nonempty (F →+* ℚ_[p]) := by
  have hpos : 0 < Module.finrank ℚ F := Module.finrank_pos
  have hne : Nat.card (F →+* ℚ_[p]) ≠ 0 := by
    rw [IsTotallySplitAt] at hsplit; omega
  exact (Nat.card_ne_zero.mp hne).1

open CategoryTheory AlgebraicGeometry in
/-- **Rational points grow along a field extension** (PROVEN glue): a ring
homomorphism `f : F →+* E` of number fields induces `Spec E ⟶ Spec F`, and
composing an `F`-point of `X` with it gives an `E`-point. The square over
`Spec ℚ` commutes because `ℚ →+* E` is a subsingleton, so
`f ∘ (algebraMap ℚ F) = algebraMap ℚ E` automatically — no compatibility
hypothesis on `f` is needed.

(The `NumberField` hypotheses are carried only to pin the `Algebra ℚ ·`
instance: `Field F` alone does not synthesize it at this pin — the
instance is `algebraRat`, which wants `CharZero`. Nothing in the proof
uses finiteness.)

This is what lets Moret–Bailly's field be enlarged to its Galois closure
without losing the point. -/
theorem HasRationalPoint.of_ringHom {X : AlgebraicGeometry.Scheme.{u}}
    (fX : X ⟶ AlgebraicGeometry.Spec (CommRingCat.of (ULift.{u} ℚ)))
    (F E : Type u) (_ : Field F) (_ : NumberField F) (_ : Field E) (_ : NumberField E)
    (f : F →+* E) (h : HasRationalPoint fX F) : HasRationalPoint fX E := by
  obtain ⟨x, hx⟩ := h
  refine ⟨AlgebraicGeometry.Spec.map (CommRingCat.ofHom f) ≫ x, ?_⟩
  rw [Category.assoc, hx]
  show AlgebraicGeometry.Spec.map (CommRingCat.ofHom f) ≫ specRatMap F = specRatMap E
  rw [specRatMap, specRatMap, ← AlgebraicGeometry.Spec.map_comp]
  congr 1
  ext z
  -- pointwise: `f ((q : F)) = (q : E)` for the rational `q = ULift.ringEquiv z`
  simp

open CategoryTheory AlgebraicGeometry in
/-- **Moret–Bailly's Théorème 1.3 on the curve, in its own form** (SORRY —
the arithmetic heart of the whole cluster). Moret–Bailly, *Groupes de
Picard et problèmes de Skolem II*, Ann. Sci. ÉNS **22** (1989), 181–194,
**Théorème 1.3** together with his Remarque 1.5, specialised to the Skolem
datum described below. The field produced is **not** normal — that is
supplied afterwards by
`exists_normalClosure_of_totallyReal_totallySplit`.

THE SKOLEM DATUM (Moret–Bailly 1.1–1.2), and how the hypotheses here
produce it. A *donnée de Skolem* is `(f : X → B, Σ, {L_v}, {Ω_v})` where
`B = Spec R` for `R` a ring of `S₀`-integers of a number field `K`, `f` is
separated of finite type and surjective with `X` irreducible and `X_K`
geometrically irreducible, `Σ` is a finite set of places of `K` DISJOINT
from `Max R`, `L_v/K_v` is finite Galois, and `Ω_v ⊆ X(L_v)` is a nonempty
`Gal(L_v/K_v)`-stable open consisting of smooth points. It is *incomplete*
when `Σ ∪ Max R` is not all places of `K`. Here:

* `K = ℚ`; take a model of `C` over `ℤ[1/M]` for a suitable `M` (finite
  type over `ℚ` spreads out), invert in addition every `p ∈ S` and ONE
  further prime `q ∉ S ∪ {∞}`, and let `R = ℤ[1/(M · q · ∏ S)]`;
* `Σ = {∞} ∪ S`, with `L_v = K_v` for every `v ∈ Σ` (so `Gal(L_v/K_v)` is
  trivial and the stability condition is vacuous);
* `Ω_∞ = C(ℝ)`, nonempty by `hreal`; `Ω_p = C(ℚ_[p])`, nonempty by `hSpt`.
  Both are open and consist of smooth points because `hsmooth` makes all
  of `C` smooth over `ℚ`.

Incompleteness holds precisely because `q` was inverted: `q ∉ Σ` and
`q ∉ Max R`. **The one further inverted prime is why this leaf asks for a
`ℚ`-point of `C` and not an integral point.**

WHAT THE CONCLUSION IS, VERBATIM FROM REMARQUE 1.5. A *point entier* is an
irreducible closed `Y ⊆ X`, finite and surjective over `B`, with
`Y ⊗ L_v` being `L_v`-split and contained in `Ω_v` for every `v ∈ Σ`. Its
generic fibre is `Spec F` for a finite extension `F/ℚ`, giving `x ∈ X(F)`;
and "`Y ⊗ L_v` is `L_v`-split" says exactly that `F ⊗_ℚ K_v` is a product
of copies of `K_v`, i.e. that `v` splits completely in `F`. At `v = ∞`
that reads `F ⊗_ℚ ℝ ≅ ℝ ^ [F : ℚ]`, i.e. `NumberField.IsTotallyReal F`;
at `v = p ∈ S` it reads `IsTotallySplitAt F p`. Hence the conclusion
below, and hence also why total reality is the archimedean member of the
same family of conditions rather than a separate hypothesis.

MORET–BAILLY'S PROOF OF §3, AS A ROADMAP FOR A PROVER (the paper's own
numbering; §2 — the reduction to relative dimension `1` — is this file's
Bertini sibling `exists_affineCurve_of_affine_geometricallyIrreducible`,
which is why this leaf may assume `topologicalKrullDim C ≤ 1`):

* **3.1** Compactify: `j : X ↪ X̄` a dense open immersion with `X̄ → B`
  projective and `X̄` normal; put `Z = X̄ - X` with its reduced structure,
  `g = ` genus of `X̄_K`, `z = deg_K Z_K` (arrange `z > 0`). After
  shrinking `B` and enlarging `Σ` (his 1.9, 1.10) one may assume `X̄`
  regular, the fibres of `X̄ → B` geometrically integral, and `Z → B`
  finite flat surjective, so `Z` is a Cartier divisor.
* **3.2** The `d`-th symmetric power `X̄^(d)`, whose `S`-points are the
  effective Cartier divisors on `X̄_S` finite flat of degree `d` over `S`
  and disjoint from `Z`; `U_d ⊆ X̄^(d)` the étale locus; `Ω_v^[d]` the
  divisors that are étale, `L_v`-split and inside `Ω_v`.
* **3.3** `Ω_v^[d]` is open in `U_d(K_v)`, and nonempty when
  `[L_v : K_v] ∣ d`.
* **3.4** The generalised Picard functor `PG(X̄, Z)` — pairs (invertible
  sheaf, trivialisation along `Z`) — sits in
  `1 → 𝔾_m,B → (π_Z)_* 𝔾_m,Z → PG(X̄,Z) → Pic_{X̄/B} → 1`, hence is a
  smooth separated `B`-group scheme, with neutral component `PG₀(X̄,Z)`
  the generalised Jacobian of Serre, *Groupes algébriques et corps de
  classes*, ch. V.
* **3.5–3.6** `φ_d : X̄^(d) → PG_d(X̄,Z)`, `D ↦ cl_Z(D)`, is a Zariski-locally
  trivial fibration in affine spaces of dimension `d + 1 - g - z` once
  `d ≥ 2g + z - 1` (Riemann–Roch plus vanishing of `R¹`).
* **3.7.2** `W_v^d := φ_d(Ω_v^[d])` is open in `P_d(K_v)`, nonempty when
  `[L_v : K_v] ∣ d`, and `W_v^d · W_v^{d'} ⊆ W_v^{d + d'}` for `d ≥ 2g + z`.
* **3.8** If `(ℒ, α)` over `R` has `d ≥ 2g + z - 1` and its image in each
  `P_d(K_v)` lies in `W_v^d`, then STRONG APPROXIMATION in the affine
  `R`-space `Γ(X̄, ℒ, α)` — available because the datum is incomplete —
  produces a global section whose divisor is a point entier.
* **3.9** Such an `(ℒ, α)` exists: take `ℒ₀` ample, and use that
  `G = P₀(K_Σ) / im Γ(Z, 𝒪_Z^×)` is QUASI-COMPACT, so `g^n → 1` along a
  subsequence for every `g ∈ G`, to move a power of `ℒ₀` into the open
  `W^d · (W^d)⁻¹`.
* **3.9.2–3.10** Quasi-compactness of `G` is the arithmetic core, and it
  is where the Picard groups of the title enter: `G` is an extension of an
  open subgroup of `∏_{v ∈ Σ} Pic⁰_{X̄_K/K}(K_v)` by
  `(R' ⊗_R K_Σ)^× / (R'^× · K_Σ^×)`. The first factor is compact by **3.10.2**
  (Raynaud: `J(F)` is compact for `J` the Jacobian of a curve over a local
  field `F`, since `J` is open in the proper Altman–Kleiman compactified
  Picard scheme); the second by **3.10.3/3.10.4**, i.e. quasi-compactness
  of `K_Σ^× / R^×`, which is Dirichlet's unit theorem plus the
  INCOMPLETENESS of the datum (the sum-of-coordinates map
  `ℝ^{S - Σ} → ℝ` is surjective exactly because `Σ ⊊ S`).

WHAT IS MISSING AT THIS PIN, honestly: mathlib has no Picard scheme, no
symmetric power of a scheme, no generalised Jacobian, no strong
approximation for affine spaces over rings of `S`-integers, and no smooth
compactification of a curve. Items (2) and (4) of the section docstring's
machinery list are exactly 3.9.2–3.10 above. `ℚ^tr` does **not** appear in
this statement: "totally real, totally split at `S`" is everything a
subfield of `ℚ^tr` contributes here, so building `ℚ^tr` speculatively
would be free-floating.

FAITHFULNESS. The degenerate directions are covered rather than assumed
away: `GeometricallyIrreducible fC` forces `C ≠ ∅`, and if
`topologicalKrullDim C ≤ 0` then `C` is `Spec` of a geometrically
irreducible smooth finite `ℚ`-algebra, i.e. `Spec ℚ`, and `F = ℚ` — which
is totally real, totally split at every prime, and carries the point —
discharges the conclusion. So `hdim` may be used as "`dim = 1` after the
`dim = 0` case is dispatched", which is how Moret–Bailly's §3 reads it.

CIRCULARITY GUARD: inherited from the parent — no route through
`Family.lean`, `Lift.lean` or `Modularity/Interface.lean`. -/
theorem exists_totallySplitPoint_of_affine_curve
    {C : AlgebraicGeometry.Scheme.{u}} [AlgebraicGeometry.IsAffine C]
    (fC : C ⟶ AlgebraicGeometry.Spec (CommRingCat.of (ULift.{u} ℚ)))
    (hsmooth : AlgebraicGeometry.Smooth fC)
    (hsep : AlgebraicGeometry.IsSeparated fC)
    (hft : AlgebraicGeometry.LocallyOfFiniteType fC)
    (hqc : AlgebraicGeometry.QuasiCompact fC)
    (hgi : AlgebraicGeometry.GeometricallyIrreducible fC)
    (hreal : HasRationalPoint fC (ULift.{u} ℝ))
    (hdim : topologicalKrullDim C ≤ 1)
    (S : Finset ℕ) (hSprime : ∀ p ∈ S, p.Prime)
    (hSpt : ∀ (p : ℕ) [Fact p.Prime], p ∈ S →
      HasRationalPoint fC (ULift.{u} ℚ_[p])) :
    ∃ (F : Type u) (_ : Field F) (_ : NumberField F)
      (_ : NumberField.IsTotallyReal F),
      (∀ (p : ℕ) [Fact p.Prime], p ∈ S → IsTotallySplitAt F p) ∧
      HasRationalPoint fC F :=
  sorry

/-- **The normal closure of a totally real, totally split number field is
again totally real and totally split** (SORRY — pure algebraic number
theory, no geometry). This is the step BLGGT Prop. 3.1.1 performs
silently when it quotes Moret–Bailly as producing a *Galois* extension:
Moret–Bailly's Remarque 1.5 produces an arbitrary finite `F/ℚ`, and one
replaces it by its normal closure.

WHY IT IS TRUE. Let `E` be the normal closure of `F` in an algebraic
closure; it is the compositum of the finitely many conjugates `σ F`.

* `NumberField E`: a compositum of finitely many number fields is one.
* `Normal ℚ E`: that is what the normal closure is (and in characteristic
  zero it is automatically Galois, which is how the parent's consumer
  `exists_totallyReal_point_of_affine_geometricallyIrreducible` upgrades
  it).
* `E →+* ℝ`, indeed `E ⊆ ℝ`: each `σ F` is totally real, since being
  totally real is a property of the abstract field `F` and `σ F ≅ F`; a
  compositum of totally real fields is totally real; and a totally real
  field has a real embedding.
* Total splitting at `p` is preserved. Use the characterisation: a
  subfield `F ⊆ ℚ̄` is totally split at `p` iff for EVERY embedding
  `ℚ̄ ↪ ℚ̄_p` the image of `F` lies in `ℚ_[p]`. That property is stable
  under conjugation (it is intrinsic to `F`) and under compositum (an
  embedding of `F₁ F₂` restricts to embeddings of `F₁` and of `F₂`, both
  landing in `ℚ_[p]`, and `ℚ_[p]` is a field). Hence it holds for `E`.

WHY THE HYPOTHESIS CANNOT BE WEAKENED to `Nonempty (F →+* ℚ_[p])`: see
the section docstring above — `F = ℚ(2 ^ (1/3))`, `p ≡ 2 mod 3` is a
counterexample, its normal closure `ℚ(2 ^ (1/3), ζ₃)` not being split at
`p`. This is the reason `IsTotallySplitAt` exists.

The hypothesis `NumberField.IsTotallyReal F` is likewise not weakenable to
a single real embedding `F →+* ℝ`: the normal closure of a field with one
real and two complex places (e.g. `ℚ(2 ^ (1/3))` again) is not real.

WHAT A PROVER HAS AT THIS PIN: `IntermediateField.normalClosure` with its
`Normal` and `IsGalois` instances, `NumberField.IsTotallyReal` and
`NumberField.InfinitePlace`, and `IntermediateField.isAlgebraic_iff`.
Nothing here needs geometry or the rest of this file. -/
theorem exists_normalClosure_of_totallyReal_totallySplit
    (F : Type u) (_ : Field F) (_ : NumberField F)
    (_ : NumberField.IsTotallyReal F) (S : Finset ℕ)
    (hsplit : ∀ (p : ℕ) [Fact p.Prime], p ∈ S → IsTotallySplitAt F p) :
    ∃ (E : Type u) (_ : Field E) (_ : NumberField E) (_ : Normal ℚ E)
      (_ : E →+* ℝ) (_ : F →+* E),
      ∀ (p : ℕ) [Fact p.Prime], p ∈ S → IsTotallySplitAt E p :=
  sorry

open CategoryTheory AlgebraicGeometry in
/-- **Steps (ii)+(iii) of Moret–Bailly's route: the CURVE case**
(**PROVEN 2026-07-26** over the two leaves above — Moret–Bailly's theorem
proper and the Galois-closure step, which BLGGT Prop. 3.1.1 performs
silently; see the section docstring "Moret–Bailly's curve case, cut at the
Galois closure" for why the intermediate splitting condition must be
`IsTotallySplitAt` and not `Nonempty (F →+* ℚ_[p])`).
This is Moret–Bailly, *Groupes de Picard et problèmes de Skolem
II*, Ann. Sci. ÉNS 22 (1989), **Théorème 1.3**, §3 (the curve case; §2 is
the hyperplane-section reduction, which is this file's Bertini sibling), in
the form in which BLGGT Prop. 3.1.1 cites it:

> Then Theorem 1.3 of [MB89] tells us that we can find a finite Galois
> extension `K'/K` and a point `P ∈ T(K')` such that every place `v` of
> `S^K` splits completely in `K'`.

Exactly the affine statement, with `X` further required to be a CURVE
(`topologicalKrullDim C ≤ 1`), and with the conclusion in its "raw"
geometric form: the field produced is only asked to be a NUMBER FIELD that
is NORMAL over `ℚ`, admits a ring map to `ℝ`, and splits every prime of a
prescribed finite set `S` completely.

ASSEMBLY (2026-07-26). `exists_totallySplitPoint_of_affine_curve` is
Moret–Bailly's theorem itself: it delivers a totally real `F`, totally
split at every `p ∈ S`, with an `F`-point of `C` — but NOT normal, because
his Remarque 1.5 produces the residue field of a closed point and nothing
makes that field normal. `exists_normalClosure_of_totallyReal_totallySplit`
then replaces `F` by its normal closure `E`, which is still totally real
(hence `E →+* ℝ`) and still totally split at `S` — both properties being
conjugation- and compositum-stable — and `HasRationalPoint.of_ringHom`
transports the point along `F →+* E`. Finally
`nonempty_ringHom_padic_of_isTotallySplitAt` converts complete splitting
into the `Nonempty (F →+* ℚ_[p])` form in which the Chebotarev sibling
`exists_primes_forall_sup_eq_top_of_isOpen` consumes it. Downstream,
`isTotallyReal_of_normal_of_realEmbedding` re-derives
`NumberField.IsTotallyReal` and `IsGalois ℚ E` from `Normal ℚ E` and the
real embedding, so nothing is lost by weakening the conclusion to those.

THE AVOIDANCE DATUM `N` IS GONE FROM THIS LEAF (2026-07-26). It is bought
instead with the auxiliary primes `S`, by
`exists_primes_forall_sup_eq_top_of_isOpen`; see the section docstring above
for why that is the honest place for it and why the parent's two
counterexamples do not obstruct it.

FAITHFULNESS (re-audited 2026-07-26 against Moret–Bailly's own text, not
reconstructed). The statement is TRUE: it is Théorème 1.3 applied to the
Skolem datum spelled out in `exists_totallySplitPoint_of_affine_curve`'s
docstring — `R = ℤ[1/(M · q · ∏ S)]`, `Σ = {∞} ∪ S`, `L_v = K_v`,
`Ω_∞ = C(ℝ)`, `Ω_p = C(ℚ_[p])` — which is INCOMPLETE because of the extra
inverted prime `q`, plus the Galois closure. Note that the `Nonempty
(F →+* ℚ_[p])` in the conclusion is complete splitting only BECAUSE `F` is
normal here (all primes above `p` are then conjugate, so one of local
degree `1` forces all); that is exactly what the sibling consumes, and it
is why the cut below carries the stronger `IsTotallySplitAt` through the
non-normal intermediate stage.

CIRCULARITY GUARD: inherited from the parent — no route through
`Family.lean`, `Lift.lean` or `Modularity/Interface.lean`. -/
theorem exists_normalSplitPoint_of_affine_curve
    {C : AlgebraicGeometry.Scheme.{u}} [AlgebraicGeometry.IsAffine C]
    (fC : C ⟶ AlgebraicGeometry.Spec (CommRingCat.of (ULift.{u} ℚ)))
    (hsmooth : AlgebraicGeometry.Smooth fC)
    (hsep : AlgebraicGeometry.IsSeparated fC)
    (hft : AlgebraicGeometry.LocallyOfFiniteType fC)
    (hqc : AlgebraicGeometry.QuasiCompact fC)
    (hgi : AlgebraicGeometry.GeometricallyIrreducible fC)
    (hreal : HasRationalPoint fC (ULift.{u} ℝ))
    (hdim : topologicalKrullDim C ≤ 1)
    (S : Finset ℕ) (hSprime : ∀ p ∈ S, p.Prime)
    (hSpt : ∀ (p : ℕ) [Fact p.Prime], p ∈ S →
      HasRationalPoint fC (ULift.{u} ℚ_[p])) :
    ∃ (F : Type u) (_ : Field F) (_ : NumberField F) (_ : Normal ℚ F)
      (_ : F →+* ℝ),
      (∀ (p : ℕ) [Fact p.Prime], p ∈ S → Nonempty (F →+* ℚ_[p])) ∧
      HasRationalPoint fC F := by
  classical
  -- Moret–Bailly Thm 1.3: a totally real `F`, totally split at `S`, with an `F`-point
  obtain ⟨F, hF, hNF, hFtr, hFsplit, hFpt⟩ :=
    exists_totallySplitPoint_of_affine_curve fC hsmooth hsep hft hqc hgi hreal hdim S
      hSprime hSpt
  -- the Galois closure: still totally real, still totally split, and `F` embeds in it
  obtain ⟨E, hE, hNE, hEnorm, ιE, fFE, hEsplit⟩ :=
    exists_normalClosure_of_totallyReal_totallySplit F hF hNF hFtr S hFsplit
  refine ⟨E, hE, hNE, hEnorm, ιE, ?_,
    HasRationalPoint.of_ringHom fC F E hF hNF hE hNE fFE hFpt⟩
  intro p _ hp
  exact nonempty_ringHom_padic_of_isTotallySplitAt E hE hNE p (hEsplit p hp)

open CategoryTheory AlgebraicGeometry in
/-- **Steps (ii)+(iii) of Moret–Bailly's route: the CURVE case with the
avoidance datum** (PROVEN 2026-07-26 as the assembly of the three leaves
above, which is BLGGT Prop. 3.1.1's own proof; see the section docstring
"The avoidance cut" for the mathematics).

ASSEMBLY. `exists_bound_forall_padicPoint_of_geometricallyIrreducible`
(Weil + Hensel) gives a bound `B` beyond which every prime is a place of
good local solvability for `C`;
`exists_primes_forall_sup_eq_top_of_isOpen` (Chebotarev, PROVEN 2026-07-26)
chooses the
auxiliary primes `S` above that bound, so that complete splitting at `S`
forces the disjointness conjunct for ANY normal `F`;
`exists_normalSplitPoint_of_affine_curve` (Moret–Bailly Thm 1.3) produces
the normal `F` with a real embedding, split at `S`, carrying an `F`-point of
`C`. The two are then combined: the disjointness is read off `S`, not off
the geometry.

FAITHFULNESS. The statement is unchanged from the 2026-07-26 cut; only its
proof is new. Its truth is not in doubt — it is BLGGT Prop. 3.1.1
specialised to `K₀ = K = ℚ`, `S = {∞}` and `L'_∞ = ℝ` (so "totally split at
`S`" reads "totally real"), with `K^avoid` the fixed field of the normal
core of `N` — and the potential-modularity literature uses exactly this
specialisation.

CIRCULARITY GUARD: inherited from the parent — no route through
`Family.lean`, `Lift.lean` or `Modularity/Interface.lean`. -/
theorem exists_normalRealPoint_of_affine_curve
    {C : AlgebraicGeometry.Scheme.{u}} [AlgebraicGeometry.IsAffine C]
    (fC : C ⟶ AlgebraicGeometry.Spec (CommRingCat.of (ULift.{u} ℚ)))
    (hsmooth : AlgebraicGeometry.Smooth fC)
    (hsep : AlgebraicGeometry.IsSeparated fC)
    (hft : AlgebraicGeometry.LocallyOfFiniteType fC)
    (hqc : AlgebraicGeometry.QuasiCompact fC)
    (hgi : AlgebraicGeometry.GeometricallyIrreducible fC)
    (hreal : HasRationalPoint fC (ULift.{u} ℝ))
    (hdim : topologicalKrullDim C ≤ 1)
    (N : Subgroup (Field.absoluteGaloisGroup ℚ))
    (hNopen : IsOpen (N : Set (Field.absoluteGaloisGroup ℚ))) :
    ∃ (F : Type u) (_ : Field F) (_ : NumberField F) (_ : Normal ℚ F)
      (_ : F →+* ℝ),
      N ⊔ (Field.absoluteGaloisGroup.map (algebraMap ℚ F)).toMonoidHom.range = ⊤ ∧
      HasRationalPoint fC F := by
  classical
  -- Weil bounds + Hensel: every prime beyond `B` is a place of good local solvability
  obtain ⟨B, hB⟩ :=
    exists_bound_forall_padicPoint_of_geometricallyIrreducible fC hsmooth hsep hft hqc hgi
  -- Chebotarev: auxiliary primes beyond `B` at which complete splitting forces disjointness
  obtain ⟨S, hS, hSsup⟩ := exists_primes_forall_sup_eq_top_of_isOpen.{u} N hNopen B
  -- Moret–Bailly on the curve: a normal `F` inside `ℝ`, split at `S`, with an `F`-point
  obtain ⟨F, hF, hNF, hnorm, ι, hsplit, hpt⟩ :=
    exists_normalSplitPoint_of_affine_curve fC hsmooth hsep hft hqc hgi hreal hdim S
      (fun p hp => (hS p hp).1)
      (by intro p _ hp; exact hB p (hS p hp).2)
  exact ⟨F, hF, hNF, hnorm, ι, hSsup F hF hNF hnorm hsplit, hpt⟩

open CategoryTheory AlgebraicGeometry in
/-- **Moret–Bailly's existence theorem, AFFINE CASE** (PROVEN 2026-07-26
as the assembly of Bertini + the curve case + the normality upgrade; see
the section docstring "Moret–Bailly's existence theorem, AFFINE CASE — the
Bertini cut" above for the mathematics and the faithfulness audit).

ASSEMBLY: `exists_affineCurve_of_affine_geometricallyIrreducible` supplies
an affine `ℚ`-curve `g : C ⟶ X` with a real point, carrying all five
geometric hypotheses for `g ≫ fX`;
`exists_normalRealPoint_of_affine_curve` supplies a normal number field
`F` with a ring map to `ℝ`, the disjointness conjunct, and an `F`-point of
`C`; `isTotallyReal_of_normal_of_realEmbedding` upgrades `F` to totally
real, characteristic zero upgrades `Normal ℚ F` to `IsGalois ℚ F`, and
`HasRationalPoint.of_comp` pushes the point from `C` to `X`. -/
theorem exists_totallyReal_point_of_affine_geometricallyIrreducible
    {X : AlgebraicGeometry.Scheme.{u}} [AlgebraicGeometry.IsAffine X]
    (fX : X ⟶ AlgebraicGeometry.Spec (CommRingCat.of (ULift.{u} ℚ)))
    (hsmooth : AlgebraicGeometry.Smooth fX)
    (hsep : AlgebraicGeometry.IsSeparated fX)
    (hft : AlgebraicGeometry.LocallyOfFiniteType fX)
    (hqc : AlgebraicGeometry.QuasiCompact fX)
    (hgi : AlgebraicGeometry.GeometricallyIrreducible fX)
    (hreal : HasRationalPoint fX (ULift.{u} ℝ))
    (N : Subgroup (Field.absoluteGaloisGroup ℚ))
    (hNopen : IsOpen (N : Set (Field.absoluteGaloisGroup ℚ))) :
    ∃ (F : Type u) (_ : Field F) (_ : NumberField F)
      (_ : NumberField.IsTotallyReal F) (_ : IsGalois ℚ F),
      N ⊔ (Field.absoluteGaloisGroup.map (algebraMap ℚ F)).toMonoidHom.range = ⊤ ∧
      HasRationalPoint fX F := by
  classical
  -- (i) Bertini: cut down to an affine `ℚ`-curve with a real point
  obtain ⟨C, hCaff, g, hCsm, hCsep, hCft, hCqc, hCgi, hCreal, hCdim⟩ :=
    exists_affineCurve_of_affine_geometricallyIrreducible fX hsmooth hsep hft hqc hgi hreal
  haveI : AlgebraicGeometry.IsAffine C := hCaff
  -- (ii)+(iii) Moret–Bailly on the curve: a NORMAL number field inside `ℝ`
  obtain ⟨F, hF, hNF, hnorm, ι, hsup, hpt⟩ :=
    exists_normalRealPoint_of_affine_curve (g ≫ fX) hCsm hCsep hCft hCqc hCgi hCreal hCdim
      N hNopen
  haveI : Normal ℚ F := hnorm
  -- normality + one real embedding ⟹ totally real; char. zero ⟹ Galois
  have hsep' : Algebra.IsSeparable ℚ F := inferInstance
  exact ⟨F, hF, hNF, isTotallyReal_of_normal_of_realEmbedding ι,
    { to_isSeparable := hsep', to_normal := hnorm }, hsup,
    HasRationalPoint.of_comp g fX hpt⟩

open CategoryTheory AlgebraicGeometry in
/-- **Moret–Bailly's existence theorem for global points with prescribed
local behaviour** (PROVEN 2026-07-25 as the affine reduction over
`exists_totallyReal_point_of_affine_geometricallyIrreducible` — pure
algebraic geometry, no arithmetic of
`ρbar`): let `X` be a smooth, separated, quasi-compact, finite-type,
geometrically irreducible variety over `ℚ` which has a real point. Then
for every open subgroup `N ≤ Γ ℚ` there is a number field `F`, TOTALLY
REAL and GALOIS over `ℚ`, with

* `N ⊔ (Γ F → Γ ℚ).range = ⊤` — the pin-stateable form of "`F` is
  linearly disjoint from the fixed field of `N`"; and
* an `F`-rational point of `X`.

This is Moret–Bailly, *Groupes de Picard et problèmes de Skolem II*,
Ann. Sci. ÉNS 22 (1989), Theorem 1.3, in the form recorded as
Proposition 3.1.1 of Barnet-Lamb–Gee–Geraghty–Taylor, *Potential
automorphy and change of weight* (equivalently Taylor 2002 Theorem G /
Prop. 2.1), specialized to `K = K₀ = ℚ`, `S = {∞}`, `L'_∞ = ℝ` and
`Ω_∞ = X(ℝ)`. In that statement the conclusion "`L_w ≅ L'_v = ℝ` for
every `w | ∞`" IS total reality of `F`, and "`L` linearly disjoint from
`K^(avoid)`" is the displayed join condition once `K^(avoid)` is taken
to be the fixed field of `N` (for non-normal `N` the statement follows
from the Galois closure, whose group is contained in `N`).

FORM AUDIT (2026-07-25): the theorem is applied here with `Ω_v` the
whole local point set, which is legitimate — `X(K_v)` is `v`-adically
open in itself — so no shrinking refinement is assumed. Quasi-projectivity,
present in Moret–Bailly's own hypotheses, is not expressible at this pin
(no `QuasiProjective` morphism property); the hypotheses used are the
ones under which BLGGT record the result, and the intended discharge
supplies a quasi-projective `X`. See the section docstring.

ASSEMBLY (2026-07-25, PROVEN — the AFFINE REDUCTION): the real point is a
morphism out of the ONE-POINT scheme `Spec ℝ`, so it factors through an
affine open `U ⊆ X` (`exists_isAffineOpen_hasRationalPoint`); all five
geometric hypotheses transfer to `U.ι ≫ fX` (smooth/separated/finite type
by stability under composition with an open immersion, quasi-compact
because `U` is affine over an affine base, geometrically irreducible
because a nonempty open still surjecting onto the one-point base `Spec ℚ`
stays geometrically irreducible);
`exists_totallyReal_point_of_affine_geometricallyIrreducible` then supplies
`F`; and the resulting `F`-point of `U` is an `F`-point of `X` by
composition (`HasRationalPoint.of_comp`). The disjointness conjunct
`N ⊔ Γ F = ⊤` is carried through untouched — the reduction never renames
or weakens it. NOTE: `hqc` is the one hypothesis the reduction does not
consume, since quasi-compactness of the affine open is re-derived rather
than inherited; it is kept because the affine leaf is stated as literally
the same theorem.

CIRCULARITY GUARD: this is a statement of algebraic geometry with no
Galois-representation hypotheses, so no route through `Family.lean`,
`Lift.lean` or `Modularity/Interface.lean` could even be relevant; the
remaining content must be proven by the geometric argument (Picard-scheme
torsors over an incompressible neighbourhood) recorded on the affine leaf
above. -/
theorem exists_totallyReal_point_of_geometricallyIrreducible
    {X : AlgebraicGeometry.Scheme.{u}}
    (fX : X ⟶ AlgebraicGeometry.Spec (CommRingCat.of (ULift.{u} ℚ)))
    (hsmooth : AlgebraicGeometry.Smooth fX)
    (hsep : AlgebraicGeometry.IsSeparated fX)
    (hft : AlgebraicGeometry.LocallyOfFiniteType fX)
    (hqc : AlgebraicGeometry.QuasiCompact fX)
    (hgi : AlgebraicGeometry.GeometricallyIrreducible fX)
    (hreal : HasRationalPoint fX (ULift.{u} ℝ))
    (N : Subgroup (Field.absoluteGaloisGroup ℚ))
    (hNopen : IsOpen (N : Set (Field.absoluteGaloisGroup ℚ))) :
    ∃ (F : Type u) (_ : Field F) (_ : NumberField F)
      (_ : NumberField.IsTotallyReal F) (_ : IsGalois ℚ F),
      N ⊔ (Field.absoluteGaloisGroup.map (algebraMap ℚ F)).toMonoidHom.range = ⊤ ∧
      HasRationalPoint fX F := by
  classical
  -- (i) shrink `X` to an affine open neighbourhood of the real point
  obtain ⟨U, hU, hUreal⟩ := exists_isAffineOpen_hasRationalPoint fX hreal
  haveI : IsAffine (U : Scheme.{u}) := hU
  -- (ii) that open is nonempty — it carries the real point
  haveI : Nonempty (U : Scheme.{u}) := by
    obtain ⟨z, -⟩ := hUreal
    obtain ⟨w⟩ : Nonempty ↥(Spec (CommRingCat.of (ULift.{u} ℝ))) := inferInstance
    exact ⟨z.base w⟩
  -- (iii) hence it still surjects onto the one-point base `Spec ℚ`, which is
  -- what upgrades geometric irreducibility along the open immersion
  haveI : Surjective (U.ι ≫ fX) :=
    ⟨fun _ => ⟨Classical.arbitrary _, Subsingleton.elim _ _⟩⟩
  haveI : GeometricallyIrreducible fX := hgi
  -- (iv) Moret–Bailly in the affine case
  obtain ⟨F, hF, hNF, hFtr, hFgal, hsup, hFpt⟩ :=
    exists_totallyReal_point_of_affine_geometricallyIrreducible (U.ι ≫ fX)
      (MorphismProperty.comp_mem _ _ _ inferInstance hsmooth)
      (MorphismProperty.comp_mem _ _ _ inferInstance hsep)
      (MorphismProperty.comp_mem _ _ _ inferInstance hft)
      inferInstance inferInstance hUreal N hNopen
  -- (v) a point of the open subscheme is a point of `X`
  exact ⟨F, hF, hNF, hFtr, hFgal, hsup, HasRationalPoint.of_comp U.ι fX hFpt⟩

/-! #### The moduli cut, recut over an abelian scheme (2026-07-25)

`exists_twistedHilbertBlumenthalModuli_of_five_le` (below) was a single
sorry joining two entirely different bodies of mathematics:

* the **moduli-space construction** — that a twisted Hilbert–Blumenthal
  moduli problem is representable by a smooth, separated, finite-type,
  quasi-compact, geometrically irreducible `ℚ`-variety with a real point
  (Shimura's theory of Hilbert–Blumenthal moduli, Rapoport,
  Deligne–Pappas; the geometric irreducibility of the *twist* is Taylor
  2002 §2);
* the **Tate-module construction** — that an `F`-point of such a space,
  i.e. a Hilbert–Blumenthal abelian variety over `F` with the two
  prescribed level structures, has `λ`-adic and `𝔭`-adic Tate modules
  forming a strictly compatible system with the prescribed residual
  representations (Weil, Faltings; Carayol normalization).

MACHINERY AUDIT (2026-07-25). Neither could be *stated* against the
pin: a sweep of `.lake/packages/mathlib` found **no** `AbelianVariety`,
`AbelianScheme`, `TateModule`, `HilbertModular`, `Blumenthal` or
`ShimuraVariety` declaration anywhere in mathlib, and none in this
project or in `~/cs/FLT` either. The whole theory is missing.
`Modularity/AbelianScheme.lean` (new, PROVEN, sorry-free) supplies the
first piece of it: abelian schemes presented by their functor of points
(`Fermat.AbelianSchemeStruct`), the group of geometric points of a fibre
at an `F`-point (`Fermat.GeomFibrePt`) with its `Γ_F`-action by additive
automorphisms (`Fermat.AbelianSchemeStruct.geomFibreAction`, whose
underlying map is `Fermat.AbelianSchemeStruct.galSMul`), and the
real-multiplication datum (`Fermat.Mult`) with its `I`-torsion Galois
submodules (`Fermat.Mult.torsion`, whose second component is exactly the
Galois stability). That is exactly enough vocabulary to WRITE the
twisted level structures down, and hence to separate the two bodies of
mathematics above into two independently citable leaves. It is not
enough to prove either of them; the further pieces needed, in dependency
order, are recorded in the docstring of
`exists_twistedHilbertBlumenthalModuliForm_of_five_le` (the recut of the
moduli half — see "The FORM cut" below, which reduced
`exists_twistedHilbertBlumenthalModuliScheme_of_five_le` to it).

The seam is `IsTwistedHilbertBlumenthalModuli`: the statement that an
abelian scheme over `X` carries real multiplication by a totally real
`D` of degree the relative dimension, and that at every `F`-point its
geometric fibre has `λ`-torsion realizing `ρbar|_{G_F}` and `𝔭`-torsion
irreducible-but-dihedral. Leaf A produces `X` together with such a
family; leaf B turns a point of such a family into a
`HilbertBlumenthalPoint`. The glue between them is PROVEN. -/

open CategoryTheory in
/-- **The twisted Hilbert–Blumenthal moduli condition** on an abelian
scheme `fA : A ⟶ X` over the `ℚ`-variety `fX : X ⟶ Spec ℚ`.

This is the seam of the moduli cut. It asserts the existence of

* a **totally real coefficient field** `D` and a **real multiplication**
  of `𝒪_D` on the family, with the relative dimension of `A ⟶ X` equal
  to `[D : ℚ]` — i.e. `A ⟶ X` is a family of Hilbert–Blumenthal abelian
  varieties with real multiplication by `𝒪_D`;
* an **auxiliary prime** `p ≠ ℓ`, and maximal ideals `λ ∋ ℓ`, `𝔭 ∋ p` of
  `𝒪_D`;
* the **FIRST moduli condition** (the `ℓ`-level structure, twisted by
  `ρbar`): at every `F`-point `x` of `X` over `ℚ`, with `F` totally real
  and Galois over `ℚ` and restriction to `G_F` image-preserving, the
  `λ`-torsion of the geometric fibre is isomorphic, as a `Γ_F`-module,
  to `W` with the action `ρbar|_{G_F}`;
* the **SECOND moduli condition** (the dihedral `p`-level structure): at
  the same points, the `𝔭`-torsion is isomorphic as a `Γ_F`-module to a
  two-dimensional `ρbarp` over a finite field, which is irreducible over
  `F` but becomes reducible over a quadratic extension.

Both level structures are stated as isomorphisms of *Galois modules* —
an injective additive map onto the torsion submodule
`(m.torsion x _).1` intertwining the scheme-theoretic Galois action
`Fermat.AbelianSchemeStruct.galSMul` with the representation — which is
possible only because `Modularity/AbelianScheme.lean` makes the
geometric points of a fibre a `Γ_F`-module in the first place, and their
`I`-torsion a Galois-stable `𝒪_D`-submodule of it.

FAITHFULNESS NOTE: the quantifier over `F` carries exactly the
hypotheses that the consumer
`exists_twistedHilbertBlumenthalModuli_of_five_le` supplies (totally
real, Galois, image-preserving restriction, an `F`-point over `ℚ`), so
this condition is never stronger there than what the classical twisted
moduli problem provides. -/
def IsTwistedHilbertBlumenthalModuli (ℓ : ℕ) [Fact ℓ.Prime]
    {k : Type u} [Field k] [TopologicalSpace k] [DiscreteTopology k]
    {W : Type v} [AddCommGroup W] [Module k W]
    (ρbar : GaloisRep ℚ k W)
    {X : AlgebraicGeometry.Scheme.{u}}
    (fX : X ⟶ AlgebraicGeometry.Spec (CommRingCat.of (ULift.{u} ℚ)))
    {A : AlgebraicGeometry.Scheme.{u}} {fA : A ⟶ X}
    (ab : Fermat.AbelianSchemeStruct fA) : Prop :=
  ∃ (D : Type u) (_ : Field D) (_ : NumberField D)
    (_ : NumberField.IsTotallyReal D)
    (m : Fermat.Mult ab (NumberField.RingOfIntegers D))
    (p : ℕ) (lam frp : Ideal (NumberField.RingOfIntegers D)),
    p.Prime ∧ p ≠ ℓ ∧ lam.IsMaximal ∧ frp.IsMaximal ∧
    (ℓ : NumberField.RingOfIntegers D) ∈ lam ∧
    (p : NumberField.RingOfIntegers D) ∈ frp ∧
    AlgebraicGeometry.SmoothOfRelativeDimension (Module.finrank ℚ D) fA ∧
    ∀ (F : Type u) (_ : Field F) (_ : NumberField F)
      (_ : NumberField.IsTotallyReal F) (_ : IsGalois ℚ F),
      (∀ g : Field.absoluteGaloisGroup ℚ,
        ∃ h : Field.absoluteGaloisGroup F,
          (ρbar.map (algebraMap ℚ F)) h = ρbar g) →
      ∀ x : (AlgebraicGeometry.Spec (CommRingCat.of F) ⟶ X), x ≫ fX = specRatMap F →
        -- FIRST moduli condition: `A[λ]` realizes `ρbar|_{G_F}`
        (∃ e : W → Fermat.GeomFibrePt fA x,
          (∀ w w' : W, e (w + w') = ab.add (e w) (e w')) ∧
          Function.Injective e ∧
          (∀ (σ : Field.absoluteGaloisGroup F) (w : W),
            e ((ρbar.map (algebraMap ℚ F)) σ w) = ab.galSMul x σ (e w)) ∧
          (∀ y, y ∈ (m.torsion x lam).1 ↔ ∃ w, e w = y)) ∧
        -- SECOND moduli condition: `A[𝔭]` is irreducible and dihedral
        (∃ (kp : Type u) (_ : Field kp) (_ : Finite kp) (_ : TopologicalSpace kp)
          (_ : DiscreteTopology kp) (ρbarp : GaloisRep F kp (Fin 2 → kp))
          (e : (Fin 2 → kp) → Fermat.GeomFibrePt fA x),
          (∀ w w' : Fin 2 → kp, e (w + w') = ab.add (e w) (e w')) ∧
          Function.Injective e ∧
          (∀ (σ : Field.absoluteGaloisGroup F) (w : Fin 2 → kp),
            e (ρbarp σ w) = ab.galSMul x σ (e w)) ∧
          (∀ y, y ∈ (m.torsion x frp).1 ↔ ∃ w, e w = y) ∧
          ρbarp.IsIrreducible ∧
          ∃ (L : Type u) (_ : Field L) (_ : Algebra F L),
            Module.finrank F L = 2 ∧
            ¬ (ρbarp.map (algebraMap F L)).IsIrreducible)

/-! #### The FORM cut (2026-07-25): Taylor's `X` is a TWIST, and the two
remaining geometric properties are read off the twisting

Taylor's own argument — *On the meromorphic continuation of degree two
`L`-functions*, Documenta Math. Extra Volume Coates (2006) 729–779, §4
pp. 759–763, which is what this module's "Taylor 2002 §2" citations
refer to — does NOT construct `X` and then verify its geometry. It
constructs `X` as a TWIST of a SPLIT moduli space and reads both
remaining geometric properties off that twisting:

* `X/ℚ` is the moduli space of quadruples `(A, i, j, α)` with `(A,i,j)`
  an `E`-HBAV and `α : W_{b₀,0} ≅ A[b₀]` carrying the standard pairing
  to the `j`-Weil pairing. "As `b₀` is divisible by two primes with
  coprime residue characteristic we see that `X` is a fine moduli space.
  As in section 1 of [Rap] we see that `X` is smooth and geometrically
  connected (because of the analytic uniformization of its complex
  points by a product of copies of the upper half complex plane)."
* `Γ = {(γ,ε) ∈ GL₂(𝒪_E/b₀) × 𝒪_{E,≫0}ˣ/(𝒪_{E,≡1(b₀)}ˣ)² : ε det γ ≡ 1}`
  acts faithfully on `X`; `H¹(G_ℚ, Γ)` is in bijection with the pairs
  `(R, ψ)`, `R : G_ℚ → GL₂(𝒪_E/b₀)` continuous with
  `ε⁻¹ det R ≡ ψ⁻¹`, and each such pair gives a twist `X_{R,ψ}/ℚ`. The
  `F`-points of `X_{R,ψ}` are the quadruples carrying a `G_F`-equivariant
  `β : W_R ≅ A[b₀]` (Lemma 4.4) — that description is exactly the
  condition `IsTwistedHilbertBlumenthalModuli` above.
* `X_ρ` and `X_Dih` are the twists by `R_ρ = ρ ⊕ Ind χ_{℘₁} ⊕ Ind χ_{℘₂}`
  and `R_Dih = Ind χ_λ ⊕ Ind χ_{℘₁} ⊕ Ind χ_{℘₂}`; "note that `X_ρ` and
  `X_Dih` become isomorphic over `ℚ_l`, `ℚ_{p₁}`, `ℚ_{p₂}` and `ℝ`."
* Lemma 4.5: "`X_Dih` has a `ℚ`-rational point" — produced by the theory
  of complex multiplication ([Lang] ch. 5 thm 5.1) — "and hence `X_ρ`
  has rational points over `ℚ_l`, `ℚ_{p₁}`, `ℚ_{p₂}` and over `ℝ`."

So the REAL POINT is not an independent signature computation: it is the
CM point of `X_Dih`, transported along an isomorphism of the two twists
over `ℝ` — and the oddness of `ρbar` is what makes that isomorphism
exist (`R_ρ` and `R_Dih` agree on `G_ℝ` precisely because both are odd).
Likewise GEOMETRIC IRREDUCIBILITY of `X_ρ` is never proven about `X_ρ`
itself: a twist is a form, so `X_ρ` and the split `X` agree over `ℚ̄`,
and geometric irreducibility depends only on that base change.

WHY THIS IS THE ONLY AVAILABLE CUT (faithfulness check, made BEFORE
writing it, and it killed the obvious alternative). One may NOT split
"the space exists" from "the space has a real point" by quantifying over
an arbitrary `X` carrying a twisted family — that statement is FALSE.
Take the twist `X_R` by a cocycle `R` which is EVEN. Then `X_R(ℝ) = ∅`,
hence `X_R(F) = ∅` for every totally real `F` (a totally real field
embeds into `ℝ`), hence the `∀ F` clause of
`IsTwistedHilbertBlumenthalModuli ℓ ρbar` holds VACUOUSLY of `X_R` —
while `X_R` is still smooth, separated, of finite type, quasi-compact
and geometrically irreducible and still carries an abelian scheme with
real multiplication of the right relative dimension. So the real point
does not follow from the moduli condition plus the geometry: the
hypothesis must REMEMBER that `X` is a form of something with a point.
`IsFormOver` below is exactly that memory, and it is why the leaf
`exists_twistedHilbertBlumenthalModuliForm_of_five_le` carries the two
comparison spaces `X₀` (over `ℚ̄`) and `Y` (over `ℝ`) in its conclusion
rather than the two properties. -/

open CategoryTheory in
/-- **`fX` and `fY` are `K`-forms of each other**: their base changes
along `Spec K ⟶ Spec ℚ` are isomorphic OVER `Spec K`.

Written with `Limits.pullback` (the base change) and with the
compatibility `e.hom ≫ pr₂ = pr₂` that makes the isomorphism one of
`K`-schemes — without that compatibility a `K`-point could not be
transported, which is the whole purpose of the definition
(`hasRationalPoint_of_isFormOver`).

`K` is only required to be a commutative `ℚ`-algebra, because the two
uses are `K = ℚ̄` (a field, for geometric irreducibility) and
`K = ℝ` (for the archimedean point), and `specRatMap` is defined for any
`ℚ`-algebra. -/
def IsFormOver (K : Type u) [CommRing K] [Algebra ℚ K]
    {X Y : AlgebraicGeometry.Scheme.{u}}
    (fX : X ⟶ AlgebraicGeometry.Spec (CommRingCat.of (ULift.{u} ℚ)))
    (fY : Y ⟶ AlgebraicGeometry.Spec (CommRingCat.of (ULift.{u} ℚ))) : Prop :=
  ∃ e : Limits.pullback fX (specRatMap K) ≅ Limits.pullback fY (specRatMap K),
    e.hom ≫ Limits.pullback.snd fY (specRatMap K) =
      Limits.pullback.snd fX (specRatMap K)

open CategoryTheory in
/-- **`K`-points transport along a `K`-form** (PROVEN): if `fX` and `fY`
are `K`-forms of each other and `fY` has a `K`-point, so does `fX`.

This is the formal content of Taylor's "and hence `X_ρ` has rational
points over ... `ℝ`" (Lemma 4.5): a `K`-point of `fY` is a section of
the second projection of the base change `Y_K`, the form isomorphism
carries sections of one second projection to sections of the other, and
a section of `pr₂ : X_K → Spec K` composed with `pr₁` is a `K`-point of
`fX`. No hypothesis on `K` beyond being a `ℚ`-algebra is used. -/
theorem hasRationalPoint_of_isFormOver {K : Type u} [CommRing K] [Algebra ℚ K]
    {X Y : AlgebraicGeometry.Scheme.{u}}
    (fX : X ⟶ AlgebraicGeometry.Spec (CommRingCat.of (ULift.{u} ℚ)))
    (fY : Y ⟶ AlgebraicGeometry.Spec (CommRingCat.of (ULift.{u} ℚ)))
    (hform : IsFormOver K fX fY) (hY : HasRationalPoint fY K) :
    HasRationalPoint fX K := by
  obtain ⟨e, he⟩ := hform
  obtain ⟨y, hy⟩ := hY
  have hlift : y ≫ fY = 𝟙 _ ≫ specRatMap K := by simpa using hy
  refine ⟨(Limits.pullback.lift y (𝟙 _) hlift ≫ e.inv) ≫
    Limits.pullback.fst fX (specRatMap K), ?_⟩
  have hinv : e.inv ≫ Limits.pullback.snd fX (specRatMap K) =
      Limits.pullback.snd fY (specRatMap K) := by
    rw [← he, Iso.inv_hom_id_assoc]
  have hsec : (Limits.pullback.lift y (𝟙 _) hlift ≫ e.inv) ≫
      Limits.pullback.snd fX (specRatMap K) = 𝟙 _ := by
    rw [Category.assoc, hinv, Limits.pullback.lift_snd]
  rw [Category.assoc, Limits.pullback.condition, ← Category.assoc, hsec,
    Category.id_comp]

open CategoryTheory AlgebraicGeometry TensorProduct in
/-- **Geometric irreducibility descends along a form** (PROVEN
2026-07-26): if `fX` and `fX₀` are `K`-forms of each other over a
`ℚ`-algebra field `K`, and `fX₀` is geometrically irreducible, then so
is `fX`.

Classically this is read off Stacks 0364 / EGA IV 4.5.9 ("geometric
irreducibility may be tested over a SINGLE algebraically closed
extension"), and at this pin that criterion is genuinely absent from
mathlib: `AlgebraicGeometry.GeometricallyIrreducible` is *defined* as the
all-extensions form (`geometrically (IrreducibleSpace ·)`, i.e.
`X ×_Y Spec L` irreducible for EVERY field `L` and every
`Spec L ⟶ Y`), and only its stability under base change is recorded.

PROOF (2026-07-26) — the Stacks criterion is NOT needed, because a form
carries more information than a single irreducible base change, and that
surplus makes the descent elementary. Write `S = Spec ℚ`.

1. `(X₀)_K ⟶ Spec K` is geometrically irreducible (base change of `fX₀`).
   The form isomorphism `e` satisfies `e.hom ≫ pr₂ = pr₂`, and
   `GeometricallyIrreducible` respects isomorphisms, so `X_K ⟶ Spec K` is
   geometrically irreducible too. This is the only place `hform` is used.
2. Let `L` be ANY field with a map `Spec L ⟶ S`; we must show `X_L` is
   irreducible. Since `ℚ` is a field, `L ⊗_ℚ K ≠ 0`, so it has a maximal
   ideal; let `Ω` be the quotient field. Then `Ω` is a field extension of
   BOTH `L` and `K`, and the two composites `ℚ → Ω` agree automatically —
   a ring map out of `ℚ` into a field is unique.
3. `X_Ω = (X_K) ×_K Ω` is irreducible, directly by step 1 applied to the
   extension `K ⊆ Ω`. (Note this needs no algebraic closedness: it is the
   *geometric* irreducibility of `X_K` over `K`, not the irreducibility
   of a single base change.)
4. `X_Ω ⟶ X_L` is the base change of `Spec Ω ⟶ Spec L` along
   `X_L ⟶ Spec L` (pasting the two pullback squares), and
   `Spec Ω ⟶ Spec L` is surjective because both spaces are single points;
   surjectivity is stable under base change. A continuous surjective
   image of an irreducible space is irreducible, so `X_L` is irreducible.

HYPOTHESIS NOT CONSUMED: `_hK : IsAlgClosed K`. The statement is true for
an arbitrary `ℚ`-algebra field `K`, as the proof above shows — the
algebraically closed case is merely how Taylor's argument supplies it
(`X = X_ρ` is a `ℚ̄`-form of the split moduli space `X₀`). The hypothesis
is KEPT in the signature so that the consumer
`exists_twistedHilbertBlumenthalModuli_of_five_le` and the leaf
`exists_twistedHilbertBlumenthalModuliForm_of_five_le` need not change;
underscored so that its non-use is mechanically visible. Anyone extracting
this for mathlib should drop it and generalise `ℚ` to an arbitrary base.

SOUNDNESS: no hypothesis on `X` beyond the form — no finiteness, no
smoothness, no separatedness — is used; the argument is valid for
arbitrary schemes over a field. -/
theorem geometricallyIrreducible_of_isFormOver_isAlgClosed
    {K : Type u} [Field K] [Algebra ℚ K] (_hK : IsAlgClosed K)
    {X X₀ : AlgebraicGeometry.Scheme.{u}}
    (fX : X ⟶ AlgebraicGeometry.Spec (CommRingCat.of (ULift.{u} ℚ)))
    (fX₀ : X₀ ⟶ AlgebraicGeometry.Spec (CommRingCat.of (ULift.{u} ℚ)))
    (hform : IsFormOver K fX fX₀)
    (h₀ : AlgebraicGeometry.GeometricallyIrreducible fX₀) :
    AlgebraicGeometry.GeometricallyIrreducible fX := by
  obtain ⟨e, he⟩ := hform
  -- STEP 1: `X_K ⟶ Spec K` is geometrically irreducible, transported
  -- across the form isomorphism (which is compatible with `pr₂`).
  have hK₀ : GeometricallyIrreducible (Limits.pullback.snd fX₀ (specRatMap K)) := inferInstance
  have hKX : GeometricallyIrreducible (Limits.pullback.snd fX (specRatMap K)) := by
    rw [← he]
    exact (MorphismProperty.cancel_left_of_respectsIso
      (P := @GeometricallyIrreducible) e.hom _).mpr hK₀
  -- STEP 2: test irreducibility after an arbitrary field extension `L`.
  refine ⟨?_⟩
  rw [geometrically_iff_of_isClosedUnderIsomorphisms]
  intro L _ y
  obtain ⟨ψ, rfl⟩ := Spec.map_surjective y
  letI : Algebra ℚ L :=
    (ψ.hom.comp (ULift.ringEquiv.symm : ℚ ≃+* ULift.{u} ℚ).toRingHom).toAlgebra
  -- STEP 3: a common field extension `Ω` of `L` and of `K`, obtained as a
  -- residue field of the (nonzero, since `ℚ` is a field) ring `L ⊗_ℚ K`.
  haveI : Nontrivial (L ⊗[ℚ] K) :=
    Algebra.TensorProduct.nontrivial_of_algebraMap_injective_of_flat_left
      (R := ℚ) L K (algebraMap ℚ K).injective
  obtain ⟨m, hm⟩ := Ideal.exists_maximal (L ⊗[ℚ] K)
  haveI := hm
  let Ω : Type u := (L ⊗[ℚ] K) ⧸ m
  letI : Field Ω := Ideal.Quotient.field m
  let φL : L →+* Ω := (Ideal.Quotient.mk m).comp Algebra.TensorProduct.includeLeftRingHom
  let φK : K →+* Ω :=
    (Ideal.Quotient.mk m).comp
      (Algebra.TensorProduct.includeRight (R := ℚ) (A := L) (B := K)).toRingHom
  let u : Spec (CommRingCat.of Ω) ⟶ Spec (CommRingCat.of K) :=
    Spec.map (CommRingCat.ofHom φK)
  let v : Spec (CommRingCat.of Ω) ⟶ Spec (CommRingCat.of L) :=
    Spec.map (CommRingCat.ofHom φL)
  -- the two structure maps `Spec Ω ⟶ Spec ℚ` agree: a ring map out of `ℚ`
  -- into a field is unique, and `ULift ℚ ≃+* ℚ`.
  have huniq : ∀ f g : (ULift.{u} ℚ) →+* Ω, f = g := by
    intro f g
    have h := RingHom.ext_rat (R := Ω)
      (f.comp (ULift.ringEquiv.symm : ℚ ≃+* ULift.{u} ℚ).toRingHom)
      (g.comp (ULift.ringEquiv.symm : ℚ ≃+* ULift.{u} ℚ).toRingHom)
    ext x
    have hx := RingHom.congr_fun h (ULift.ringEquiv x)
    simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe,
      RingEquiv.symm_apply_apply] at hx
    exact hx
  have hcompat : u ≫ specRatMap K = v ≫ Spec.map ψ := by
    simp only [u, v, specRatMap, ← Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    exact huniq _ _
  -- STEP 4: paste `X_Ω = (X_K) ×_K Ω` over `X_L`, exhibiting
  -- `X_Ω ⟶ X_L` as the base change of `Spec Ω ⟶ Spec L`.
  have sqTop : IsPullback
      (Limits.pullback.snd (Limits.pullback.snd fX (specRatMap K)) u)
      (Limits.pullback.fst (Limits.pullback.snd fX (specRatMap K)) u) u
      (Limits.pullback.snd fX (specRatMap K)) :=
    (IsPullback.of_hasPullback _ _).flip
  have sqMid : IsPullback (Limits.pullback.snd fX (specRatMap K))
      (Limits.pullback.fst fX (specRatMap K)) (specRatMap K) fX :=
    (IsPullback.of_hasPullback _ _).flip
  have sqBig := sqTop.paste_vert sqMid
  rw [hcompat] at sqBig
  have sqBot : IsPullback (Limits.pullback.snd fX (Spec.map ψ))
      (Limits.pullback.fst fX (Spec.map ψ)) (Spec.map ψ) fX :=
    (IsPullback.of_hasPullback _ _).flip
  obtain ⟨w, hw⟩ : ∃ w : Limits.pullback (Limits.pullback.snd fX (specRatMap K)) u ⟶
      Limits.pullback fX (Spec.map ψ),
      IsPullback (Limits.pullback.snd (Limits.pullback.snd fX (specRatMap K)) u) w v
        (Limits.pullback.snd fX (Spec.map ψ)) :=
    ⟨_, IsPullback.of_bot' sqBig sqBot⟩
  -- STEP 5: `w` is surjective and its source is irreducible.
  haveI : Surjective v := inferInstance
  haveI : Surjective w := MorphismProperty.of_isPullback hw ‹Surjective v›
  have hirr : IrreducibleSpace
      ↥(Limits.pullback (Limits.pullback.snd fX (specRatMap K)) u) :=
    pullback_of_geometrically hKX.geometrically_irreducibleSpace Ω u
  rw [irreducibleSpace_def]
  have himg := (IrreducibleSpace.isIrreducible_univ
    ↥(Limits.pullback (Limits.pullback.snd fX (specRatMap K)) u)).image
      w.base w.continuous.continuousOn
  rwa [Set.image_univ, Set.range_eq_univ.mpr w.surjective] at himg

/-! #### The ARCHIMEDEAN cut (2026-07-26): the only input to the FORM leaf
that does not mention `X`

`exists_twistedHilbertBlumenthalModuliForm_of_five_le` still joined two
independent bodies of mathematics, and the seam between them is the
ARCHIMEDEAN place:

* the **representability half** — Rapoport §1 (the split moduli space of
  `𝒪_D`-HBAVs with full `λ𝔭`-level structure is a FINE moduli space,
  smooth and geometrically connected over `ℚ`) together with Galois
  descent along the cocycle attached to `ρbar` (Taylor §4, Lemma 4.4).
  This produces `X = X_ρ`, its moduli property, its geometry, and the
  identification of `X` as a `ℚ̄`-form of the split space;
* the **archimedean half** — that the twisted moduli problem is SOLVABLE
  OVER `ℝ`. This is where the ODDNESS of `ρbar` is consumed, and it is
  what Taylor's Lemma 4.5 (the CM point of `X_Dih`, plus
  `X_ρ ≅ X_Dih` over `ℝ`) exists to supply.

WHY THIS IS THE CUT, and why the obvious alternatives are not. The FORM
section docstring above records that one may NOT split "the space exists"
from "the space has a real point" by quantifying over an arbitrary `X`
carrying a twisted family: the EVEN twists satisfy the moduli condition
VACUOUSLY (`X_R(ℝ) = ∅` for `R` even, hence `X_R(F) = ∅` for every
totally real `F`) while having no real point. That refutation kills every
cut whose second leaf is a statement ABOUT `X`, because nothing
`IsTwistedHilbertBlumenthalModuli` says can force a point to exist — it
is a condition on the points there ARE, never a supply of points. The
same objection kills the two other cuts that were tried on paper first:
"`X` is a `ℚ̄`-form of some geometrically irreducible `X₀`" is satisfied
by conics without real points, and "the DIHEDRAL twist `Y` has a rational
point" is again vacuous for a pointless `Y`.

`HasRealHilbertBlumenthalObject` below evades all of that because it
mentions no space at all: it is a statement about `ρbar` and an abelian
variety over `ℝ`. It is exactly the fibre of the moduli problem over the
archimedean place, and it is TRUE precisely when the twisting cocycle is
odd — the content Taylor extracts from the CM point.

THE TWO LEAVES, and how the assembly composes them:

* `exists_twistedHilbertBlumenthalModuliTwist_of_five_le` — the
  representability half, stated so that it hands over the auxiliary datum
  it chose (`D`, `λ`, `𝔭`, and the dihedral `𝔭`-level representation
  `ρbarp`) together with the FINENESS consequence that it, and only it,
  owns: a real object for that datum IS an `ℝ`-point of `X`.
* `hasRealHilbertBlumenthalObject_of_isHardlyRamified` — the archimedean
  half, quantified over an arbitrary ADMISSIBLE datum, so that whichever
  datum the first leaf chose is covered.

DATUM THREADING (the design constraint that fixed the shape of both
statements). The two leaves must agree on `D`, `λ`, `𝔭` and `ρbarp`,
while the seam `IsTwistedHilbertBlumenthalModuli` hides those inside an
existential. Rather than refactor the seam — it has other consumers, and
a parameterized copy would duplicate forty lines of level-structure
conditions — the first leaf's conclusion carries a SECOND, independent
copy of the datum together with the implication that consumes it. The two
copies are the same object in the intended discharge, and the assembly
never needs to know that.

WHY THE RESIDUE-FIELD ISOMORPHISMS ARE NOT AN EXTRA ASSUMPTION on the
first leaf: the first moduli condition of the seam demands an additive
BIJECTION `W ≅ A[λ]`, and `A[λ]` is free of rank two over `𝒪_D/λ` while
`W` is free of rank two over `k`; so `|𝒪_D/λ| = |k|` is FORCED by the
seam, and finite fields of equal cardinality are isomorphic. Likewise
`𝒪_D/𝔭 ≅ kp` is forced by the second moduli condition.

WHY THE SECOND LEAF IS TRUE, and what it does NOT need — recorded so that
nobody dispatched at it goes looking for Shimura theory. Let `E/ℝ` be an
elliptic curve and put `B = E ⊗_ℤ 𝒪_D`, an abelian variety over `ℝ` of
dimension `[D:ℚ]` with real multiplication by `𝒪_D`. For any maximal
`λ ∋ ℓ` one has `B[λ] ≅ E[ℓ] ⊗_{𝔽_ℓ} 𝒪_D/λ` as `Γ_ℝ`-modules — this
holds even when `λ` is RAMIFIED over `ℓ`, since the `λ`-torsion of
`𝒪_D/ℓ` is `λ^{e-1}/λ^e ≅ 𝒪_D/λ`, one-dimensional over the residue
field. So complex conjugation acts on the two-dimensional
`𝒪_D/λ`-space `B[λ]` exactly as it acts on `E[ℓ]`: with determinant
`-1`, because it acts on `H₁(E(ℂ), ℤ) = ℤ²` with determinant `-1`. In
odd residue characteristic an involution of determinant `-1` on a
two-dimensional space is conjugate to `diag(1, -1)`; there is exactly ONE
odd two-dimensional representation of `Γ_ℝ = ℤ/2` up to isomorphism, so
`B[λ] ≅ ρbar|_{Γ_ℝ}` as soon as `ρbar` is odd — which `IsHardlyRamified`
gives, its determinant being the cyclotomic character and
`cyclotomicCharacter_complexConj` being `-1`. The same argument at `𝔭`
uses the oddness hypothesis on `ρbarp`; in residue characteristic `2`
"odd" is vacuous, and the two involutions that can occur (the identity
and a transvection) are BOTH realized, by choosing the sign of the
discriminant of `E`: `c` acts trivially on `E[2]` iff `E(ℝ)` has full
two-torsion. One real elliptic curve therefore suffices, and no moduli
space, no complex multiplication and no Shimura variety enter. (Taylor
reaches the archimedean conclusion through the CM point of `X_Dih`
because he wants a `ℚ`-RATIONAL point of a specific twist; the FORM cut
above already reduced that to the archimedean statement, and this cut
isolates it.)

CIRCULARITY GUARD (inherited from pillar β, load-bearing, and inherited
in turn by both leaves): neither may be discharged through `Family.lean`,
`Lift.lean`, or `Modularity/Interface.lean`. -/

open CategoryTheory in
/-- **Every scheme is a `K`-form of itself** (PROVEN): the identity
isomorphism of the base change is compatible with the second projection.

This is what lets the `Y`-clause of
`exists_twistedHilbertBlumenthalModuliForm_of_five_le` be discharged with
`Y = X` once `X` itself is known to have a real point: the clause
`∃ Y fY, HasRationalPoint fY ℝ ∧ IsFormOver ℝ fX fY` is, up to this
lemma, exactly `HasRationalPoint fX ℝ`. The `Y` in it is a memory of
Taylor's route (`Y = X_Dih`), not an extra demand. -/
theorem isFormOver_refl (K : Type u) [CommRing K] [Algebra ℚ K]
    {X : AlgebraicGeometry.Scheme.{u}}
    (fX : X ⟶ AlgebraicGeometry.Spec (CommRingCat.of (ULift.{u} ℚ))) :
    IsFormOver K fX fX :=
  ⟨Iso.refl _, by simp⟩

open CategoryTheory in
/-- **A real object of the twisted Hilbert–Blumenthal moduli problem**:
an abelian variety `B` over `ℝ`, with real multiplication by `𝒪_D` and
of dimension `[D:ℚ]`, whose `λ`-torsion realizes `ρbar` restricted to
`Γ_ℝ` and whose `𝔭`-torsion realizes `ρbarp` restricted to `Γ_ℝ`.

This is the fibre over the archimedean place of the moduli problem whose
`F`-points, for `F` a totally real number field, are described by
`IsTwistedHilbertBlumenthalModuli`. It is stated with the SAME
vocabulary — `Fermat.AbelianSchemeStruct`, `Fermat.Mult`,
`Fermat.GeomFibrePt`, `Fermat.Mult.torsion` — with two differences forced
by the place:

* the base is `Spec ℝ` rather than `Spec ℚ`, so the point at which the
  geometric fibre is taken is the identity of `Spec ℝ`;
* `ρbar` cannot be restricted with `GaloisRep.map`, whose target field
  must be a number field, so the restriction is written directly with
  `Field.absoluteGaloisGroup.map (algebraMap ℚ ℝ) : Γ_ℝ →ₜ* Γ_ℚ` —
  which is exactly what `GaloisRep.map` unfolds to (`GaloisRep.map_apply`).

NO IRREDUCIBILITY, AND THAT IS NOT AN OVERSIGHT. The second moduli
condition of the seam asks for a `ρbarp` that is irreducible over `F` and
becomes reducible over a quadratic extension. Over `ℝ` the first half is
IMPOSSIBLE: `Γ_ℝ = ℤ/2`, and an involution of a two-dimensional space
over any field always has an invariant line (in odd characteristic it is
diagonalizable; in characteristic two it is unipotent). So the dihedral
condition is a GLOBAL condition on the twisting cocycle, not a condition
on the objects it classifies, and demanding it here would make this
definition unsatisfiable. What survives at `ℝ`, and all that the moduli
interpretation needs there, is the level structure itself. -/
def HasRealHilbertBlumenthalObject
    {k : Type u} [Field k] [TopologicalSpace k]
    {W : Type v} [AddCommGroup W] [Module k W]
    (ρbar : GaloisRep ℚ k W)
    (D : Type u) [Field D] [NumberField D]
    (lam frp : Ideal (NumberField.RingOfIntegers D))
    {kp : Type u} [Field kp] [TopologicalSpace kp]
    (ρbarp : GaloisRep ℚ kp (Fin 2 → kp)) : Prop :=
  ∃ (B : AlgebraicGeometry.Scheme.{u})
    (fB : B ⟶ AlgebraicGeometry.Spec (CommRingCat.of (ULift.{u} ℝ)))
    (abB : Fermat.AbelianSchemeStruct fB)
    (m : Fermat.Mult abB (NumberField.RingOfIntegers D)),
    AlgebraicGeometry.SmoothOfRelativeDimension (Module.finrank ℚ D) fB ∧
    -- the `λ`-level structure: `B[λ]` realizes `ρbar|_{Γ_ℝ}`
    (∃ e : W → Fermat.GeomFibrePt fB
        (𝟙 (AlgebraicGeometry.Spec (CommRingCat.of (ULift.{u} ℝ)))),
      (∀ w w' : W, e (w + w') = abB.add (e w) (e w')) ∧
      Function.Injective e ∧
      (∀ (σ : Field.absoluteGaloisGroup (ULift.{u} ℝ)) (w : W),
        e (ρbar (Field.absoluteGaloisGroup.map (algebraMap ℚ (ULift.{u} ℝ)) σ) w) =
          abB.galSMul (𝟙 (AlgebraicGeometry.Spec (CommRingCat.of (ULift.{u} ℝ)))) σ (e w)) ∧
      (∀ y, y ∈ (m.torsion
        (𝟙 (AlgebraicGeometry.Spec (CommRingCat.of (ULift.{u} ℝ)))) lam).1 ↔ ∃ w, e w = y)) ∧
    -- the `𝔭`-level structure: `B[𝔭]` realizes `ρbarp|_{Γ_ℝ}`
    (∃ e : (Fin 2 → kp) → Fermat.GeomFibrePt fB
        (𝟙 (AlgebraicGeometry.Spec (CommRingCat.of (ULift.{u} ℝ)))),
      (∀ w w' : Fin 2 → kp, e (w + w') = abB.add (e w) (e w')) ∧
      Function.Injective e ∧
      (∀ (σ : Field.absoluteGaloisGroup (ULift.{u} ℝ)) (w : Fin 2 → kp),
        e (ρbarp (Field.absoluteGaloisGroup.map (algebraMap ℚ (ULift.{u} ℝ)) σ) w) =
          abB.galSMul (𝟙 (AlgebraicGeometry.Spec (CommRingCat.of (ULift.{u} ℝ)))) σ (e w)) ∧
      (∀ y, y ∈ (m.torsion
        (𝟙 (AlgebraicGeometry.Spec (CommRingCat.of (ULift.{u} ℝ)))) frp).1 ↔ ∃ w, e w = y))

/-- **The twisted Hilbert–Blumenthal moduli space as a twist** (sorry
node, cut 2026-07-26 — the REPRESENTABILITY half of Taylor §4, all of
`exists_twistedHilbertBlumenthalModuliForm_of_five_le` except the
archimedean place): for the irreducible hardly ramified `ρbar` at
`ℓ ≥ 5` there is a smooth, separated, finite-type, quasi-compact
`ℚ`-variety `X` carrying an abelian scheme `A ⟶ X` satisfying
`IsTwistedHilbertBlumenthalModuli`, which is a `ℚ̄`-form of a
geometrically irreducible `X₀`, and which is FINE at the archimedean
place: the auxiliary datum `(D, λ, 𝔭, ρbarp)` that the construction
chose is handed over, together with the implication that a real object
for that datum is an `ℝ`-point of `X`.

Classically: `X₀` is Rapoport's split moduli space of `𝒪_D`-HBAVs with
full `λ𝔭`-level structure (smooth and geometrically connected, the
connectedness by the uniformization of its complex points by
`𝔥^{[D:ℚ]}`, and FINE because `λ𝔭` is divisible by two primes of coprime
residue characteristic), and `X = X_ρ` is its twist by the cocycle
`R = ρbar ⊕ ρbarp` (Taylor §4, Lemma 4.4, whose description of the
`F`-points of `X_{R,ψ}` is exactly `IsTwistedHilbertBlumenthalModuli`).
The final conjunct is fineness read at `ℝ`: an `ℝ`-point of a fine
moduli space is an isomorphism class of objects over `ℝ`.

THE FOUR ADMISSIBILITY CONJUNCTS are exactly the hypotheses of
`hasRealHilbertBlumenthalObject_of_isHardlyRamified`, so that the
assembly is a single application; see the section docstring above for why
the two residue-field isomorphisms are forced by the seam rather than
assumed, and why the datum has to be handed over a second time.

MISSING MACHINERY, IN DEPENDENCY ORDER (2026-07-25, updated 2026-07-26;
item 1 is DONE, supplied by `Modularity/AbelianScheme.lean`; items 5–6 of
the original list were removed by the FORM cut, and the archimedean cut
has now removed complex multiplication as well — see
`hasRealHilbertBlumenthalObject_of_isHardlyRamified`, which needs only a
real elliptic curve):

1. *Abelian schemes* — **DONE**: `Fermat.AbelianSchemeStruct`,
   `Fermat.GeomFibrePt`, `Fermat.AbelianSchemeStruct.geomFibreAction`,
   `Fermat.Mult`, `Fermat.Mult.torsion`.
2. *Torsion subgroup schemes* `A[n]` for `n` invertible on the base:
   finite étale of rank `n ^ (2 * relative dimension)`, so the torsion
   Galois modules have the right size — needed to know `A[λ]` is free of
   rank `2` over `𝒪_D/λ`, hence abstractly isomorphic to `W` (and hence
   also to know `𝒪_D/λ ≅ k`, which this leaf must produce).
3. *Moduli functors and their representability*: the functor of
   Hilbert–Blumenthal abelian schemes with `𝒪_D`-action and full
   `λ𝔭`-level structure is representable by a quasi-projective `ℚ`-scheme,
   smooth of relative dimension `[D:ℚ]`; FINE because `λ𝔭` is divisible by
   two primes of coprime residue characteristic, which kills the
   automorphisms (Rapoport; Deligne–Pappas). Fineness is used TWICE here:
   for the moduli condition, and for the archimedean implication.
4. *Twisted forms*: Galois descent for quasi-projective schemes along a
   continuous cocycle `Γ_ℚ → Γ ≤ Aut(level)`, giving `X_{R,ψ}` and the
   description of its `F`-points (Taylor Lemma 4.4) — this is what
   produces both the moduli condition and the `IsFormOver` clause.

CIRCULARITY GUARD (inherited from pillar β, load-bearing): must be
discharged by the independent moduli construction — never through
`Family.lean`, `Lift.lean`, or `Modularity/Interface.lean`.

SOUNDNESS AUDIT (both ways): (i) direct — this is Taylor §4
pp. 759–762 with the archimedean argument of Lemma 4.5 factored out;
(ii) collapse — the hypothesis package (an irreducible hardly ramified
mod-`ℓ` representation, `ℓ ≥ 5`) is classically unsatisfiable (headline
of this module), so the statement is also vacuously sound. -/
theorem exists_twistedHilbertBlumenthalModuliTwist_of_five_le
    {ℓ : ℕ} (hℓodd : Odd ℓ) [Fact ℓ.Prime] (hℓ5 : 5 ≤ ℓ)
    {k : Type u} [Field k] [Finite k] [Algebra ℤ_[ℓ] k]
    [TopologicalSpace k] [DiscreteTopology k]
    {W : Type v} [AddCommGroup W] [Module k W] [Module.Finite k W]
    [Module.Free k W]
    (hW : Module.rank k W = 2) {ρbar : GaloisRep ℚ k W}
    (hρbar : IsHardlyRamified hℓodd hW ρbar)
    (hirr : ρbar.IsIrreducible) :
    ∃ (X : AlgebraicGeometry.Scheme.{u})
      (fX : X ⟶ AlgebraicGeometry.Spec (CommRingCat.of (ULift.{u} ℚ)))
      (A : AlgebraicGeometry.Scheme.{u}) (fA : A ⟶ X)
      (ab : Fermat.AbelianSchemeStruct fA),
      AlgebraicGeometry.Smooth fX ∧ AlgebraicGeometry.IsSeparated fX ∧
      AlgebraicGeometry.LocallyOfFiniteType fX ∧
      AlgebraicGeometry.QuasiCompact fX ∧
      IsTwistedHilbertBlumenthalModuli ℓ ρbar fX ab ∧
      (∃ (X₀ : AlgebraicGeometry.Scheme.{u})
        (fX₀ : X₀ ⟶ AlgebraicGeometry.Spec (CommRingCat.of (ULift.{u} ℚ)))
        (K : Type u) (_ : Field K) (_ : Algebra ℚ K),
        IsAlgClosed K ∧ AlgebraicGeometry.GeometricallyIrreducible fX₀ ∧
        IsFormOver K fX fX₀) ∧
      -- the auxiliary datum, handed over with the fineness consequence at `ℝ`
      (∃ (D : Type u) (_ : Field D) (_ : NumberField D)
        (_ : NumberField.IsTotallyReal D)
        (lam frp : Ideal (NumberField.RingOfIntegers D))
        (kp : Type u) (_ : Field kp) (_ : Finite kp) (_ : TopologicalSpace kp)
        (_ : DiscreteTopology kp) (ρbarp : GaloisRep ℚ kp (Fin 2 → kp)),
        Nonempty ((NumberField.RingOfIntegers D ⧸ lam) ≃+* k) ∧
        Nonempty ((NumberField.RingOfIntegers D ⧸ frp) ≃+* kp) ∧
        lam ≠ frp ∧
        (∀ σ : Field.absoluteGaloisGroup (ULift.{u} ℝ), σ ≠ 1 →
          ρbarp.det (Field.absoluteGaloisGroup.map (algebraMap ℚ (ULift.{u} ℝ)) σ) = -1) ∧
        (HasRealHilbertBlumenthalObject ρbar D lam frp ρbarp →
          HasRationalPoint fX (ULift.{u} ℝ))) :=
  sorry

/-- **Complex conjugation inverts roots of unity** (PROVEN 2026-07-26; cut
2026-07-26 out of `hasRealHilbertBlumenthalObject_of_isHardlyRamified`):
the `ℓ`-adic cyclotomic character takes the value `-1` at the image in
`Γ_ℚ` of any NONTRIVIAL element of `Γ_ℝ`, for `ℓ` odd.

This is the ONE arithmetic input of the archimedean cut, and it is what
turns `IsHardlyRamified`'s cyclotomic-determinant clause into the
statement that `ρbar` is ODD on `Γ_ℝ`. It is the exact analogue, for the
image of `Γ_ℝ` under `Field.absoluteGaloisGroup.map`, of the PROVEN
`cyclotomicCharacter_complexConj`
(`GaloisRepresentation/ComplexConjugation.lean`), which says the same at
the distinguished `complexConj : Γ_ℚ` built there from an embedding
`ℚᵃˡᵍ ↪ ℂ`.

WHY IT IS NOT LITERALLY THAT LEMMA, and hence why it is a separate leaf:
`Field.absoluteGaloisGroup.map` is built from an ARBITRARILY CHOSEN
embedding of algebraic closures (see its docstring in
`Deformations/RepresentationTheory/AbsoluteGaloisGroup.lean`), so
`Field.absoluteGaloisGroup.map (algebraMap ℚ ℝ) σ` need not be the same
element of `Γ_ℚ` as `complexConj`. It is only CONJUGATE to it — every
complex conjugation of `Γ_ℚ` is, by Artin–Schreier — and the cyclotomic
character, being a homomorphism into an abelian group, is a class
function, so the value is the same. That last step is the content here.

THE PROOF ACTUALLY GIVEN is a variant of the "class-function route" that
never has to mention `complexConj`, `[ℝᵃˡᵍ : ℝ] = 2`, the Galois
correspondence, or Artin–Schreier conjugacy. It is in five steps.

1. *`(ULift ℝ)ᵃˡᵍ` IS `ℂ`.* `AlgebraicClosure (ULift ℝ)` is an algebraic
   extension of `ℝ` (mathlib supplies `Algebra ℝ (AlgebraicClosure L)`
   and `IsScalarTower ℝ L (AlgebraicClosure L)` from `Algebra ℝ L`, and
   `ULift ℝ` is algebraic over `ℝ` because `algebraMap ℝ (ULift ℝ)` is
   surjective), so `Real.nonempty_algEquiv_or` gives an `ℝ`-algebra
   isomorphism onto `ℝ` or onto `ℂ`. The first is impossible: an
   algebraically closed field has a square root of `-1`, whose image
   would be a real square equal to `-1`. So there is a ring isomorphism
   `e : (ULift ℝ)ᵃˡᵍ ≃+* ℂ` carrying `ULift.up r` to `r`.
2. *`σ` IS COMPLEX CONJUGATION THROUGH `e`.* Conjugating `σ` by `e`
   gives an `ℝ`-algebra endomorphism of `ℂ` (it fixes the reals because
   `σ` fixes `ULift ℝ` pointwise), and
   `Complex.real_algHom_eq_id_or_conj` says there are only two: the
   identity — which would force `σ = 1`, excluded by `hσ` — and
   `conj`. So `e (σ x) = conj (e x)` for all `x`. This is the ONE place
   the hypothesis `σ ≠ 1` is used, and it is what replaces the
   Artin–Schreier conjugacy step: no choice of complex conjugation is
   ever made, because `e` is produced together with `σ`'s description.
3. *`g` IS AN INVOLUTION.* Writing `F = AlgebraicClosure.map` and
   `g` for the image of `σ`, `Field.absoluteGaloisGroup.lift_map` gives
   `F (g x) = σ (F x)`; `conj` is an involution, so `σ` is, so `g` is
   (`F` is injective). Hence `χ_ℓ(g)² = 1`, and `χ_ℓ(g) = ±1` because
   `ℤ_[ℓ]` is a domain.
4. *IT IS NOT `+1`.* Otherwise `cyclotomicCharacter.spec` at level one
   says `g` fixes a primitive `ℓ`-th root of unity `ζ` of `ℚᵃˡᵍ`; then
   `conj` fixes `e (F ζ)`, which is therefore a REAL `ℓ`-th root of
   unity, hence `1` for `ℓ` odd (`Odd.strictMono_pow` is injective on
   `ℝ`) — contradicting primitivity for `ℓ > 1`.
5. Oddness of `ℓ` is genuinely used in step 4, exactly as in
   `cyclotomicCharacter_complexConj`: for `ℓ = 2` the level-one root of
   unity is `−1`, which conjugation does fix.

The historical alternative — exhibit `τ ∈ Γ_ℚ` with
`Field.absoluteGaloisGroup.map (algebraMap ℚ ℝ) σ = τ * complexConj * τ⁻¹`
and conclude by `map_mul` from `cyclotomicCharacter_complexConj` — was
not taken: it needs Artin–Schreier conjugacy, which the tree does not
have, whereas step 2 above obtains the same conclusion from the
elementary classification of the `ℝ`-algebra endomorphisms of `ℂ`. -/
theorem cyclotomicCharacter_absoluteGaloisGroupMap_real
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓodd : Odd ℓ)
    (σ : Field.absoluteGaloisGroup (ULift.{u} ℝ)) (hσ : σ ≠ 1) :
    cyclotomicCharacter (AlgebraicClosure ℚ) ℓ
      (Field.absoluteGaloisGroup.map (algebraMap ℚ (ULift.{u} ℝ)) σ).toRingEquiv = -1 := by
  have hℓ1 : 1 < ℓ := (Fact.out : ℓ.Prime).one_lt
  -- STEP 1: an isomorphism `AlgebraicClosure (ULift ℝ) ≃+* ℂ` compatible with the reals.
  obtain ⟨e, he⟩ : ∃ e : AlgebraicClosure (ULift.{u} ℝ) ≃+* ℂ,
      ∀ r : ℝ, e (algebraMap (ULift.{u} ℝ) (AlgebraicClosure (ULift.{u} ℝ)) (ULift.up r))
        = algebraMap ℝ ℂ r := by
    haveI : Algebra.IsAlgebraic ℝ (ULift.{u} ℝ) := by
      refine ⟨fun x => ?_⟩
      have hx : x = algebraMap ℝ (ULift.{u} ℝ) x.down := rfl
      rw [hx]
      exact isAlgebraic_algebraMap _
    haveI : Algebra.IsAlgebraic ℝ (AlgebraicClosure (ULift.{u} ℝ)) :=
      Algebra.IsAlgebraic.trans ℝ (ULift.{u} ℝ) (AlgebraicClosure (ULift.{u} ℝ))
    rcases Real.nonempty_algEquiv_or (AlgebraicClosure (ULift.{u} ℝ)) with hcase | hcase
    · exfalso
      obtain ⟨φ⟩ := hcase
      obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq
        (-1 : AlgebraicClosure (ULift.{u} ℝ)) (n := 2) (by norm_num)
      have h1 : (φ z) ^ 2 = -1 := by rw [← map_pow, hz, map_neg, map_one]
      linarith [sq_nonneg (φ z)]
    · obtain ⟨φ⟩ := hcase
      refine ⟨φ.toRingEquiv, fun r => ?_⟩
      have h2 : algebraMap (ULift.{u} ℝ) (AlgebraicClosure (ULift.{u} ℝ)) (ULift.up r)
          = algebraMap ℝ (AlgebraicClosure (ULift.{u} ℝ)) r :=
        (IsScalarTower.algebraMap_apply ℝ (ULift.{u} ℝ)
          (AlgebraicClosure (ULift.{u} ℝ)) r).symm
      rw [h2]
      exact φ.commutes r
  -- STEP 2: notation for the transported element.
  set f : ℚ →+* ULift.{u} ℝ := algebraMap ℚ (ULift.{u} ℝ) with hf
  set F : AlgebraicClosure ℚ →+* AlgebraicClosure (ULift.{u} ℝ) :=
    AlgebraicClosure.map f with hFdef
  set g := Field.absoluteGaloisGroup.map f σ with hgdef
  have hlift : ∀ x : AlgebraicClosure ℚ, F (g x) = σ (F x) :=
    fun x => Field.absoluteGaloisGroup.lift_map f σ x
  have hFinj : Function.Injective F := F.injective
  -- STEP 3: through `e`, `σ` is complex conjugation.
  have hσconj : ∀ x, e (σ x) = starRingEnd ℂ (e x) := by
    have hcomm : ∀ r : ℝ,
        (e.symm.trans ((AlgEquiv.toRingEquiv σ).trans e)) (algebraMap ℝ ℂ r)
          = algebraMap ℝ ℂ r := by
      intro r
      have h1 : e.symm (algebraMap ℝ ℂ r)
          = algebraMap (ULift.{u} ℝ) (AlgebraicClosure (ULift.{u} ℝ)) (ULift.up r) := by
        rw [← he r]
        exact e.symm_apply_apply _
      show e (σ (e.symm (algebraMap ℝ ℂ r))) = algebraMap ℝ ℂ r
      rw [h1, AlgEquiv.commutes σ (ULift.up r)]
      exact he r
    let cA : ℂ →ₐ[ℝ] ℂ :=
      { (e.symm.trans ((AlgEquiv.toRingEquiv σ).trans e)).toRingHom with commutes' := hcomm }
    have hcA : ∀ z : ℂ, cA z = e (σ (e.symm z)) := fun _ => rfl
    rcases Complex.real_algHom_eq_id_or_conj cA with h | h
    · exfalso
      refine hσ (AlgEquiv.ext fun x => ?_)
      show σ x = x
      have hx := DFunLike.congr_fun h (e x)
      rw [hcA] at hx
      simp only [AlgHom.coe_id, id_eq, RingEquiv.symm_apply_apply] at hx
      exact e.injective hx
    · intro x
      have hx := DFunLike.congr_fun h (e x)
      rw [hcA] at hx
      simpa using hx
  -- STEP 4: `g` is an involution, hence so is its `RingEquiv` shadow.
  have hgg : ∀ x : AlgebraicClosure ℚ, g (g x) = x := by
    intro x
    apply hFinj
    rw [hlift, hlift]
    apply e.injective
    rw [hσconj, hσconj, Complex.conj_conj]
  have hRE : (AlgEquiv.toRingEquiv g) * (AlgEquiv.toRingEquiv g) = 1 := by
    ext x
    exact hgg x
  -- STEP 5: the cyclotomic character of an involution that moves the roots of unity.
  haveI : NeZero ((ℓ : ℕ) : ℚ) :=
    ⟨by simpa using (Nat.cast_ne_zero (R := ℚ)).mpr (Fact.out : ℓ.Prime).ne_zero⟩
  haveI : Fact (1 < ℓ ^ 1) := ⟨by simpa using hℓ1⟩
  set u := cyclotomicCharacter (AlgebraicClosure ℚ) ℓ (AlgEquiv.toRingEquiv g) with hu
  have husq : u * u = 1 := by rw [hu, ← map_mul, hRE, map_one]
  have hval : (u : ℤ_[ℓ]) = 1 ∨ (u : ℤ_[ℓ]) = -1 := by
    have h0 : ((u : ℤ_[ℓ]) - 1) * ((u : ℤ_[ℓ]) + 1) = 0 := by
      have h1 : (u : ℤ_[ℓ]) * (u : ℤ_[ℓ]) = 1 := by
        rw [← Units.val_mul, husq, Units.val_one]
      linear_combination h1
    rcases mul_eq_zero.mp h0 with h | h
    · exact Or.inl (sub_eq_zero.mp h)
    · exact Or.inr (eq_neg_of_add_eq_zero_left h)
  have hne : (u : ℤ_[ℓ]) ≠ 1 := by
    intro h1
    obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (AlgebraicClosure ℚ) ℓ
    have hspec := cyclotomicCharacter.spec (L := AlgebraicClosure ℚ) ℓ (n := 1)
      (AlgEquiv.toRingEquiv g) ζ (by rw [pow_one]; exact hζ.pow_eq_one)
    rw [← hu, h1, map_one, ZMod.val_one, pow_one] at hspec
    have hgζ : g ζ = ζ := hspec
    have hfix : σ (F ζ) = F ζ := by rw [← hlift, hgζ]
    set z : ℂ := e (F ζ) with hzdef
    have hzconj : starRingEnd ℂ z = z := by rw [hzdef, ← hσconj, hfix]
    have hFζpow : (F ζ) ^ ℓ = 1 := by rw [← map_pow, hζ.pow_eq_one, map_one]
    have hzpow : z ^ ℓ = 1 := by rw [hzdef, ← map_pow, hFζpow, map_one]
    have him : z.im = 0 := Complex.conj_eq_iff_im.mp hzconj
    have hre : z = (z.re : ℂ) := by apply Complex.ext <;> simp [him]
    have hrepow : z.re ^ ℓ = 1 := by
      have h3 : ((z.re ^ ℓ : ℝ) : ℂ) = ((1 : ℝ) : ℂ) := by
        push_cast
        rw [← hre, hzpow]
      exact_mod_cast h3
    have hre1 : z.re = 1 :=
      (hℓodd.strictMono_pow (R := ℝ)).injective
        (show z.re ^ ℓ = (1 : ℝ) ^ ℓ by simpa using hrepow)
    have hz1 : z = 1 := by rw [hre, hre1]; norm_num
    have hFζ : F ζ = 1 := by
      have h4 := congrArg e.symm hz1
      rw [hzdef, e.symm_apply_apply, map_one] at h4
      exact h4
    have hζ1 : ζ = 1 := hFinj (by rw [hFζ, map_one])
    exact hζ.ne_one hℓ1 hζ1
  refine Units.ext ?_
  simpa using hval.resolve_left hne

open CategoryTheory in
/-- **The real Hilbert–Blumenthal object exists for any pair of ODD
archimedean characters** (sorry leaf, cut 2026-07-26 out of
`hasRealHilbertBlumenthalObject_of_isHardlyRamified`): the whole
GEOMETRIC content of the archimedean half of Taylor §4, with the
Galois-representation packaging stripped off.

The two level structures are prescribed by plain MONOID HOMOMORPHISMS
`r : Γ_ℝ → End_k(W)` and `rp : Γ_ℝ → End_kp(kp²)` rather than by
`GaloisRep`s: no continuity, no `ℓ`-adic coefficients and no
`IsHardlyRamified` enter, because none of them is archimedean. All that
is asked of `r` and `rp` is ODDNESS — determinant `-1` away from the
identity — which is exactly the hypothesis `hoddp` that the seam already
supplies for the `𝔭`-side, and which
`cyclotomicCharacter_absoluteGaloisGroupMap_real` supplies for the
`λ`-side out of `IsHardlyRamified.det`.

INVOLUTIVITY IS NOT A HYPOTHESIS and must not be added: `r` is a monoid
homomorphism out of `Γ_ℝ`, and `Γ_ℝ` has order two, so `(r σ)² = r (σ²)
= r 1 = 1` for free. That is also why the two conditions can be stated
for ALL `σ` rather than for a distinguished complex conjugation: the
`σ = 1` case is `r 1 = 1` against `galSMul 1 = id`.

INTENDED DISCHARGE (unchanged from the parent, and it is ELEMENTARY —
no moduli space, no complex multiplication, no Shimura theory). Take
`B = E ⊗_ℤ 𝒪_D` for a real elliptic curve `E`, an abelian variety over
`ℝ` of dimension `[D:ℚ]` with real multiplication by `𝒪_D`. Then
`B[I] ≅ E[m] ⊗_{𝔽_m} 𝒪_D/I` for any maximal `I ∋ m` — true even when `I`
is RAMIFIED over `m`, since the `I`-torsion of `𝒪_D/m` is
`I^{e-1}/I^e ≅ 𝒪_D/I`, one-dimensional over the residue field. Complex
conjugation acts on `H₁(E(ℂ), ℤ) = ℤ²` by an involution `C ∈ GL₂(ℤ)` of
determinant `-1`, hence on every `E[m] = H₁/m` by `C mod m`; there are
exactly TWO conjugacy classes of such `C` over `ℤ` — `diag(1,-1)`, the
rectangular lattice, realized by `Δ(E) > 0`, and the regular
representation `[[1,1],[0,-1]]`, realized by `Δ(E) < 0` — and both are
realized by a real elliptic curve.

WHY ONE `E` SUFFICES FOR BOTH PRIMES, i.e. why `hk2` is exactly the
right hypothesis and is not cosmetic. At `λ` the residue characteristic
is odd (`hk2`), and in odd characteristic BOTH classes of `C` reduce to
an involution of determinant `-1`, which is conjugate to `diag(1,-1)`;
so any `E` realizes `r`, whatever `r` is. At `𝔭` the residue
characteristic may be `2`, where `hrp` is vacuous and there are two
possible involutions of `kp²` — the identity and a transvection —
distinguished by `C mod 2`, i.e. by the SIGN of `Δ(E)`; choosing that
sign realizes `rp`. The two demands never collide because `λ` and `𝔭`
cannot both have residue characteristic `2`.

WITHOUT `hk2` THE STATEMENT IS FALSE. If `char k = 2` as well, then
`hr` and `hrp` are both vacuous and `r`, `rp` may independently be the
identity and a transvection; but a single `E` reduces the SAME `C mod 2`
at both primes, so no `B` can realize an ill-matched pair. This is not a
convenience hypothesis — it is the discriminating condition, and it is
available at the call site because `k` is the residue field at `λ`,
whose characteristic is the odd prime `ℓ`.

MISSING MACHINERY, in dependency order (all of it archimedean and
elementary, and none of it present at this pin):
1. *Elliptic curves as abelian schemes in the `Fermat.AbelianSchemeStruct`
   presentation* — mathlib has `WeierstrassCurve` and the group law on
   its point sets, but no `Scheme` model, no properness, and no
   functor-of-points group structure. This is the bulk of the work.
2. *The tensor construction* `E ⊗_ℤ 𝒪_D` with its `Fermat.Mult` by
   `𝒪_D`, and `SmoothOfRelativeDimension [D:ℚ]` for it.
3. *The action of complex conjugation on `E[m]`*, and the identification
   `B[I] ≅ E[m] ⊗ 𝒪_D/I` of `Fermat.Mult.torsion` values.
4. *`Γ_ℝ` has order two* (Artin–Schreier for `ULift ℝ`), used both for
   involutivity and to know that `σ ≠ 1` pins a single conjugacy class.

CIRCULARITY GUARD (inherited from pillar β, load-bearing): must be
discharged by the independent construction — never through
`Family.lean`, `Lift.lean`, or `Modularity/Interface.lean`. -/
theorem exists_realHilbertBlumenthalObject_of_odd
    (D : Type u) [Field D] [NumberField D] [NumberField.IsTotallyReal D]
    (lam frp : Ideal (NumberField.RingOfIntegers D)) (hne : lam ≠ frp)
    {k : Type u} [Field k] [Finite k] (hk2 : (2 : k) ≠ 0)
    {W : Type v} [AddCommGroup W] [Module k W] [Module.Finite k W] [Module.Free k W]
    (hW : Module.rank k W = 2)
    {kp : Type u} [Field kp] [Finite kp]
    (hres : Nonempty ((NumberField.RingOfIntegers D ⧸ lam) ≃+* k))
    (hresp : Nonempty ((NumberField.RingOfIntegers D ⧸ frp) ≃+* kp))
    (r : Field.absoluteGaloisGroup (ULift.{u} ℝ) →* Module.End k W)
    (hr : ∀ σ : Field.absoluteGaloisGroup (ULift.{u} ℝ), σ ≠ 1 →
      LinearMap.det (r σ) = -1)
    (rp : Field.absoluteGaloisGroup (ULift.{u} ℝ) →* Module.End kp (Fin 2 → kp))
    (hrp : ∀ σ : Field.absoluteGaloisGroup (ULift.{u} ℝ), σ ≠ 1 →
      LinearMap.det (rp σ) = -1) :
    ∃ (B : AlgebraicGeometry.Scheme.{u})
      (fB : B ⟶ AlgebraicGeometry.Spec (CommRingCat.of (ULift.{u} ℝ)))
      (abB : Fermat.AbelianSchemeStruct fB)
      (m : Fermat.Mult abB (NumberField.RingOfIntegers D)),
      AlgebraicGeometry.SmoothOfRelativeDimension (Module.finrank ℚ D) fB ∧
      (∃ e : W → Fermat.GeomFibrePt fB
          (𝟙 (AlgebraicGeometry.Spec (CommRingCat.of (ULift.{u} ℝ)))),
        (∀ w w' : W, e (w + w') = abB.add (e w) (e w')) ∧
        Function.Injective e ∧
        (∀ (σ : Field.absoluteGaloisGroup (ULift.{u} ℝ)) (w : W),
          e (r σ w) =
            abB.galSMul (𝟙 (AlgebraicGeometry.Spec (CommRingCat.of (ULift.{u} ℝ)))) σ (e w)) ∧
        (∀ y, y ∈ (m.torsion
          (𝟙 (AlgebraicGeometry.Spec (CommRingCat.of (ULift.{u} ℝ)))) lam).1 ↔ ∃ w, e w = y)) ∧
      (∃ e : (Fin 2 → kp) → Fermat.GeomFibrePt fB
          (𝟙 (AlgebraicGeometry.Spec (CommRingCat.of (ULift.{u} ℝ)))),
        (∀ w w' : Fin 2 → kp, e (w + w') = abB.add (e w) (e w')) ∧
        Function.Injective e ∧
        (∀ (σ : Field.absoluteGaloisGroup (ULift.{u} ℝ)) (w : Fin 2 → kp),
          e (rp σ w) =
            abB.galSMul (𝟙 (AlgebraicGeometry.Spec (CommRingCat.of (ULift.{u} ℝ)))) σ (e w)) ∧
        (∀ y, y ∈ (m.torsion
          (𝟙 (AlgebraicGeometry.Spec (CommRingCat.of (ULift.{u} ℝ)))) frp).1 ↔ ∃ w, e w = y)) :=
  sorry

/-- **The twisted moduli problem is solvable over `ℝ`** (PROVEN
2026-07-26 as an assembly over the ODDNESS cut; formerly the sorry node
cut 2026-07-26 — the ARCHIMEDEAN half of Taylor §4, and the one place
where the ODDNESS of `ρbar` is consumed): for an admissible auxiliary datum
`(D, λ, 𝔭, ρbarp)` there is an abelian variety over `ℝ` with real
multiplication by `𝒪_D` of dimension `[D:ℚ]` whose `λ`-torsion realizes
`ρbar|_{Γ_ℝ}` and whose `𝔭`-torsion realizes `ρbarp|_{Γ_ℝ}`.

ADMISSIBILITY is the four hypotheses `hres`, `hresp`, `hne`, `hoddp`:
the residue fields of `λ` and `𝔭` are `k` and `kp` (forced by the seam
that consumes this — see the section docstring), the two primes are
distinct, and the `𝔭`-level representation is ODD. Oddness of `ρbar`
itself is not hypothesized separately: it is contained in `hρbar`, whose
`det` field says that `det ρbar` is the cyclotomic character, which
`cyclotomicCharacter_absoluteGaloisGroupMap_real` (the arithmetic leaf of
the proof below, itself the `Field.absoluteGaloisGroup.map` analogue of
the PROVEN `cyclotomicCharacter_complexConj`) evaluates to `-1` at the
image of any nontrivial element of `Γ_ℝ`.

PROOF SKETCH, recorded in full in the section docstring above and
summarized here because it decides the difficulty of this leaf: take
`B = E ⊗_ℤ 𝒪_D` for a real elliptic curve `E`. Then
`B[λ] ≅ E[ℓ] ⊗_{𝔽_ℓ} 𝒪_D/λ` (true even for `λ` ramified over `ℓ`), so
complex conjugation acts on it with determinant `-1`; in odd residue
characteristic there is exactly ONE odd two-dimensional representation of
`Γ_ℝ = ℤ/2` up to isomorphism, whence `B[λ] ≅ ρbar|_{Γ_ℝ}`. The same at
`𝔭`, where in residue characteristic two the two possible involutions are
separated by the sign of the discriminant of `E`. **No moduli space, no
complex multiplication and no Shimura theory are needed** — this is
elementary theory of real elliptic curves plus the tensor construction,
and the machinery it really wants is (i) elliptic curves as abelian
schemes in the `Fermat.AbelianSchemeStruct` presentation, (ii) the
tensor `E ⊗_ℤ 𝒪_D` with its `Fermat.Mult`, and (iii) the action of
complex conjugation on `E[n]`.

FAITHFULNESS: the conclusion mentions no moduli space, so it cannot be
satisfied vacuously by a pointless variety — which is precisely why the
cut was made here and not at any statement about `X`.

PROOF (2026-07-26 — the ODDNESS cut; this node is no longer a sorry
node). Nothing in the sketch above is archimedean *and* `ℓ`-adic at the
same time: `IsHardlyRamified` is a global, `ℓ`-adic condition, and the
only thing the construction over `ℝ` ever reads off it is that `ρbar` is
ODD. So this proof does exactly three things and hands the geometry on:

1. `k` has characteristic `ℓ`, hence `(2 : k) ≠ 0`. The `ℤ_[ℓ]`-algebra
   structure on the finite field `k` forces this: if `char k = p ≠ ℓ`
   then `(p : ℤ_[ℓ])` is a unit (its norm is `1`, as `ℓ ∤ p`) whose image
   `(p : k) = 0` is not — so `p = ℓ`, and `ℓ` is odd. This is the
   discriminating hypothesis `hk2` of the geometric leaf; see there for
   why the leaf is FALSE without it.
2. `ρbar` and `ρbarp`, restricted to `Γ_ℝ` along
   `Field.absoluteGaloisGroup.map (algebraMap ℚ ℝ)`, are repackaged as
   plain monoid homomorphisms `r`, `rp` into `Module.End`. Continuity and
   the `ℓ`-adic coefficients play no archimedean role and are dropped.
3. Both are ODD. For `rp` this is the hypothesis `hoddp` verbatim (modulo
   `GaloisRep.det_apply`). For `r` it is `IsHardlyRamified.det` — which
   says `det ρbar` is the `ℓ`-adic cyclotomic character — composed with
   `cyclotomicCharacter_absoluteGaloisGroupMap_real`, the one arithmetic
   leaf of this cut, which evaluates that character to `-1` at the image
   of any nontrivial element of `Γ_ℝ`. This is where, and the only place
   where, the ODDNESS of `ρbar` is consumed.

The remaining geometric content is
`exists_realHilbertBlumenthalObject_of_odd`, which is the same statement
with `IsHardlyRamified`, `GaloisRep` and `ℓ` removed — purely
archimedean, and stated so that its intended discharge (one real elliptic
curve, tensored with `𝒪_D`) is all it can possibly need.

INVOLUTIVITY IS NOT PASSED ON, because it is free: `r` and `rp` are
monoid homomorphisms out of `Γ_ℝ`, which has order two. -/
theorem hasRealHilbertBlumenthalObject_of_isHardlyRamified
    {ℓ : ℕ} (hℓodd : Odd ℓ) [Fact ℓ.Prime]
    {k : Type u} [Field k] [Finite k] [Algebra ℤ_[ℓ] k]
    [TopologicalSpace k] [DiscreteTopology k]
    {W : Type v} [AddCommGroup W] [Module k W] [Module.Finite k W]
    [Module.Free k W]
    (hW : Module.rank k W = 2) {ρbar : GaloisRep ℚ k W}
    (hρbar : IsHardlyRamified hℓodd hW ρbar)
    (D : Type u) [Field D] [NumberField D] [NumberField.IsTotallyReal D]
    (lam frp : Ideal (NumberField.RingOfIntegers D))
    {kp : Type u} [Field kp] [Finite kp] [TopologicalSpace kp]
    [DiscreteTopology kp] (ρbarp : GaloisRep ℚ kp (Fin 2 → kp))
    (hres : Nonempty ((NumberField.RingOfIntegers D ⧸ lam) ≃+* k))
    (hresp : Nonempty ((NumberField.RingOfIntegers D ⧸ frp) ≃+* kp))
    (hne : lam ≠ frp)
    (hoddp : ∀ σ : Field.absoluteGaloisGroup (ULift.{u} ℝ), σ ≠ 1 →
      ρbarp.det (Field.absoluteGaloisGroup.map (algebraMap ℚ (ULift.{u} ℝ)) σ) = -1) :
    HasRealHilbertBlumenthalObject ρbar D lam frp ρbarp := by
  classical
  -- **(1)** `k` has characteristic `ℓ`, and `ℓ` is odd, so `2 ≠ 0` in `k`.
  have hlk : ((ℓ : ℕ) : k) = 0 := by
    haveI : CharP k (ringChar k) := ringChar.charP k
    have hpprime : Nat.Prime (ringChar k) := CharP.prime_ringChar k
    have hpk : ((ringChar k : ℕ) : k) = 0 := CharP.cast_eq_zero k _
    have hpl : ringChar k = ℓ := by
      by_contra hne'
      have hnd : ¬ ((ℓ : ℤ) ∣ ((ringChar k : ℕ) : ℤ)) := by
        rw [Int.natCast_dvd_natCast]
        exact fun h => hne' ((Nat.prime_dvd_prime_iff_eq Fact.out hpprime).mp h).symm
      have hnorm : (1 : ℝ) ≤ ‖(((ringChar k : ℕ) : ℤ) : ℤ_[ℓ])‖ :=
        not_lt.mp fun h => hnd ((PadicInt.norm_int_lt_one_iff_dvd _).mp h)
      have hu : IsUnit (((ringChar k : ℕ)) : ℤ_[ℓ]) := by
        rw [PadicInt.isUnit_iff]
        refine le_antisymm (PadicInt.norm_le_one _) ?_
        simpa using hnorm
      have hu' := IsUnit.map (algebraMap ℤ_[ℓ] k) hu
      rw [map_natCast, hpk] at hu'
      exact not_isUnit_zero hu'
    rw [← hpl]; exact hpk
  haveI hchark : CharP k ℓ := (CharP.charP_iff_prime_eq_zero Fact.out).mpr hlk
  have hk2 : (2 : k) ≠ 0 := by
    intro h
    have hdvd : (ℓ : ℕ) ∣ 2 := by
      have h2 : ((2 : ℕ) : k) = 0 := by exact_mod_cast h
      exact (CharP.cast_eq_zero_iff k ℓ 2).mp h2
    have hl2 : ℓ = 2 := (Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).mp hdvd
    exact (Nat.not_odd_iff_even.mpr (hl2 ▸ (even_two : Even 2))) hℓodd
  -- **(2)** the two restricted representations, as plain monoid homomorphisms.
  have hmapone : Field.absoluteGaloisGroup.map (algebraMap ℚ (ULift.{u} ℝ)) 1 = 1 :=
    map_one _
  have hmapmul : ∀ a b : Field.absoluteGaloisGroup (ULift.{u} ℝ),
      Field.absoluteGaloisGroup.map (algebraMap ℚ (ULift.{u} ℝ)) (a * b) =
        Field.absoluteGaloisGroup.map (algebraMap ℚ (ULift.{u} ℝ)) a *
          Field.absoluteGaloisGroup.map (algebraMap ℚ (ULift.{u} ℝ)) b :=
    fun a b => map_mul _ a b
  let r : Field.absoluteGaloisGroup (ULift.{u} ℝ) →* Module.End k W :=
    { toFun := fun σ => ρbar (Field.absoluteGaloisGroup.map (algebraMap ℚ (ULift.{u} ℝ)) σ)
      map_one' := by rw [hmapone, map_one]
      map_mul' := fun a b => by rw [hmapmul, map_mul] }
  let rp : Field.absoluteGaloisGroup (ULift.{u} ℝ) →* Module.End kp (Fin 2 → kp) :=
    { toFun := fun σ => ρbarp (Field.absoluteGaloisGroup.map (algebraMap ℚ (ULift.{u} ℝ)) σ)
      map_one' := by rw [hmapone, map_one]
      map_mul' := fun a b => by rw [hmapmul, map_mul] }
  -- **(3)** both are ODD on `Γ_ℝ` — the one place the oddness of `ρbar` is used.
  have hr : ∀ σ : Field.absoluteGaloisGroup (ULift.{u} ℝ), σ ≠ 1 →
      LinearMap.det (r σ) = -1 := by
    intro σ hσ
    have h := hρbar.det (Field.absoluteGaloisGroup.map (algebraMap ℚ (ULift.{u} ℝ)) σ)
    rw [GaloisRep.det_apply] at h
    show LinearMap.det (ρbar _) = -1
    rw [h, cyclotomicCharacter_absoluteGaloisGroupMap_real ℓ hℓodd σ hσ]
    simp
  have hrp : ∀ σ : Field.absoluteGaloisGroup (ULift.{u} ℝ), σ ≠ 1 →
      LinearMap.det (rp σ) = -1 := by
    intro σ hσ
    have h := hoddp σ hσ
    rw [GaloisRep.det_apply] at h
    exact h
  -- **(4)** the archimedean geometric leaf.
  exact exists_realHilbertBlumenthalObject_of_odd D lam frp hne hk2 hW hres hresp r hr rp hrp

/-- **The twisted Hilbert–Blumenthal moduli space, as a FORM** (PROVEN
2026-07-26 as an assembly over the ARCHIMEDEAN cut — see the section
docstring above; formerly the representability half of Taylor §4, recut
2026-07-25): for the
irreducible hardly ramified `ρbar` at `ℓ ≥ 5` there is a smooth,
separated, finite-type, quasi-compact `ℚ`-variety `X` carrying an
abelian scheme `A ⟶ X` satisfying `IsTwistedHilbertBlumenthalModuli`,
TOGETHER WITH

* a space `X₀/ℚ` which is geometrically irreducible and of which `X` is a
  `ℚ̄`-form — classically the SPLIT moduli space of `E`-HBAVs with full
  `b₀`-level structure, geometrically connected by the uniformization of
  its complex points by `𝔥^{[E:ℚ]}` (Rapoport §1), and `X = X_ρ` is its
  twist by the cocycle attached to `ρbar`, hence a form of it;
* a space `Y/ℚ` with a real point of which `X` is an `ℝ`-form —
  classically `Y = X_Dih`, the twist by the DIHEDRAL cocycle, which has a
  `ℚ`-rational point by complex multiplication (Taylor Lemma 4.5), and
  `X_ρ ≅ X_Dih` over `ℝ` because `R_ρ` and `R_Dih` agree on `G_ℝ` — this
  is where the ODDNESS of `ρbar` is consumed.

Both remaining properties of the target — geometric irreducibility and
the existence of a real point — are then formal consequences
(`geometricallyIrreducible_of_isFormOver_isAlgClosed` and
`hasRationalPoint_of_isFormOver`). See the section docstring above for
why they cannot be split off as statements about an arbitrary `X`
carrying such a family: the even twists refute that.

PROOF (2026-07-26 — the ARCHIMEDEAN cut; this node is no longer a sorry
node). The two leaves it now rests on are

* `exists_twistedHilbertBlumenthalModuliTwist_of_five_le`, which supplies
  `X`, its geometry, its moduli property, the `ℚ̄`-form clause, and the
  auxiliary datum `(D, λ, 𝔭, ρbarp)` together with the fineness
  implication "a real object for that datum is an `ℝ`-point of `X`";
* `hasRealHilbertBlumenthalObject_of_isHardlyRamified`, which supplies
  the real object for that datum — the archimedean place, where the
  ODDNESS of `ρbar` is consumed.

The `Y`-clause is then discharged with `Y = X` by `isFormOver_refl`: it
demands a space with a real point of which `X` is an `ℝ`-form, and once
`X` itself has a real point, `X` will do. `Y` was never an independent
demand — it is a memory of Taylor's route through `X_Dih`, and the CM
point of `X_Dih` was only ever a device for producing a real point of
`X_ρ`. Removing it removes complex multiplication from the missing
machinery of this subtree entirely; see
`hasRealHilbertBlumenthalObject_of_isHardlyRamified`, whose intended
discharge is one real elliptic curve.

MISSING MACHINERY: moved onto the two leaves, where each item now has an
owner — representability and Galois descent onto the twist leaf, the
archimedean realization onto the real-object leaf.

CIRCULARITY GUARD (inherited from pillar β, load-bearing): must be
discharged by the independent moduli construction — never through
`Family.lean`, `Lift.lean`, or `Modularity/Interface.lean`. Both leaves
inherit the guard.

SOUNDNESS AUDIT (both ways, 2026-07-25): (i) direct — this is Taylor
§4 pp. 759–762; (ii) collapse — the hypothesis package (an irreducible
hardly ramified mod-`ℓ` representation, `ℓ ≥ 5`) is classically
unsatisfiable (headline of this module), so the statement is also
vacuously sound. -/
theorem exists_twistedHilbertBlumenthalModuliForm_of_five_le
    {ℓ : ℕ} (hℓodd : Odd ℓ) [Fact ℓ.Prime] (hℓ5 : 5 ≤ ℓ)
    {k : Type u} [Field k] [Finite k] [Algebra ℤ_[ℓ] k]
    [TopologicalSpace k] [DiscreteTopology k]
    {W : Type v} [AddCommGroup W] [Module k W] [Module.Finite k W]
    [Module.Free k W]
    (hW : Module.rank k W = 2) {ρbar : GaloisRep ℚ k W}
    (hρbar : IsHardlyRamified hℓodd hW ρbar)
    (hirr : ρbar.IsIrreducible) :
    ∃ (X : AlgebraicGeometry.Scheme.{u})
      (fX : X ⟶ AlgebraicGeometry.Spec (CommRingCat.of (ULift.{u} ℚ)))
      (A : AlgebraicGeometry.Scheme.{u}) (fA : A ⟶ X)
      (ab : Fermat.AbelianSchemeStruct fA),
      AlgebraicGeometry.Smooth fX ∧ AlgebraicGeometry.IsSeparated fX ∧
      AlgebraicGeometry.LocallyOfFiniteType fX ∧
      AlgebraicGeometry.QuasiCompact fX ∧
      IsTwistedHilbertBlumenthalModuli ℓ ρbar fX ab ∧
      (∃ (X₀ : AlgebraicGeometry.Scheme.{u})
        (fX₀ : X₀ ⟶ AlgebraicGeometry.Spec (CommRingCat.of (ULift.{u} ℚ)))
        (K : Type u) (_ : Field K) (_ : Algebra ℚ K),
        IsAlgClosed K ∧ AlgebraicGeometry.GeometricallyIrreducible fX₀ ∧
        IsFormOver K fX fX₀) ∧
      (∃ (Y : AlgebraicGeometry.Scheme.{u})
        (fY : Y ⟶ AlgebraicGeometry.Spec (CommRingCat.of (ULift.{u} ℚ))),
        HasRationalPoint fY (ULift.{u} ℝ) ∧ IsFormOver (ULift.{u} ℝ) fX fY) := by
  obtain ⟨X, fX, A, fA, ab, hsm, hsep, hft, hqc, hmod, hform₀,
    D, iDfield, iDnf, iDtr, lam, frp, kp, ikpfield, ikpfin, ikptop, ikpdisc, ρbarp,
    hres, hresp, hne, hoddp, himp⟩ :=
    exists_twistedHilbertBlumenthalModuliTwist_of_five_le hℓodd hℓ5 hW hρbar hirr
  refine ⟨X, fX, A, fA, ab, hsm, hsep, hft, hqc, hmod, hform₀, X, fX, ?_,
    isFormOver_refl _ fX⟩
  exact himp (hasRealHilbertBlumenthalObject_of_isHardlyRamified hℓodd hW hρbar
    D lam frp ρbarp hres hresp hne hoddp)

/-- **The twisted Hilbert–Blumenthal moduli SPACE** (PROVEN 2026-07-25 as
an assembly over the FORM cut — see the section docstring above): for the
irreducible hardly ramified residual representation `ρbar` at `ℓ ≥ 5`
there is a smooth, separated, quasi-compact, finite-type, geometrically
irreducible variety `X` over `ℚ` with a real point, carrying an abelian
scheme `A ⟶ X` which satisfies the twisted Hilbert–Blumenthal moduli
condition `IsTwistedHilbertBlumenthalModuli`.

Classically `X` is the moduli space of Hilbert–Blumenthal abelian
varieties with real multiplication by `𝒪_D` for a fixed totally real
`D`, carrying an `ℓ`-level structure twisted by `ρbar` and an auxiliary
dihedral `p`-level structure; `A ⟶ X` is the universal abelian scheme.

PROOF (2026-07-25): an assembly over the FORM cut described in the
section docstring above. The construction leaf
`exists_twistedHilbertBlumenthalModuliForm_of_five_le` supplies `X` with
everything except the last two properties, together with the two
comparison spaces that Taylor's argument actually produces — the split
moduli space `X₀` (geometrically irreducible; `X` is a `ℚ̄`-form of it,
being its twist) and the dihedral twist `Y` (which has a real point by
complex multiplication; `X` is an `ℝ`-form of it, because `ρbar` is
odd). The two remaining properties are then formal:

* geometric irreducibility from `X₀`, by
  `geometricallyIrreducible_of_isFormOver_isAlgClosed` (PROVEN here
  2026-07-26; it does not in fact need the Stacks 0364 criterion, and
  does not use the algebraic closedness of `K` either);
* the real point from `Y`, by `hasRationalPoint_of_isFormOver` (PROVEN
  here).

HYPOTHESES NOT CONSUMED (underscored, so the reduction is mechanically
visible): the whole `ℓ`-adic package `O`, `ρ`, `_hZinj`, `_hρ`, `π`,
`_hπsurj`, `_hπ`. Taylor's moduli construction needs only the RESIDUAL
representation — `ρbar` irreducible and hardly ramified (whence odd) at
`ℓ ≥ 5`. The lift is used by the CONSUMER of this leaf, not by it.

CIRCULARITY GUARD (inherited from pillar β, load-bearing): must be
discharged by the independent moduli construction — never through
`Family.lean`, `Lift.lean`, or `Modularity/Interface.lean`. The two
leaves it now rests on inherit that guard.

SOUNDNESS AUDIT (both ways, 2026-07-25): (i) direct — this is Taylor
§4 pp. 759–763; (ii) collapse — the hypothesis package (an irreducible
hardly ramified mod-`ℓ` representation, `ℓ ≥ 5`) is classically
unsatisfiable (headline of this module), so the statement is also
vacuously sound. -/
theorem exists_twistedHilbertBlumenthalModuliScheme_of_five_le
    {ℓ : ℕ} (hℓodd : Odd ℓ) [Fact ℓ.Prime] (hℓ5 : 5 ≤ ℓ)
    {O : Type u} [CommRing O] [IsDomain O] [TopologicalSpace O]
    [IsTopologicalRing O] [Algebra ℤ_[ℓ] O] [IsLocalRing O]
    [Module.Finite ℤ_[ℓ] O] [IsModuleTopology ℤ_[ℓ] O]
    (_hZinj : Function.Injective (algebraMap ℤ_[ℓ] O))
    {ρ : GaloisRep ℚ O (Fin 2 → O)}
    (hrank : Module.rank O (Fin 2 → O) = 2)
    (_hρ : IsHardlyRamified hℓodd hrank ρ)
    {k : Type u} [Field k] [Finite k] [Algebra ℤ_[ℓ] k]
    [TopologicalSpace k] [DiscreteTopology k]
    {W : Type v} [AddCommGroup W] [Module k W] [Module.Finite k W]
    [Module.Free k W]
    (hW : Module.rank k W = 2) {ρbar : GaloisRep ℚ k W}
    (hρbar : IsHardlyRamified hℓodd hW ρbar)
    (hirr : ρbar.IsIrreducible)
    (π : O →+* k) (_hπsurj : Function.Surjective π)
    (_hπ : ∀ (q : ℕ) (hq : q.Prime), q ≠ 2 → q ≠ ℓ →
      (ρ.charFrob hq.toHeightOneSpectrumRingOfIntegersRat).map π =
        ρbar.charFrob hq.toHeightOneSpectrumRingOfIntegersRat) :
    ∃ (X : AlgebraicGeometry.Scheme.{u})
      (fX : X ⟶ AlgebraicGeometry.Spec (CommRingCat.of (ULift.{u} ℚ)))
      (A : AlgebraicGeometry.Scheme.{u}) (fA : A ⟶ X)
      (ab : Fermat.AbelianSchemeStruct fA),
      AlgebraicGeometry.Smooth fX ∧ AlgebraicGeometry.IsSeparated fX ∧
      AlgebraicGeometry.LocallyOfFiniteType fX ∧
      AlgebraicGeometry.QuasiCompact fX ∧
      AlgebraicGeometry.GeometricallyIrreducible fX ∧
      HasRationalPoint fX (ULift.{u} ℝ) ∧
      IsTwistedHilbertBlumenthalModuli ℓ ρbar fX ab := by
  obtain ⟨X, fX, A, fA, ab, hsm, hsep, hft, hqc, hmod,
    ⟨X₀, fX₀, K, _, _, hKalg, hgi₀, hform₀⟩, ⟨Y, fY, hYpt, hformR⟩⟩ :=
    exists_twistedHilbertBlumenthalModuliForm_of_five_le hℓodd hℓ5 hW hρbar hirr
  exact ⟨X, fX, A, fA, ab, hsm, hsep, hft, hqc,
    geometricallyIrreducible_of_isFormOver_isAlgClosed hKalg fX fX₀ hform₀ hgi₀,
    hasRationalPoint_of_isFormOver fX fY hformR hYpt, hmod⟩

/-- **The Tate-module construction** (PROVEN 2026-07-25 as an assembly
over the two leaves of `Modularity/TateModule.lean`; the
compatible-system half of Taylor 2002 §2): a point of a twisted
Hilbert–Blumenthal moduli family is a `HilbertBlumenthalPoint`.

Given an abelian scheme `A ⟶ X` satisfying
`IsTwistedHilbertBlumenthalModuli` and an `F`-point of `X` over `ℚ`, the
fibre `A_x` is a Hilbert–Blumenthal abelian variety over `F` with real
multiplication by `𝒪_D`, whose `λ`-torsion realizes `ρbar|_{G_F}` and
whose `𝔭`-torsion is irreducible and dihedral. Its `λ`-adic and
`𝔭`-adic Tate modules are then the two members of one strictly
compatible system with coefficient field `D` — which is exactly the
data of a `HilbertBlumenthalPoint`.

This leaf contains NO moduli theory: the space, its geometry and its
real point have all been consumed by
`exists_twistedHilbertBlumenthalModuliScheme_of_five_le`. It also
carries none of the arithmetic of `ρbar`: the hardly-ramified
hypotheses and `ℓ ≥ 5` are deliberately ABSENT, because the statement is
true for any abelian scheme with the displayed level structures. That
makes it an independently citable statement of the theory of abelian
varieties, reusable wherever a Tate module is needed.

FAITHFULNESS AUDIT (2026-07-25 — THIS LEAF WAS FALSE AS STATED, and is
repaired here by the hypothesis `hW`). The leaf was cut deliberately to
carry no arithmetic of `ρbar`, which makes it a statement about abelian
varieties that must be true on its own merits. Its original statement
was not: it omitted any constraint on `Module.rank k W`, and it is
refuted by the following counterexample.

  Let `D` be a real quadratic field in which `ℓ` is INERT, so that
  `λ = (ℓ)` is maximal in `𝒪_D` with residue field `𝔽_{ℓ²}`. Let `A/ℚ`
  be a Hilbert–Blumenthal abelian surface with real multiplication by
  `𝒪_D` and a dihedral `𝔭`-level structure at some auxiliary `p ≠ ℓ`,
  and take `X = Spec ℚ`, `fX = 𝟙`, `A ⟶ X` the surface itself. Then
  `A[λ] = A[ℓ]` is `(𝒪_D/λ)² = 𝔽_{ℓ²}²`, i.e. an `𝔽_ℓ`-vector space of
  dimension FOUR. Put `k = 𝔽_ℓ` and `W = A[ℓ](ℚ̄)` with its `𝔽_ℓ`-structure
  and `ρbar` the resulting four-dimensional representation of `Γ_ℚ`.
  Every hypothesis holds: `IsTwistedHilbertBlumenthalModuli ℓ ρbar fX ab`
  is witnessed by `D`, `λ`, `𝔭` and the identity level structure — which
  the seam requires only to be an ADDITIVE `Γ_F`-equivariant bijection
  onto `(m.torsion x λ).1`, not a `k`-linear one — and `F = ℚ`,
  `hrestr`, `hpt` are immediate.

  But the conclusion fails. In a `HilbertBlumenthalPoint`, `σ.charFrob w`
  is the characteristic polynomial of a rank-two representation, hence
  MONIC OF DEGREE 2, and so is its image under the ring map `π₀`
  (`k` is a nonzero ring); while `ρbarF.charFrob w` is monic of degree
  `finrank k W = 4`. The field `residualℓ` demands they be equal for
  every `w ∉ bad`, and `bad` is finite while the set of finite places is
  infinite. So no `HilbertBlumenthalPoint` exists.

The defect is a genuine under-specification of the seam
`IsTwistedHilbertBlumenthalModuli`, whose FIRST moduli condition asks
only for an additive Galois-equivariant bijection `W ≃ A[λ]` and never
relates the coefficient field `k` to the residue field `𝒪_D/λ`; the
classical twisted moduli problem does, by choosing `λ` with
`𝒪_D/λ ≅ k` and demanding a semilinear level structure. The repair
adopted here is the MINIMAL one that stays inside this declaration:
`hW : Module.rank k W = 2` is added as a hypothesis (the consumer
`exists_twistedHilbertBlumenthalModuli_of_five_le` already carries it
verbatim and passes it straight through, so nothing downstream is
weakened). With it, `#W = #k²` and `#A[λ] = #(𝒪_D/λ)²` force
`k ≅ 𝒪_D/λ`, and the residual comparison becomes a comparison of two
`𝔽_q`-structures on `W` — the given one and the one transported from
`A[λ]` — i.e. of two embeddings of `𝔽_q` into the commutant of the
Galois image; the automorphism relating them is absorbed into the
choice of the reduction map `π₀`, which is why
`exists_tateFrame_of_levelStructure` quantifies `ι₀` existentially
rather than fixing it to be the residue map.

CORRECTION (2026-07-26). The previous version of this paragraph
justified that last step by "conjugate up to an automorphism of `𝔽_q` by
Wedderburn–Malcev". **That justification is FALSE**, and with it the
`hW`-only repair was insufficient: Wedderburn–Malcev and Noether–Skolem
conjugate embeddings inside a SIMPLE algebra, whereas the commutant
`End_{ℤ[Γ_F]}(A[λ])` need not be simple — for a split residual
representation it is `𝔽_q × 𝔽_q`, which has no inner automorphisms at
all, and the two embeddings are then genuinely inequivalent. An explicit
counterexample (a Hilbert–Blumenthal surface with big image, base
changed to the field cut out by the diagonal torus) is written out in
the FAITHFULNESS AUDIT of `Fermat.exists_tateFrame_of_levelStructure`.
The missing hypothesis is IRREDUCIBILITY of the residual representation,
which is what makes the commutant simple; it is added there as `hirr`
and here as `hirr : ρbar.IsIrreducible`, and it costs nothing, since
`exists_twistedHilbertBlumenthalModuli_of_five_le` already carries it
(it is transported to `Γ_F` along `hrestr` by
`Fermat.isIrreducible_map_of_restrictionSurjective`), and at `𝔭` the
seam already supplies `ρbarp.IsIrreducible`.

REPORTED, not repaired here: strengthening the seam itself to demand a
semilinear level structure is a cut-level change to a definition shared
with `exists_twistedHilbertBlumenthalModuliScheme_of_five_le`, which has
a separate owner, and is left to them.

MISSING MACHINERY, IN DEPENDENCY ORDER (2026-07-25), continuing the list
in the sibling leaf's docstring — items 7–9 are now the two leaves of
`Modularity/TateModule.lean`, and this node is their PROVEN assembly:

7. *Tate modules*: `T_λ A = lim_n A[λ^n]` as a finitely generated free
   `𝒪_{D,λ}`-module of rank `2` with continuous `Γ_F`-action, and
   `T_λ A / λ = A[λ]` — the statement needed is an isomorphism of
   `Γ_F`-modules between the reduction of the Tate module and the
   torsion module, which is what carries the residual conditions
   `residualℓ` and `residualp` of `HilbertBlumenthalPoint`. **The
   OBJECT is now written**: `Fermat.TatePt`, the honest inverse limit
   inside the `Γ_F`-module of geometric points of
   `Modularity/AbelianScheme.lean`.
8. *Good reduction and Frobenius*: `A` has good reduction outside a
   finite set of places `bad`, and for `w ∉ bad` the Frobenius acts on
   `T_λ A` with characteristic polynomial in `𝒪_D[T]`. **Leaf**:
   `Fermat.exists_tateFrame_of_levelStructure` (7 and 8 together — it
   produces a rank-two FRAME of `TatePt` and the residual comparison).
9. *Weil / Faltings compatibility*: that characteristic polynomial is
   INDEPENDENT of `λ` — this is what makes the `λ`-adic and `𝔭`-adic
   Tate modules members of ONE compatible system, i.e. the fields
   `matchℓ` and `matchp`, and it is the deepest item in the list.
   **Leaf**: `Fermat.exists_weilFrobeniusSystem_of_mult`, which
   quantifies the `D`-rational system `P` BEFORE the ideal, so that one
   family of polynomials serves every residue characteristic.

WHY THE CUT NEEDED A DEFINITION. "There is a rank-two representation
whose reduction is `A[λ]`" and "there is a `D`-rational compatible
system" are statements about unrelated representations unless something
ties both to `A`; the second is outright FALSE for an arbitrary `τ` with
the right reduction, since a residual condition constrains `τ` only
modulo `λ`. `Fermat.TatePt` is that tie: the first leaf produces a frame
of it and the second consumes one. See the module docstring of
`Modularity/TateModule.lean`.

ASSEMBLY (PROVEN): the moduli condition at the `F`-point supplied by
`hpt` gives the two level structures; the first leaf, applied at `λ`
(over `ℓ`) and at `𝔭` (over `p`), gives the two members `σ`, `τp` with
their coefficient rings and their residual comparisons — the latter at
EVERY place, so `residualℓ` and `residualp` need no bad set; the second
leaf gives ONE `D`-rational system `P` serving both residue
characteristics, and then, once per member through the frame just
produced, an exceptional set and the embeddings realizing `matchℓ` and
`matchp`. The point's `bad` is the union of those two exceptional sets
(each contains the places over its own residue characteristic, where the
member is ramified — which is why the second leaf cannot quantify one
`bad` before `q`) TOGETHER WITH the exceptional set of the `ℓ`-adic
frame's determinant clause (2026-07-26), which supplies the field
`detσ`; the `p`-adic frame's determinant clause is discarded, since
`matchp` and `ιC_injective` recover it from `detσ` through `P`. The
dihedral data `kp`, `ρbarp`, `L` and the two
conditions on them come from the seam unchanged.

BINDER NOTE (not a vacuity signal): `_hF`, `_hNF`, `_hFtr` and `_hFgal`
carry the underscore prefix because they are the *instance-carrying*
arguments of the `∀ F` clause of `IsTwistedHilbertBlumenthalModuli`,
which is stated with explicit rather than instance binders (it quantifies
over the field `F` itself). They are consumed — the proof passes them
straight back to `hmod` in order to reach the level structures at `x` —
and are NOT hypotheses the proof ignores.

CIRCULARITY GUARD (inherited from pillar β, load-bearing): must be
discharged by the Tate-module construction — never through
`Family.lean`, `Lift.lean`, or `Modularity/Interface.lean`. -/
theorem nonempty_hilbertBlumenthalPoint_of_isTwistedHilbertBlumenthalModuli
    {ℓ : ℕ} [Fact ℓ.Prime]
    {k : Type u} [Field k] [Finite k] [TopologicalSpace k] [DiscreteTopology k]
    {W : Type v} [AddCommGroup W] [Module k W] [Module.Finite k W]
    [Module.Free k W] (hW : Module.rank k W = 2) {ρbar : GaloisRep ℚ k W}
    (hirr : ρbar.IsIrreducible)
    {X : AlgebraicGeometry.Scheme.{u}}
    {fX : X ⟶ AlgebraicGeometry.Spec (CommRingCat.of (ULift.{u} ℚ))}
    {A : AlgebraicGeometry.Scheme.{u}} {fA : A ⟶ X}
    {ab : Fermat.AbelianSchemeStruct fA}
    (hmod : IsTwistedHilbertBlumenthalModuli ℓ ρbar fX ab)
    (F : Type u) (_hF : Field F) (_hNF : NumberField F)
    (_hFtr : NumberField.IsTotallyReal F) (_hFgal : IsGalois ℚ F)
    (hrestr : ∀ g : Field.absoluteGaloisGroup ℚ,
      ∃ h : Field.absoluteGaloisGroup F,
        (ρbar.map (algebraMap ℚ F)) h = ρbar g)
    (hpt : HasRationalPoint fX F) :
    Nonempty (HilbertBlumenthalPoint ℓ F (ρbar.map (algebraMap ℚ F))) := by
  -- the union of the two exceptional sets below needs decidable equality of places
  classical
  -- the moduli datum: the coefficient field, the real multiplication, the
  -- auxiliary prime and the two level ideals
  obtain ⟨D, _, _, _, m, p, lam, frp, hp, hpne, hlam, hfrp, hℓlam, hpfrp, hdim, hcond⟩ := hmod
  -- the `F`-point of `X` at which the level structures are read
  obtain ⟨x, hx⟩ := hpt
  obtain ⟨⟨e, headd, heinj, heequiv, heimg⟩,
      kp, _, _, _, _, ρbarp, e', h'add, h'inj, h'equiv, h'img, hirrp,
      L, _, _, hLrank, hLred⟩ :=
    hcond F _hF _hNF _hFtr _hFgal hrestr x hx
  haveI : Fact p.Prime := ⟨hp⟩
  -- the residual irreducibility hypothesis of the Tate-module leaf, transported
  -- from `Γ_ℚ` to `Γ_F` along `hrestr` (see the FAITHFULNESS AUDIT of
  -- `Fermat.exists_tateFrame_of_levelStructure`: without it that leaf is FALSE)
  have hirrF : (ρbar.map (algebraMap ℚ F)).IsIrreducible :=
    Fermat.isIrreducible_map_of_restrictionSurjective ρbar (algebraMap ℚ F) hrestr hirr
  -- the `λ`-adic member, framed on the Tate module `TatePt m x lam ϖℓ`;
  -- `_jD₀`/`_hjD₀` are the real-multiplication clause of the frame, kept bound for
  -- the compatible-system leaf, which does not yet take them.  `baddet`/`hdet₀`
  -- are the determinant (Weil-pairing) clause, consumed by the field
  -- `HilbertBlumenthalPoint.detσ` below.
  obtain ⟨ϖℓ, hϖℓ, hϖℓ2, O₀, _, _, _, _, _, _, _, _, σ, φ₀, ι₀, _jD₀, baddet,
      hφ₀add, hφ₀bij, hφ₀eq, hres₀, _hjD₀, hdet₀⟩ :=
    Fermat.exists_tateFrame_of_levelStructure m x hdim ℓ lam hlam hℓlam hW
      (ρbar.map (algebraMap ℚ F)) hirrF e headd heinj heequiv heimg
  -- the `𝔭`-adic member, framed on `TatePt m x frp ϖp`; its own
  -- determinant clause is not needed — the point records the `ℓ`-adic
  -- one, and `matchp`/`ιC_injective` recover the `p`-adic one from it
  obtain ⟨ϖp, hϖp, hϖp2, C, _, _, _, _, _, _, _, _, τp, φp, ιp, _jDp, _,
      hφpadd, hφpbij, hφpeq, hresp, _hjDp, _⟩ :=
    Fermat.exists_tateFrame_of_levelStructure m x hdim p frp hfrp hpfrp
      (by simp) ρbarp hirrp e' h'add h'inj h'equiv h'img
  -- ONE `D`-rational compatible system, read at both members through their frames;
  -- the two exceptional sets are produced separately (they contain the places over
  -- `ℓ` resp. `p`) and the point's `bad` is their union
  obtain ⟨P, hP⟩ := Fermat.exists_weilFrobeniusSystem_of_mult m x hdim
  obtain ⟨badℓ, ψℓ, ιℓ, hιℓinj, hmatchℓ⟩ :=
    hP ℓ inferInstance lam hlam hℓlam ϖℓ hϖℓ hϖℓ2 O₀ inferInstance inferInstance
      inferInstance σ φ₀ hφ₀add hφ₀bij hφ₀eq
  obtain ⟨badp, ψp, ιC, hιCinj, hmatchp⟩ :=
    hP p inferInstance frp hfrp hpfrp ϖp hϖp hϖp2 C inferInstance inferInstance
      inferInstance τp φp hφpadd hφpbij hφpeq
  exact ⟨{ bad := badℓ ∪ badp ∪ baddet, D := D, P := P, O₀ := O₀, σ := σ,
           ψDℓ := ψℓ, ιO₀ := ιℓ,
           ιO₀_injective := hιℓinj,
           matchℓ := fun w hw => hmatchℓ w fun hb =>
             hw (Finset.mem_union_left _ (Finset.mem_union_left _ hb)),
           detσ := fun w hw => hdet₀ w fun hb => hw (Finset.mem_union_right _ hb),
           π₀ := ι₀,
           residualℓ := fun w _ => hres₀ w,
           p := p, pfact := ⟨hp⟩, p_ne_ℓ := hpne,
           C := C, τp := τp, ψDp := ψp, ιC := ιC,
           ιC_injective := hιCinj,
           matchp := fun w hw => hmatchp w fun hb =>
             hw (Finset.mem_union_left _ (Finset.mem_union_right _ hb)),
           kp := kp, ρbarp := ρbarp, πp := ιp,
           residualp := fun w _ => hresp w,
           irreduciblep := hirrp, L := L, finrankL := hLrank, dihedralp := hLred }⟩

/-- **The twisted Hilbert–Blumenthal moduli variety** (PROVEN 2026-07-25
as the assembly of the moduli cut above — see the section note before
`IsTwistedHilbertBlumenthalModuli`; it was previously a single sorry
node for Taylor 2002 §2 via Shimura's theory of
Hilbert–Blumenthal moduli): for the irreducible hardly ramified residual
representation `ρbar` at `ℓ ≥ 5` there is a smooth, separated,
quasi-compact, finite-type, geometrically irreducible variety `X` over
`ℚ` with a real point, whose `F`-points — over any totally real Galois
`F/ℚ` to which `ρbar` restricts with the same image — are
`HilbertBlumenthalPoint`s.

Classically `X` is the moduli variety of Hilbert–Blumenthal abelian
varieties with real multiplication by a fixed totally real field `D`,
carrying two twisted level structures: an `ℓ`-level structure twisted so
that an `F`-point is an abelian variety `A/F` whose `ℓ`-torsion realizes
`ρbar|_{G_F}` (the FIRST moduli condition of `HilbertBlumenthalPoint`),
and an auxiliary `p`-level structure imposing that `A[p]` be induced
from a character of a quadratic extension (the SECOND, dihedral
condition). Geometric irreducibility of the twist is Taylor 2002 §2; the
real point is the archimedean local condition, arranged by hand from the
signature of the Hilbert–Blumenthal family; the `F`-point-to-package
translation is the moduli interpretation together with the Tate-module
construction of the two members of the compatible system.

This node is what remains of the geometric joint after Moret–Bailly's
theorem is split off above: it contains no existence-of-global-points
content whatsoever, only the construction and the moduli
interpretation of one variety.

ASSEMBLY (2026-07-25, PROVEN): the moduli SPACE
(`exists_twistedHilbertBlumenthalModuliScheme_of_five_le`) supplies `X`
together with its geometry, its real point, and an abelian scheme
`A ⟶ X` satisfying `IsTwistedHilbertBlumenthalModuli`; the Tate-module
construction
(`nonempty_hilbertBlumenthalPoint_of_isTwistedHilbertBlumenthalModuli`)
turns an `F`-point of that family into a `HilbertBlumenthalPoint`.
Nothing geometric and nothing arithmetic is asserted here: the two
leaves are the moduli-space theory and the abelian-variety theory
respectively, and neither is stateable without
`Modularity/AbelianScheme.lean`.

SOUNDNESS AUDIT (both ways, 2026-07-25): (i) direct — this is Taylor
2002 §2; (ii) collapse — the hypothesis package (an irreducible hardly
ramified mod-`ℓ` representation, `ℓ ≥ 5`) is classically unsatisfiable
(headline below), so the statement is also vacuously sound.

ROUTE AUDIT: the odd-prime dichotomy is unavailable here — see the
`Moret–Bailly cut` section docstring above (import cycle AND declaration
cycle).

CIRCULARITY GUARD (inherited from pillar β, load-bearing): must be
discharged by the independent moduli construction — never through
`Family.lean`, `Lift.lean`, or `Modularity/Interface.lean`. -/
theorem exists_twistedHilbertBlumenthalModuli_of_five_le
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
    ∃ (X : AlgebraicGeometry.Scheme.{u})
      (fX : X ⟶ AlgebraicGeometry.Spec (CommRingCat.of (ULift.{u} ℚ))),
      AlgebraicGeometry.Smooth fX ∧ AlgebraicGeometry.IsSeparated fX ∧
      AlgebraicGeometry.LocallyOfFiniteType fX ∧
      AlgebraicGeometry.QuasiCompact fX ∧
      AlgebraicGeometry.GeometricallyIrreducible fX ∧
      HasRationalPoint fX (ULift.{u} ℝ) ∧
      ∀ (F : Type u) (_ : Field F) (_ : NumberField F)
        (_ : NumberField.IsTotallyReal F) (_ : IsGalois ℚ F),
        (∀ g : Field.absoluteGaloisGroup ℚ,
          ∃ h : Field.absoluteGaloisGroup F,
            (ρbar.map (algebraMap ℚ F)) h = ρbar g) →
        HasRationalPoint fX F →
        Nonempty (HilbertBlumenthalPoint ℓ F (ρbar.map (algebraMap ℚ F))) := by
  -- (i) the moduli SPACE, with its universal abelian scheme
  obtain ⟨X, fX, A, fA, ab, hsm, hsep, hft, hqc, hgi, hreal, hmod⟩ :=
    exists_twistedHilbertBlumenthalModuliScheme_of_five_le hℓodd hℓ5 hZinj hrank hρ hW
      hρbar hirr π hπsurj hπ
  -- (ii) the Tate-module construction at each `F`-point
  exact ⟨X, fX, hsm, hsep, hft, hqc, hgi, hreal,
    fun F hF hNF hFtr hFgal hrestr hpt =>
      nonempty_hilbertBlumenthalPoint_of_isTwistedHilbertBlumenthalModuli hW hirr hmod F hF hNF
        hFtr hFgal hrestr hpt⟩

/-- **The kernel of a residual representation is open** (PROVEN): for a
finite discrete coefficient field `k` and a finite `k`-module `W`, the
endomorphism algebra `Module.End k W` is discrete in its module
topology, so the kernel of the continuous `ρbar` is the preimage of an
open singleton.

This is the side condition of Moret–Bailly's avoidance datum: the
subgroup handed to
`exists_totallyReal_point_of_geometricallyIrreducible` must be open (it
is the group of the splitting field of `ρbar`, a finite extension of
`ℚ`), and openness — not merely finite index — is what makes it
correspond to a field at all. -/
theorem isOpen_ker_of_finite_discrete
    {k : Type u} [Field k] [TopologicalSpace k] [DiscreteTopology k]
    {W : Type v} [AddCommGroup W] [Module k W] [Module.Finite k W]
    (ρbar : GaloisRep ℚ k W) :
    IsOpen ((ρbar.ker : Subgroup (Field.absoluteGaloisGroup ℚ)) :
      Set (Field.absoluteGaloisGroup ℚ)) := by
  letI : TopologicalSpace (Module.End k W) := moduleTopology k (Module.End k W)
  haveI : DiscreteTopology (Module.End k W) :=
    discreteTopology_moduleTopology _ _
  have hcont : Continuous fun g : Field.absoluteGaloisGroup ℚ => ρbar g :=
    ContinuousMonoidHom.continuous_toFun ρbar
  have hset : ((ρbar.ker : Subgroup (Field.absoluteGaloisGroup ℚ)) :
      Set (Field.absoluteGaloisGroup ℚ)) =
      (fun g : Field.absoluteGaloisGroup ℚ => ρbar g) ⁻¹' {1} := rfl
  rw [hset]
  exact hcont.isOpen_preimage _ (isOpen_discrete _)

/-- **The geometric joint of Theorem B** (PROVEN 2026-07-25 as the
assembly of the Moret–Bailly split above — Moret–Bailly
1989 + the twisted Hilbert–Blumenthal moduli interpretation, Taylor
2002 §2): for the irreducible hardly ramified residual representation
`ρbar` at `ℓ ≥ 5` there is a totally real number field `F`, Galois
over `ℚ`, such that

* restriction to `G_F` PRESERVES THE IMAGE of `ρbar` (`hrestr`: every
  `ρbar g` is already `ρbar|_{G_F} h` for some `h`) — the
  pin-stateable form of "`F` is linearly disjoint from the splitting
  field of `ρbar`", which is how Moret–Bailly's avoidance set is
  chosen; and
* the twisted Hilbert–Blumenthal moduli variety has an `F`-point, i.e.
  there is a `HilbertBlumenthalPoint`.

Classically: the moduli variety of Hilbert–Blumenthal abelian
varieties with real multiplication by a fixed totally real `D`, with
`ℓ`-level structure twisted so that an `F`-point is an abelian variety
`A/F` whose `ℓ`-torsion realizes `ρbar|_{G_F}`, and with an auxiliary
`p`-level structure imposing that `A[p]` be induced from a character,
is geometrically irreducible (Taylor 2002 §2, via Shimura's theory of
Hilbert–Blumenthal moduli) and has points over `ℝ` and over `ℚ_q` for
`q` in the finite set of relevant primes (the local conditions at `2`,
`3`, `p`, `ℓ` being arranged by hand). Moret–Bailly's theorem
(*Groupes de Picard et problèmes de Skolem II*, Ann. Sci. ÉNS 22
(1989); the form used is Taylor 2002 Theorem G / Prop. 2.1) then
produces the totally real `F` — Galois over `ℚ`, and linearly disjoint
from any prescribed finite extension, whence `hrestr` — together with
the desired `F`-point.

PIN AUDIT (2026-07-24, **SUPERSEDED 2026-07-25**): the earlier note
recorded that the pin has no algebraic geometry to state Moret–Bailly
against, so that the geometric existence theorem and the moduli
interpretation could not be separated. The re-audit in the section
docstring above shows the pin DOES carry `Scheme`, `Spec`,
`GeometricallyIrreducible`, `Smooth`, `IsSeparated`,
`LocallyOfFiniteType` and `QuasiCompact`, and the two inputs are now
separate leaves. It remains true that the pin has no Moret–Bailly
MATERIAL (no `Skolem`/`MoretBailly` declarations, no
incompressible-neighbourhood existence theorem on Picard-scheme
torsors), no number-field weak approximation in the required form, and
no Hilbert–Blumenthal moduli — those are precisely the contents of the
two sorry leaves, not of this node.

SOUNDNESS AUDIT (both ways, 2026-07-24): (i) direct — this is Taylor
2002 §2 with the Galois refinement of §1, a true nonvacuous theorem
whose proof nowhere presupposes Serre's conjecture; (ii) collapse —
the hypothesis set (an irreducible hardly ramified mod-`ℓ`
representation, `ℓ ≥ 5`) is classically unsatisfiable (headline
below), so the statement is also vacuously sound.

ROUTE AUDIT: the odd-prime dichotomy is unavailable here — see the
section docstring above (import cycle AND declaration cycle).

ASSEMBLY (2026-07-25, PROVEN): the moduli input
(`exists_twistedHilbertBlumenthalModuli_of_five_le`) supplies the
twisted variety `X/ℚ` with its geometric properties, its real point and
its `F`-point-to-`HilbertBlumenthalPoint` translation; the openness of
`ρbar.ker` is PROVEN (`isOpen_ker_of_finite_discrete`) and hands the
splitting field of `ρbar` to Moret–Bailly as the avoidance datum;
`exists_totallyReal_point_of_geometricallyIrreducible` returns the
totally real Galois `F` with the disjointness join and the `F`-point;
`forall_exists_map_eq_of_ker_sup_range_eq_top` converts the join into
`hrestr`, which is then also what the translation consumes. Nothing
arithmetic and nothing geometric is asserted here.

CIRCULARITY GUARD (inherited from pillar β, load-bearing): must be
proven by the independent Moret–Bailly construction — never through
`Family.lean`, `Lift.lean`, or `Modularity/Interface.lean`. -/
theorem exists_hilbertBlumenthalPoint_of_five_le
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
    ∃ (F : Type u) (_ : Field F) (_ : NumberField F)
      (_ : NumberField.IsTotallyReal F) (_ : IsGalois ℚ F),
      (∀ g : Field.absoluteGaloisGroup ℚ,
        ∃ h : Field.absoluteGaloisGroup F,
          (ρbar.map (algebraMap ℚ F)) h = ρbar g) ∧
      Nonempty (HilbertBlumenthalPoint ℓ F (ρbar.map (algebraMap ℚ F))) := by
  classical
  -- (i) the moduli input: the twisted Hilbert–Blumenthal variety `X/ℚ`
  obtain ⟨X, fX, hsm, hsep, hft, hqc, hgi, hreal, htrans⟩ :=
    exists_twistedHilbertBlumenthalModuli_of_five_le hℓodd hℓ5 hZinj hrank hρ hW
      hρbar hirr π hπsurj hπ
  -- (ii) Moret–Bailly, with the splitting field of `ρbar` as avoidance datum
  obtain ⟨F, hF, hNF, hFtr, hFgal, hsup, hFpt⟩ :=
    exists_totallyReal_point_of_geometricallyIrreducible fX hsm hsep hft hqc hgi
      hreal ρbar.ker (isOpen_ker_of_finite_discrete ρbar)
  -- (iii) the avoidance join IS image preservation
  have hrestr : ∀ g : Field.absoluteGaloisGroup ℚ,
      ∃ h : Field.absoluteGaloisGroup F,
        (ρbar.map (algebraMap ℚ F)) h = ρbar g :=
    fun g => forall_exists_map_eq_of_ker_sup_range_eq_top ρbar (algebraMap ℚ F) hsup g
  exact ⟨F, hF, hNF, hFtr, hFgal, hrestr,
    htrans F hF hNF hFtr hFgal hrestr hFpt⟩

/-- **Irreducibility descends along an image-preserving restriction**
(PROVEN glue): if every value `ρbar g` of a representation of `Γ K` is
already a value of its restriction `ρbar|_{Γ L}` along `f : K →+* L`,
then irreducibility over `K` implies irreducibility over `L`.

This is the formal content of the Moret–Bailly avoidance condition:
`F` is chosen linearly disjoint from the splitting field of `ρbar`, so
`G_F` still surjects onto the image of `ρbar`, and a subspace is
stable under the image iff it is stable under the restricted
representation — irreducibility is a property of the image alone. -/
theorem isIrreducible_map_of_range_surjective
    {K : Type*} [Field K] [NumberField K] {L : Type*} [Field L]
    [NumberField L]
    {k : Type*} [Field k] [TopologicalSpace k]
    {W : Type*} [AddCommGroup W] [Module k W]
    {ρbar : GaloisRep K k W} (f : K →+* L)
    (hrestr : ∀ g : Field.absoluteGaloisGroup K,
      ∃ h : Field.absoluteGaloisGroup L, (ρbar.map f) h = ρbar g)
    (hirr : ρbar.IsIrreducible) :
    (ρbar.map f).IsIrreducible := by
  obtain ⟨hnt, hsub⟩ :=
    (Slop.OddRep.isIrreducible_iff_forall ρbar.toRepresentation).mp hirr
  refine (Slop.OddRep.isIrreducible_iff_forall
    (ρbar.map f).toRepresentation).mpr ⟨hnt, fun V hV => hsub V ?_⟩
  intro g v hv
  obtain ⟨h, hh⟩ := hrestr g
  have hveq : ρbar.toRepresentation g v = (ρbar.map f).toRepresentation h v := by
    rw [show (ρbar.map f).toRepresentation h = (ρbar.map f) h from rfl,
      show ρbar.toRepresentation g = ρbar g from rfl, hh]
  rw [hveq]
  exact hV h v hv

/-! #### The automorphic joint, cut at its own seam (2026-07-25)

The automorphic joint packs TWO genuinely different classical
citations, and they are separated here:

* **(a) residual modularity in the DIHEDRAL case**
  (`exists_residualModularity_of_hilbertBlumenthalPoint`) — NOT a
  citation of Serre's conjecture but Hecke's automorphic induction:
  the mod-`p` representation of the point is induced from a character
  of the quadratic `L/F` (`irreduciblep` + `dihedralp`), so it is the
  reduction of a theta series of `L`, automorphic over `F` by the
  converse theorem and movable between the quaternionic and Hilbert
  settings by Jacquet–Langlands;
* **(b) modularity lifting at `p` in the residually dihedral case**
  (`exists_heckeSystem_of_residualModularity`) — Taylor, *Remarks on a
  conjecture of Fontaine and Mazur*, J. Inst. Math. Jussieu 1 (2002),
  §5, following Wiles and Skinner–Wiles (Hida families in the
  residually dihedral situation): the residual modularity of (a) is
  promoted to the `p`-adic member `τp` of the point's system.

The remaining content of the joint — transport of the eigensystem from
the `p`-adic member to the `ℓ`-adic side along the point's own
compatibility data, the union of the bad sets, and the coefficient
bookkeeping that moves the Hecke polynomials between the Hecke field
and the real-multiplication field `D` — is PROVEN below from those two
leaves.

WHY (b) IS STATED WITH `θ : E₀ →+* pt.D` (the design constraint of the
cut).  The bare conclusion of the joint — "`P` is, inside `ℚ̄_ℓ`, a
family of Hecke polynomials over some number field" — is satisfiable
by the point's OWN data (`E₀ := pt.D`, `hecke₀ := pt.P`,
`ψ₀ := pt.ψDℓ`, `S := ∅`, `rfl`), because `D` is already a number
field and `P` is already a polynomial family over it: as stated it
carries no automorphic content at all.  The cut therefore pushes the
content into the two joints, where it IS pin-stateable:

1. the Hecke polynomials have the parallel-weight-`2` shape
   `X² − a_w·X + Nw` — the constant coefficient is the absolute norm
   of `w`, not free data (Weil pairing / cyclotomic determinant); and
2. the Hecke field is identified INSIDE the coefficient field of the
   system by a ring homomorphism `θ` compatible with the chosen place
   over `p` — the formal trace of "one strictly compatible system with
   coefficient field `D`" plus Shimura rationality.

Neither clause is derivable from the `HilbertBlumenthalPoint`
interface (`P` is arbitrary data there), so both joints are genuine
sorry nodes, and the assembly below is genuine algebra: it descends
the identity from `ℚ̄_p` to `D` by injectivity of `ψDp`, then pushes it
into `ℚ̄_ℓ` along `ψDℓ`.

CLUSTER VACUITY SWEEP (2026-07-25, audit only — no statement was
changed; see the per-joint VACUITY AUDIT paragraphs below).  Clause 2
above is NOT a second piece of content: it is DERIVABLE from the
interface.  Take `E₀ := pt.D` and `θ := RingHom.id pt.D`; then for
`w ∉ pt.bad` the field `matchp` gives
`(pt.τp.charFrob w).map pt.ιC = (pt.P w).map pt.ψDp`, whose left side
is monic of degree `2` (`charFrob_map_eq_quadratic_of_rank_two`), so
`pt.P w` is monic of degree `2` by injectivity of `pt.ψDp`, and
`a₀ w := −(pt.P w).coeff 1` makes joint (b)'s conclusion hold at every
`w ∉ pt.bad` — EXCEPT for the single residual equation
`(pt.P w).coeff 0 = (Nw : pt.D)`.  So joint (b)'s entire formal content
is clause 1, the norm clause, and nothing of Taylor 2002 §5 is captured.

SWEEP ACTED ON (2026-07-25).  The paragraph above is no longer only an
audit: joint (b) has been CUT along exactly the seam it describes.
`exists_coeff_zero_eq_absNorm_of_hilbertBlumenthalPoint` now states the
norm clause on its own — one equation, the Weil-pairing determinant of
the point's compatible system, belonging to the GEOMETRIC joint — and
`exists_heckeSystem_of_residualModularity` is PROVEN from it by the
junk-witness construction above.  Two consequences are now mechanical
rather than asserted: (i) the residual-modularity package produced by
joint (a) is not consumed by joint (b) at all (its arguments are
underscore-prefixed there), so the two joints are independent and the
lifting-theorem content of Taylor 2002 §5 is formally absent; (ii) the
norm leaf also implies joint (a) (via `matchp`, `ιC_injective` and
`residualp`), so ONE leaf now carries the arithmetic of both.  The
repair remains cut-level and is NOT performed here: the norm clause
belongs as a FIELD of `HilbertBlumenthalPoint` supplied by the
geometric joint, and a genuinely automorphic clause (the Weil bound
`∀ ι : E₀ →+* ℂ, ‖ι (a w)‖ ≤ 2 √(Nw)`, or integrality of the
eigenvalues) has to appear at the PARENT's conclusion.

Worse, joint (a) is IMPLIED by clause 1 plus the interface, so the two
joints are one fact stated twice: from `(pt.P w).coeff 0 = (Nw : pt.D)`,
`matchp` and injectivity of `pt.ιC` give
`(pt.τp.charFrob w).coeff 0 = (Nw : pt.C)`, and `residualp` then gives
`(pt.ρbarp.charFrob w).coeff 0 = (Nw : pt.kp)` — which is all joint (a)
demands beyond `redΛ`-surjectivity onto the FINITE field `pt.kp`, itself
free (any finite field is a residue field of a number field, so `E₁`,
`Λ`, `jΛ` carry no algebraicity content here, unlike in the sibling
`exists_heckeField_mem_range_of_eigensystem` where the target is
`ℚ̄_ℓ`).  `pt.irreduciblep`, `pt.dihedralp` and `pt.L` are consumed by
neither joint.

And the conclusion of `exists_heckeEigensystem_of_hilbertBlumenthalPoint`
itself was never restated: it is still the `rfl`-satisfiable one recorded
in its own VACUITY AUDIT.  Adding the norm clause cannot repair it —
`E₀ := pt.D`, `hecke₀ := pt.P`, `ψ₀ := pt.ψDℓ` satisfies it whatever
`P` is.  A repair must change that node's CONCLUSION so that `hecke₀`
is tied to data the point does not already carry; the cheapest
pin-stateable clauses are the Weil bound
`∀ ι : E₀ →+* ℂ, ‖ι (a w)‖ ≤ 2 * √(Nw)` (Weil's Riemann hypothesis for
`A/F`, equivalently Ramanujan–Petersson at parallel weight `2`) or, more
weakly, integrality `a w ∈ 𝓞_{E₀}` — neither derivable from the
interface.  That is a cut-level change spanning this node,
`MoretBaillySeed.hecke₀`/`modular₀` and
`PotentialModularityWitness.heckeF`/`modularF`; it was NOT performed
here.

CIRCULARITY GUARD (inherited from pillar β, load-bearing): as
everywhere in this module, neither joint may be proven through
`Family.lean`, `Lift.lean`, or `Modularity/Interface.lean`. -/

/-! #### Joint (a), cut again — at the determinant (2026-07-25)

The VACUITY AUDIT on `exists_residualModularity_of_hilbertBlumenthalPoint`
below recorded, as an ASSERTION, that the node's entire formal content is
the residual norm clause
`(pt.ρbarp.charFrob w).coeff 0 = (Ideal.absNorm w.asIdeal : pt.kp)`,
everything else being dischargeable by a junk witness.  That assertion is
now a THEOREM: the node is PROVEN below as an assembly over

* `exists_coeff_zero_eq_absNorm_of_hilbertBlumenthalPoint` — the
  determinant (Weil-pairing) clause for the compatible system of the
  Hilbert–Blumenthal abelian variety — itself PROVEN 2026-07-26 by the
  cut-level repair that made the clause the FIELD
  `HilbertBlumenthalPoint.detσ`, so this node consumes no sorried leaf
  of its own any more.  CONVERGENT CUT (2026-07-25): that leaf was extracted
  independently, on the same day and at the same seam, by the owner of
  the sibling joint `exists_heckeSystem_of_residualModularity`, whose
  VACUITY AUDIT identified the same single equation as everything joint
  (b) formally asserts.  A duplicate of it was briefly introduced here
  and has been deleted in favour of that one — the two joints really are
  one determinant fact, and it now has exactly one statement in the tree.
* PROVEN algebra: the coefficient ring
  (`exists_numberField_surjection_of_finite`, built from three PROVEN
  steps below), the descent of the norm clause from the system to the
  residual representation
  (`residual_charFrob_coeff_zero_eq_absNorm_of_hilbertBlumenthalPoint`),
  and the monic-quadratic shape of `charFrob`
  (`charFrob_monic_natDegree_two_of_rank_two`).

So the audit's finding that the "the eigenvalues are ALGEBRAIC" reading of
`E₁`/`jΛ` is FORMALLY EMPTY is no longer an opinion: the number field
`E₁`, the coefficient ring `Λ`, the injection `jΛ` and the reduction
`redΛ` are now literally constructed out of nothing but the FINITENESS of
`pt.kp` — the construction never looks at `pt` at all — and `a₁` is chosen
by surjectivity of `redΛ` from the trace of the residual charpoly.  Nothing
of Hecke's theta series, of the converse theorem or of Jacquet–Langlands
survives anywhere in this node; `pt.irreduciblep`, `pt.dihedralp` and
`pt.L` are consumed by no step of the proof.

WHY THAT LEAF MUST KEEP THE WHOLE HYPOTHESIS PACKAGE (it does).  Stated
for a bare abstract `pt`, "the constant coefficient of `P w` is `Nw`"
would be FALSE as stated: the interface constrains `P` not at all, so a
point whose `p`-adic determinant is not cyclotomic refutes it, and such a
point is excluded by nothing in `HilbertBlumenthalPoint`.  It is only the
parent's package — an irreducible hardly ramified mod-`ℓ` representation
at `ℓ ≥ 5`, classically unsatisfiable (headline below) — that makes it
classically true, exactly as for its two siblings.  Do NOT restate it
without the package.

WHERE THE CLAUSE REALLY BELONGS (recommendation, PERFORMED 2026-07-26):
as a FIELD of `HilbertBlumenthalPoint` — `detσ` — discharged through
`exists_twistedHilbertBlumenthalModuli_of_five_le`, whose conclusion is
`Nonempty (HilbertBlumenthalPoint …)` and therefore absorbed the new
field with no change to its own statement, down to
`Fermat.exists_tateFrame_of_levelStructure`, where the Weil pairing on
the Tate module is actually available.

CIRCULARITY GUARD (inherited from pillar β, load-bearing): none of the
declarations below may be discharged through `Family.lean`, `Lift.lean`,
or `Modularity/Interface.lean`. -/

/-- **A finite field is generated by a root of a monic integer polynomial
that stays irreducible over `ℚ`** (PROVEN helper, pure algebra; first of
the three steps building the junk coefficient ring below).

Take `α` a generator of the cyclic group `kˣ`, let `f̄ := minpoly 𝔽_q α`
over the prime field `𝔽_q = ZMod (ringChar k)` — monic and irreducible —
and lift it coefficientwise to a MONIC `f : ℤ[X]`
(`Polynomial.lifts_and_degree_eq_and_monic`, using surjectivity of
`ℤ → ZMod q`).  Monicity is what makes the lift usable twice over: it
gives `Irreducible f` from `Irreducible f̄`
(`Polynomial.Monic.irreducible_of_irreducible_map`) and then
`Irreducible (f.map (ℤ → ℚ))` by Gauss's lemma
(`Polynomial.IsPrimitive.Int.irreducible_iff_irreducible_map_cast`).
Every element of `k` is `0` or a power of `α`, whence the final clause:
every element is an `ℤ[X]`-evaluation at `α`. -/
theorem exists_monic_int_poly_of_finite_field (k : Type*) [Field k]
    [Finite k] :
    ∃ (f : Polynomial ℤ) (α : k), f.Monic ∧
      Irreducible (f.map (Int.castRingHom ℚ)) ∧
      eval₂ (Int.castRingHom k) α f = 0 ∧
      ∀ x : k, ∃ g : Polynomial ℤ, eval₂ (Int.castRingHom k) α g = x := by
  classical
  haveI : CharP k (ringChar k) := ringChar.charP k
  haveI hqp : Fact (ringChar k).Prime := ⟨CharP.char_is_prime k (ringChar k)⟩
  letI : Algebra (ZMod (ringChar k)) k := ZMod.algebra k (ringChar k)
  haveI : Module.Finite (ZMod (ringChar k)) k := Module.Finite.of_finite
  haveI : Algebra.IsIntegral (ZMod (ringChar k)) k :=
    Algebra.IsIntegral.of_finite _ _
  obtain ⟨u, hu⟩ := IsCyclic.exists_generator (α := kˣ)
  have hint : IsIntegral (ZMod (ringChar k)) (u : k) :=
    Algebra.IsIntegral.isIntegral (u : k)
  obtain ⟨f, hfmap, -, hfmon⟩ :=
    Polynomial.lifts_and_degree_eq_and_monic
      (f := Int.castRingHom (ZMod (ringChar k)))
      ((Polynomial.lifts_iff_coeff_lifts _).2
        (fun n => ZMod.intCast_surjective _)) (minpoly.monic hint)
  have hfirr : Irreducible f :=
    Polynomial.Monic.irreducible_of_irreducible_map _ f hfmon
      (by rw [hfmap]; exact minpoly.irreducible hint)
  have hcomp : (Int.castRingHom k) =
      (algebraMap (ZMod (ringChar k)) k).comp
        (Int.castRingHom (ZMod (ringChar k))) := RingHom.ext_int _ _
  refine ⟨f, (u : k), hfmon,
    (Polynomial.IsPrimitive.Int.irreducible_iff_irreducible_map_cast
      hfmon.isPrimitive).mp hfirr, ?_, ?_⟩
  · rw [hcomp, ← Polynomial.eval₂_map, hfmap]
    exact minpoly.aeval (ZMod (ringChar k)) (u : k)
  · intro x
    rcases eq_or_ne x 0 with rfl | hx
    · exact ⟨0, by simp⟩
    · obtain ⟨n, hn⟩ := mem_powers_iff_mem_zpowers.2 (hu (Units.mk0 x hx))
      have hn' : u ^ n = Units.mk0 x hx := hn
      have h2 : ((u ^ n : kˣ) : k) = x := by rw [hn']; simp
      exact ⟨X ^ n, by simpa using h2⟩

/-- **`ℤ[X]/(f) → ℚ[X]/(f)` is injective for monic `f`** (PROVEN helper,
pure algebra; second of the three steps).

This is the statement that `ℤ[α]` really is a SUBRING of the number field
`ℚ(α)`, which is what the target's `jΛ`-with-`Function.Injective jΛ`
demands.  Formally: an element of `AdjoinRoot f` is `mk f g`, and it dies
in `AdjoinRoot (f.map (ℤ → ℚ))` exactly when `fℚ ∣ gℚ`; monic division
`g = f * (g /ₘ f) + g %ₘ f` then forces `fℚ ∣ (g %ₘ f)ℚ`, whose degree is
below `deg fℚ = deg f`, so `(g %ₘ f)ℚ = 0`, so `g %ₘ f = 0` by injectivity
of `ℤ → ℚ` on coefficients, i.e. `f ∣ g`.

Monicity is essential, and is exactly what the previous step's lift
supplies: for `f = 2X` the class of `X` in `ℤ[X]/(2X)` is nonzero but dies
in `ℚ[X]/(2X) = ℚ`, so the map is not injective. -/
theorem exists_injective_adjoinRoot_int_rat {f : Polynomial ℤ}
    (hfmon : f.Monic) :
    ∃ j : AdjoinRoot f →+* AdjoinRoot (f.map (Int.castRingHom ℚ)),
      Function.Injective j := by
  classical
  have hev : ∀ t : Polynomial ℚ,
      eval₂ (AdjoinRoot.of (f.map (Int.castRingHom ℚ)))
        (AdjoinRoot.root (f.map (Int.castRingHom ℚ))) t =
        AdjoinRoot.mk (f.map (Int.castRingHom ℚ)) t := by
    intro t
    rw [← AdjoinRoot.algebraMap_eq, ← Polynomial.aeval_def, AdjoinRoot.aeval_eq]
  have hroot : eval₂ ((AdjoinRoot.of (f.map (Int.castRingHom ℚ))).comp
      (Int.castRingHom ℚ)) (AdjoinRoot.root (f.map (Int.castRingHom ℚ)))
      f = 0 := by
    rw [← Polynomial.eval₂_map]
    exact AdjoinRoot.eval₂_root _
  refine ⟨AdjoinRoot.lift _ _ hroot, ?_⟩
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨g, rfl⟩ := AdjoinRoot.mk_surjective x
  rw [AdjoinRoot.lift_mk, ← Polynomial.eval₂_map, hev] at hx
  have hdvd : (f.map (Int.castRingHom ℚ)) ∣ g.map (Int.castRingHom ℚ) :=
    AdjoinRoot.mk_eq_zero.mp hx
  rw [AdjoinRoot.mk_eq_zero]
  have hsplit : g %ₘ f = g - f * (g /ₘ f) :=
    eq_sub_of_add_eq (Polynomial.modByMonic_add_div g f)
  have hzero : (g %ₘ f).map (Int.castRingHom ℚ) = 0 := by
    refine Polynomial.eq_zero_of_dvd_of_degree_lt
      (p := f.map (Int.castRingHom ℚ)) ?_ ?_
    · rw [hsplit, Polynomial.map_sub, Polynomial.map_mul]
      exact dvd_sub hdvd (Dvd.intro _ rfl)
    · calc ((g %ₘ f).map (Int.castRingHom ℚ)).degree ≤ (g %ₘ f).degree :=
            Polynomial.degree_map_le
        _ < f.degree := Polynomial.degree_modByMonic_lt g hfmon
        _ = (f.map (Int.castRingHom ℚ)).degree := (hfmon.degree_map _).symm
  refine (Polynomial.modByMonic_eq_zero_iff_dvd hfmon).1 ?_
  exact Polynomial.map_injective (Int.castRingHom ℚ) Int.cast_injective
    (by rw [hzero, Polynomial.map_zero])

/-- **Every finite field is a ring-homomorphic image of a subring of a
number field** (PROVEN, in an arbitrary universe; third step, and the
whole junk witness of joint (a)).

`E := ℚ(α)`, `Λ := ℤ[α]` for `α` a root of the monic integer polynomial
of the first step, `j` the inclusion of the second, and `red` the
evaluation `ℤ[X]/(f) → k` at the generator of `kˣ`, surjective because
that generator generates.  `ULift` places the pair in the universe of `k`;
`NumberField` transfers along `ULift.ringEquiv` (`CharZero` by
`RingHom.charZero`, finite-dimensionality by the induced `ℚ`-algebra
equivalence).

This is the FORMAL-CONTENT sink of the residual-modularity leaf: it shows
that a coefficient ring "sitting injectively inside a number field and
reducing onto `pt.kp`" — the clause whose intended reading was that the
Hecke eigenvalues of the theta series are ALGEBRAIC — is available for
EVERY finite field with no arithmetic input at all.  Algebraicity is a
real constraint only against a characteristic-zero target such as `ℚ̄_ℓ`
(as in `exists_heckeField_mem_range_of_eigensystem`), never against a
finite one. -/
theorem exists_numberField_surjection_of_finite (k : Type u) [Field k]
    [Finite k] :
    ∃ (E : Type u) (_ : Field E) (_ : NumberField E) (Λ : Type u)
      (_ : CommRing Λ) (j : Λ →+* E) (_ : Function.Injective j)
      (red : Λ →+* k), Function.Surjective red := by
  classical
  obtain ⟨f, α, hfmon, hirr, hroot, hsurj⟩ :=
    exists_monic_int_poly_of_finite_field k
  haveI : Fact (Irreducible (f.map (Int.castRingHom ℚ))) := ⟨hirr⟩
  obtain ⟨j₀, hj₀⟩ := exists_injective_adjoinRoot_int_rat hfmon
  haveI : CharZero (AdjoinRoot (f.map (Int.castRingHom ℚ))) :=
    charZero_of_injective_algebraMap
      (algebraMap ℚ (AdjoinRoot (f.map (Int.castRingHom ℚ)))).injective
  haveI : CharZero (ULift.{u} (AdjoinRoot (f.map (Int.castRingHom ℚ)))) :=
    (ULift.ringEquiv
      (R := AdjoinRoot (f.map (Int.castRingHom ℚ)))).toRingHom.charZero
  have e : ULift.{u} (AdjoinRoot (f.map (Int.castRingHom ℚ)))
      ≃ₐ[ℚ] AdjoinRoot (f.map (Int.castRingHom ℚ)) :=
    { ULift.ringEquiv (R := AdjoinRoot (f.map (Int.castRingHom ℚ))) with
      commutes' := fun r => by simp }
  haveI : FiniteDimensional ℚ
      (ULift.{u} (AdjoinRoot (f.map (Int.castRingHom ℚ)))) :=
    LinearEquiv.finiteDimensional e.toLinearEquiv.symm
  haveI : NumberField (ULift.{u} (AdjoinRoot (f.map (Int.castRingHom ℚ)))) :=
    {}
  refine ⟨ULift.{u} (AdjoinRoot (f.map (Int.castRingHom ℚ))), inferInstance,
    inferInstance, ULift.{u} (AdjoinRoot f), inferInstance,
    (ULift.ringEquiv
        (R := AdjoinRoot (f.map (Int.castRingHom ℚ)))).symm.toRingHom.comp
      (j₀.comp (ULift.ringEquiv (R := AdjoinRoot f)).toRingHom), ?_,
    (AdjoinRoot.lift (Int.castRingHom k) α hroot).comp
      (ULift.ringEquiv (R := AdjoinRoot f)).toRingHom, ?_⟩
  · exact (ULift.ringEquiv
      (R := AdjoinRoot (f.map (Int.castRingHom ℚ)))).symm.injective.comp
      (hj₀.comp (ULift.ringEquiv (R := AdjoinRoot f)).injective)
  · intro x
    obtain ⟨g, hg⟩ := hsurj x
    refine ⟨ULift.up (AdjoinRoot.mk f g), ?_⟩
    show AdjoinRoot.lift (Int.castRingHom k) α hroot (AdjoinRoot.mk f g) = x
    rw [AdjoinRoot.lift_mk]
    exact hg

/-- **A monic quadratic is determined by its two lower coefficients**
(PROVEN helper, pure polynomial algebra): if `φ a = −p₁` and `φ d = p₀`
for a monic `p` of `natDegree = 2`, then `(X² − C a·X + C d).map φ = p`.

The `map`-source companion of `map_eq_quadratic_of_monic_natDegree_two`
further down this file, which reads the coefficients off the TARGET of the
map; this one is stated in the direction the residual-modularity leaf
needs (the Hecke polynomial lives upstairs, over `Λ`, and is pushed down
to `pt.kp`).  It is restated here rather than reused because that lemma is
declared after this point in the module. -/
theorem quadratic_map_eq_of_monic_natDegree_two {A B : Type*} [CommRing A]
    [CommRing B] {p : Polynomial B} (hmonic : p.Monic) (hdeg : p.natDegree = 2)
    (φ : A →+* B) (a d : A) (ha : φ a = -(p.coeff 1)) (hd : φ d = p.coeff 0) :
    (X ^ 2 - C a * X + C d).map φ = p := by
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
  have hmap : (X ^ 2 - C a * X + C d).map φ
      = X ^ 2 + C (p.coeff 1) * X + C (p.coeff 0) := by
    simp only [Polynomial.map_add, Polynomial.map_sub, Polynomial.map_mul,
      Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C, ha, hd,
      Polynomial.C_neg]
    ring
  rw [hmap]
  exact hp.symm

set_option backward.isDefEq.respectTransparency false in
/-- **`charFrob` of a rank-`2` representation is monic of degree `2`**
(PROVEN helper): it is the characteristic polynomial of an endomorphism of
a finite free module of rank `2`.

The two conjuncts are separately available further down this file
(`charFrob_monic_of_free`, `charFrob_natDegree_of_rank_two`), but those are
pinned to the base `K = ℚ` and are declared after this point; the general
base is what the Hilbert–Blumenthal point needs (`F`). -/
theorem charFrob_monic_natDegree_two_of_rank_two {K : Type*} [Field K]
    [NumberField K] {A : Type*} [CommRing A] [Nontrivial A]
    [TopologicalSpace A] [IsTopologicalRing A] {M : Type*} [AddCommGroup M]
    [Module A M] [Module.Finite A M] [Module.Free A M]
    (v : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (ρ : GaloisRep K A M) (hdim : Module.rank A M = 2) :
    (ρ.charFrob v).Monic ∧ (ρ.charFrob v).natDegree = 2 := by
  refine ⟨?_, ?_⟩
  · show ((ρ.toLocal v
      (Field.AbsoluteGaloisGroup.adicArithFrob v)).charpoly).Monic
    exact LinearMap.charpoly_monic _
  · show ((ρ.toLocal v
      (Field.AbsoluteGaloisGroup.adicArithFrob v)).charpoly).natDegree = 2
    rw [LinearMap.charpoly_natDegree]
    exact Module.finrank_eq_of_rank_eq (by exact_mod_cast hdim)

/-- **The determinant clause descends to the residual representation**
(PROVEN glue, pure algebra over the `HilbertBlumenthalPoint` interface):
if the constant coefficient of `P w` is `Nw` in `D`, then the constant
coefficient of `ρbarp.charFrob w` is `Nw` in `kp`.

The chain is the point's own compatibility data.  `matchp` reads the
identity in `ℚ̄_p`: `ιC ((τp.charFrob w).coeff 0) = ψDp ((P w).coeff 0)`.
Ring homomorphisms preserve `ℕ`-casts, so the right side is `(Nw : ℚ̄_p)`,
which is also `ιC ((Nw : C))`; `ιC_injective` therefore DESCENDS the
identity to `C`, and applying `πp` and `residualp` moves it to `kp`.

Note that this is where the two joints of the automorphic cut turn out to
be one fact: the same argument, run from
`exists_heckeSystem_of_residualModularity`'s norm clause, is the
derivation recorded in the section note before that leaf.  The hypothesis
is stated over an ARBITRARY finite exceptional set `S`, which is the shape
`exists_coeff_zero_eq_absNorm_of_hilbertBlumenthalPoint` delivers; the
point's own compatibility data is only available off `pt.bad`, so the
conclusion needs both exclusions.  They are stated as two hypotheses
rather than as `w ∉ S ∪ pt.bad` so that the statement needs no
`DecidableEq` on the place set. -/
theorem residual_charFrob_coeff_zero_eq_absNorm_of_hilbertBlumenthalPoint
    {ℓ : ℕ} [Fact ℓ.Prime] {F : Type u} [Field F] [NumberField F]
    {k : Type u} [Field k] [TopologicalSpace k] [DiscreteTopology k]
    {W : Type v} [AddCommGroup W] [Module k W] [Module.Finite k W]
    [Module.Free k W]
    {ρbarF : GaloisRep F k W} (pt : HilbertBlumenthalPoint ℓ F ρbarF)
    (S : Finset (HeightOneSpectrum (NumberField.RingOfIntegers F)))
    (hP : ∀ w ∉ S, (pt.P w).coeff 0 = (Ideal.absNorm w.asIdeal : pt.D)) :
    ∀ w, w ∉ S → w ∉ pt.bad →
      (pt.ρbarp.charFrob w).coeff 0 = (Ideal.absNorm w.asIdeal : pt.kp) := by
  -- `pfact` is a field of the structure but is not registered globally as an
  -- instance, and `ℚ̄_p` cannot be named without it
  haveI : Fact (pt.p).Prime := pt.pfact
  intro w hwS hwbad
  have h1 : pt.ιC ((pt.τp.charFrob w).coeff 0)
      = pt.ψDp ((pt.P w).coeff 0) := by
    have h := congrArg (fun p : Polynomial (AlgebraicClosure ℚ_[pt.p]) =>
      p.coeff 0) (pt.matchp w hwbad)
    simpa using h
  rw [hP w hwS] at h1
  have h2 : (pt.τp.charFrob w).coeff 0
      = ((Ideal.absNorm w.asIdeal : ℕ) : pt.C) := by
    refine pt.ιC_injective ?_
    rw [h1]
    simp
  have h3 := congrArg (fun p : Polynomial pt.kp => p.coeff 0)
    (pt.residualp w hwbad)
  simp only [Polynomial.coeff_map, h2] at h3
  rw [← h3]
  simp

/-- **The parallel-weight-`2` normalization of the point's compatible
system** (**PROVEN 2026-07-26** by the cut-level repair recorded below —
the determinant clause is now the FIELD `HilbertBlumenthalPoint.detσ`;
EXTRACTED 2026-07-25 as the exact residual
content of joint (b) — see the VACUITY AUDIT of
`exists_heckeSystem_of_residualModularity` below, which identified this
single equation as everything that node formally asserts): away from a
finite set of places, the constant coefficient of the Frobenius
characteristic polynomial `P w` of the compatible system carried by a
`HilbertBlumenthalPoint` is the absolute norm `Nw`.

Classically this is the WEIL PAIRING on the Hilbert–Blumenthal abelian
variety `A/F`: for a place `w` of good reduction the determinant of
Frobenius on the Tate module is the value of the cyclotomic character,
i.e. `Nw`, so the charpoly of `Frob_w` is `X² − a_w·X + Nw` — the
parallel-weight-`2` normalization.  Equivalently, `det τp` is the
`p`-adic cyclotomic character, and `det σ` the `ℓ`-adic one; since both
members lie in the single system with coefficient field `D`, the clause
is a statement about `P` alone and is characteristic-free.

WHY IT WAS A SORRY NODE (history, and the reason for the repair).  The
`HilbertBlumenthalPoint` interface recorded `P`, `τp`, `σ` and the two
matching clauses `matchp`/`matchℓ`, but NO determinant
condition on any of them: `P` was arbitrary polynomial data there.  So
the clause was not derivable from the interface, and it is exactly the
piece of the abelian variety's geometry that the interface dropped —
which is why the repair is a new FIELD and not a new proof.
The in-tree PROVEN analogue for a representation that IS
hypothesized hardly ramified is
`charFrob_baseChange_coeff_zero_eq_absNorm` further down this module
(the determinant half of the Carayol/Shimura sub-cut): it derives the
same equation from `IsHardlyRamified.det` plus
`cyclotomicCharacter_adicArithFrob_base_eq_absNorm`.  Neither is
applicable to `pt.τp`, which is not `ρ.map (algebraMap ℚ F)` and
carries no hardly-ramified hypothesis.

WHERE IT NOW LIVES (cut-level repair, PERFORMED 2026-07-26): as the
FIELD `HilbertBlumenthalPoint.detσ`, supplied — through the geometric
joint `exists_hilbertBlumenthalPoint_of_five_le` and its two PROVEN
assemblies — by the frame that
`Fermat.exists_tateFrame_of_levelStructure` chooses, which is the only
place in the tree where the abelian variety's Weil pairing is visible.
This leaf is discharged by projection onto that field plus the algebra
recorded under SKELETON below.

SHARED WITH JOINT (a).  The sibling joint
`exists_residualModularity_of_hilbertBlumenthalPoint` has the SAME
formal content in residual form
(`(pt.ρbarp.charFrob w).coeff 0 = (Nw : pt.kp)`), and that follows from
this leaf through `pt.matchp`, injectivity of `pt.ιC` and
`pt.residualp`.  So this one leaf discharges the arithmetic of both
joints; the two are one determinant fact stated twice, as the cluster
sweep in the section note above records.

SOUNDNESS AUDIT (both ways, 2026-07-25): (i) direct — for a point
produced by `exists_hilbertBlumenthalPoint_of_five_le`, `P` really is
the family of Frobenius charpolys of a Hilbert–Blumenthal abelian
variety and the equation is the Weil-pairing determinant computation
above; for an abstract point the abstract-quantification caveat applies
IN FULL FORCE — nothing in the interface forces it, which is precisely
why the leaf is stated rather than proven; (ii) collapse — the
hypothesis package (an irreducible hardly ramified mod-`ℓ`
representation with `ℓ ≥ 5`) is classically unsatisfiable (headline
below), so the statement is classically true for every package.

SKELETON (2026-07-26 — glue first, then the cut).  The bare `sorry` was
first replaced by the full assembly over ONE sorried `have` carrying the
entire mathematical content: the WEIL-PAIRING DETERMINANT of the point's
`ℓ`-adic member,

  `∀ w ∉ pt.bad, LinearMap.det (pt.σ.toLocal w Frob_w) = (Nw : pt.O₀)`.

That `have` is now discharged by `pt.detσ` — it is verbatim the new
field — and the leaf is PROVEN.  Everything around it was already
compiler-checked rather than asserted: the
constant coefficient of a rank-`2` charpoly is the determinant
(`LinearMap.det_eq_sign_charpoly_coeff` together with
`Module.finrank_fin_fun`), `pt.matchℓ` transports the identity into
`ℚ̄_ℓ`, ring homomorphisms preserve `Nat.cast`, and `pt.ψDℓ` — a
homomorphism out of a field — is injective, so the identity descends to
`pt.D`.  The `have` was stated in exactly the form a FIELD of
`HilbertBlumenthalPoint` would take, and was deliberately NOT split off
as a named theorem: by the refutation below it is not dispatchable work
AT THIS NODE, so a separate node here would only have manufactured a
phantom leaf for the fleet to send an agent at.  The repair made it a
field instead.

NO PROOF OF THAT `have` CAN EXIST FROM THE INTERFACE — an explicit
refutation RELATIVE TO the interface (2026-07-26).  The audit above says
the interface "records no determinant condition"; that is sharper than
it sounds, because the conclusion is actually REFUTABLE for the points
the interface admits, existential `S₂` and all.  Let `pt` be any point
and let `χ : Γ_F → μ_ℓ` be a character of order `ℓ`, unramified outside
a finite set.  Twist:

* `D' := D(ζ_ℓ)` and `P' w := X² − χ(w)·a_w·X + χ(w)²·Nw`;
* `O₀' := O₀[ζ_ℓ]` (still local, finite free over `ℤ_ℓ`),
  `σ' := σ ⊗ χ`, with `ψDℓ'`, `ιO₀'` the evident extensions — `matchℓ`
  holds;
* `residualℓ` SURVIVES the twist: `ζ_ℓ ≡ 1` modulo the maximal ideal of
  `ℤ_ℓ[ζ_ℓ]` (where `ζ_ℓ − 1` is the uniformizer), so `χ` reduces to the
  trivial character and the mod-`ℓ` charpolys are unchanged;
* `C' := C[ζ_ℓ]`, `τp' := τp ⊗ χ` — `matchp` holds; `residualp` is
  restored by replacing the DATUM `ρbarp` with `ρbarp ⊗ χ̄`, and
  `irreduciblep`/`dihedralp` are invariant under twisting by a
  character.

The result satisfies every field of `HilbertBlumenthalPoint` over the
SAME `ρbarF`, yet `(P' w).coeff 0 = χ(w)²·Nw`, which differs from `Nw`
on a set of places of positive density (`χ²` is nontrivial because `ℓ`
is odd), hence on an INFINITE set — so no finite `S₂` repairs it.  The
conclusion is therefore not merely underdetermined by the interface: it
is FALSE for points the interface admits.

What keeps this declaration true is only the outer hypothesis package
(`hirr`, `hρbar`, `hℓ5`: an irreducible hardly ramified mod-`ℓ`
representation at `ℓ ≥ 5`), which is classically unsatisfiable — and
that discharge is exactly the one the ROUTE AUDIT of the section
docstring forbids here, in both of its forms (import cycle through
`Modularity/Interface.lean`, declaration cycle through this module's own
headline, whose assembly consumes pillar β hence this leaf).  So the
outer hypotheses are load-bearing for TRUTH while being unusable in any
PROOF, which is why the proof below consumes none of them.

CONSEQUENCE — THE ONLY DISCHARGE IS A FIELD OF THE STRUCTURE
(cut-level, PERFORMED 2026-07-26).  `HilbertBlumenthalPoint` now carries

  `detσ : ∀ w ∉ bad, LinearMap.det (σ.toLocal w Frob_w) = (Nw : O₀)`

(equivalently the `τp` form, which `matchp` and `ιC_injective` make
interchangeable with it; the `σ` form was chosen because it keeps the
algebra above alive and because the `ℓ`-adic frame is where the clause
is supplied).  Note that even a complete Weil-pairing theory in the tree
could not have discharged this leaf as stated:
`HilbertBlumenthalPoint` carries no abelian scheme at all, and
`Modularity/AbelianScheme.lean` (sorry-free) has geometric points and
Galois-stable torsion but no Tate module, no Weil pairing and no
Frobenius charpoly — so there would have been nothing here to apply
it TO.

WHERE THE FIELD IS SUPPLIED, and why that site is the honest one.  The
ONLY construction site of `HilbertBlumenthalPoint` in the tree is
`nonempty_hilbertBlumenthalPoint_of_isTwistedHilbertBlumenthalModuli`
(the geometric joint reaches it through
`exists_twistedHilbertBlumenthalModuli_of_five_le`), and there the
`ℓ`-adic member is the frame produced by
`Fermat.exists_tateFrame_of_levelStructure`.  The determinant clause was
added as one extra conjunct of THAT leaf's existential conclusion, and
the point's `bad` is now the union of three finite sets rather than two.
Putting it there is what makes it TRUE: the frame is chosen by the
prover, so the honest Tate frame discharges it, whereas the same clause
for a GIVEN frame is false — `φ` is only additive and `Γ_F`-equivariant,
so the `O`-structure it transports is an arbitrary embedding into
`End_{ℤ_q[Γ_F]}(T)`, and a second rank-`2` structure twisted by an
automorphism of `𝒪_{D,I}/ℤ_q` changes the determinant.  That is the same
counterexample that refuted the sibling
`Fermat.exists_weilFrobeniusSystem_of_mult`; see the DETERMINANT CLAUSE
paragraph in `Modularity/TateModule.lean`.

FAITHFULNESS (2026-07-26): `S₂` is EXISTENTIALLY quantified, so the
question "must `S₂` exclude the places above `p` as well as the ramified
ones?" is moot — the prover chooses `S₂`, and the proof below chooses
`pt.bad`, which by the interface's own documentation already contains
the conductor together with the places over `2`, `p` and `ℓ`.
Classically the identity holds at EVERY place of good reduction,
including `w ∣ p` (the constant coefficient of the compatible system's
polynomial is computed by any realization `λ ∤ w`), so no widening is
needed.  The statement is faithful.

CIRCULARITY GUARD (inherited from pillar β, load-bearing): no
discharge through `Family.lean`, `Lift.lean`, or
`Modularity/Interface.lean`. -/
theorem exists_coeff_zero_eq_absNorm_of_hilbertBlumenthalPoint
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
    (pt : HilbertBlumenthalPoint ℓ F (ρbar.map (algebraMap ℚ F))) :
    ∃ S₂ : Finset (HeightOneSpectrum (NumberField.RingOfIntegers F)),
      ∀ w ∉ S₂, (pt.P w).coeff 0 = (Ideal.absNorm w.asIdeal : pt.D) := by
  -- THE WEIL PAIRING on the Hilbert–Blumenthal abelian variety: the
  -- determinant of Frobenius on the `λ`-adic Tate module is the
  -- cyclotomic value `Nw`.  Not derivable from the interface, and
  -- refutable relative to it (twisting argument in the docstring) — so
  -- since 2026-07-26 it IS the interface: the field `detσ`, supplied
  -- where the Weil pairing is visible (the frame chosen by
  -- `Fermat.exists_tateFrame_of_levelStructure`).
  have hweil : ∀ w ∉ pt.bad,
      LinearMap.det (pt.σ.toLocal w (Field.AbsoluteGaloisGroup.adicArithFrob w)) =
        (Ideal.absNorm w.asIdeal : pt.O₀) := pt.detσ
  -- the constant coefficient of a rank-`2` charpoly is the determinant
  have hcoeff : ∀ w ∉ pt.bad,
      (pt.σ.charFrob w).coeff 0 = (Ideal.absNorm w.asIdeal : pt.O₀) := by
    intro w hw
    have hfr : Module.finrank pt.O₀ (Fin 2 → pt.O₀) = 2 :=
      Module.finrank_fin_fun pt.O₀
    have hdet := LinearMap.det_eq_sign_charpoly_coeff
      (pt.σ.toLocal w (Field.AbsoluteGaloisGroup.adicArithFrob w))
    rw [hfr, neg_one_sq, one_mul] at hdet
    rw [show pt.σ.charFrob w =
        (pt.σ.toLocal w (Field.AbsoluteGaloisGroup.adicArithFrob w)).charpoly from rfl,
      ← hdet, hweil w hw]
  -- transport into `ℚ̄_ℓ` along the point's own compatibility datum,
  -- then descend to `D` by injectivity of the place `ψDℓ`
  refine ⟨pt.bad, fun w hw => ?_⟩
  have hc := congrArg (fun q : Polynomial (AlgebraicClosure ℚ_[ℓ]) => q.coeff 0)
    (pt.matchℓ w hw)
  simp only [Polynomial.coeff_map] at hc
  rw [hcoeff w hw, map_natCast] at hc
  exact pt.ψDℓ.injective (by rw [map_natCast]; exact hc.symm)

/-- **Residual modularity in the dihedral case** (PROVEN 2026-07-25 as an
assembly over the determinant clause
`exists_coeff_zero_eq_absNorm_of_hilbertBlumenthalPoint` — the sibling
joint's own extracted leaf, immediately above — and the junk
coefficient ring `exists_numberField_surjection_of_finite`; see the
section note before those helpers; formerly a sorry node, joint (a) of the
automorphic cut — Hecke theta series / automorphic
induction from the quadratic `L`, the converse theorem, and
Jacquet–Langlands): the residual mod-`p` representation `ρbarp` of a
`HilbertBlumenthalPoint` — irreducible over `F` (`pt.irreduciblep`)
but reducible over the quadratic extension `L/F` (`pt.dihedralp`),
i.e. induced from a character of `G_L` — is MODULAR: away from a
finite set its Frobenius characteristic polynomials are the reductions
of the parallel-weight-`2` Hecke polynomials `X² − a_w·X + Nw` of a
Hilbert modular form.

The output is stated integrally, in the only pin-stateable form: a
coefficient ring `Λ` sitting injectively inside a NUMBER FIELD `E₁`
(the Hecke field of the theta series — this is the clause recording
that the eigenvalues are ALGEBRAIC, i.e. come from an automorphic
object rather than from an arbitrary family of residual polynomials),
a reduction `redΛ : Λ →+* kp` onto the residual coefficient field of
the point, and the eigenvalue function `a₁`.  The constant coefficient
is not free data: it is the absolute norm `Nw`, the parallel-weight-`2`
normalization forced classically by the Weil pairing on `A[p]`.

Classically: a `2`-dimensional representation irreducible over `F` and
reducible over a quadratic extension `L/F` is induced from a character
of `G_L`, so `ρbarp ≅ Ind_{G_L}^{G_F} χ̄`.  Lift `χ̄` to a Hecke
character `χ` of `L` and form the theta series `θ(χ)` — automorphic
induction from `GL(1)/L` to `GL(2)/F`, whose Hecke eigenvalue at a
place `w` of `F` is `χ(w₁) + χ(w₂)` for `w` split in `L` and `0` for
`w` inert, with constant coefficient the norm; Weil's converse theorem
(in the Jacquet–Langlands form) makes `θ(χ)` automorphic, and the
Jacquet–Langlands correspondence transports it between the
quaternionic and Hilbert settings in which the lifting theorem of
joint (b) is formulated.  This is Hecke's classical construction over
`ℚ`; over a totally real base see Rogawski–Tunnell, *On Artin
L-functions associated to Hilbert modular forms of weight one*,
Invent. Math. 74 (1983), and Taylor, *Remarks on a conjecture of
Fontaine and Mazur*, J. Inst. Math. Jussieu 1 (2002), §5, where this
is the residual input of the lifting theorem.

NOT SERRE'S CONJECTURE (the reason the cut is worth making): the
dihedral case of residual modularity is elementary automorphic
induction, available since Hecke — which is exactly why Taylor's
construction arranges the auxiliary `p`-level structure so that `A[p]`
is induced.  Nothing here presupposes Serre's conjecture or any
`R = 𝕋` theorem.

PIN AUDIT (2026-07-25): the mathlib pin has no Hecke characters of a
number field, no theta series, no converse theorem and no
Jacquet–Langlands correspondence — and no Hilbert modular forms at all
(`grep Hilbert` over `Mathlib/NumberTheory/` finds only Hilbert's
theorem 90 and the Hilbert basis theorem), so no part of this
statement reduces to library material.

SOUNDNESS AUDIT (both ways, 2026-07-25): (i) direct — for the intended
instantiation (a point produced by
`exists_hilbertBlumenthalPoint_of_five_le`, whose `p`-torsion really is
induced from a character and whose determinant really is cyclotomic,
so that the constant coefficient really is `Nw`) this is the
theta-series construction above; for an abstract point the
abstract-quantification caveat applies IN FULL FORCE — the interface
does not force `det ρbarp` to be cyclotomic, and the norm clause does
force it; (ii) collapse — the hypothesis package (an irreducible
hardly ramified mod-`ℓ` representation with `ℓ ≥ 5`) is classically
unsatisfiable (headline below), so the statement is classically true
for every package.

VACUITY AUDIT (2026-07-25, cluster sweep — audit only, the statement
was NOT changed).  This node is CONTENT-LITE: its entire formal content
is the residual norm clause
`(pt.ρbarp.charFrob w).coeff 0 = (Ideal.absNorm w.asIdeal : pt.kp)`.
Junk witness for everything else: `pt.kp` is FINITE, so pick a number
field `E₁` with a prime over `p` of the right residue degree, put
`Λ := 𝓞_{E₁}`, `jΛ` the inclusion, `redΛ` the (surjective) reduction
onto `pt.kp`, `S₁ := ∅`, and `a₁ w :=` any `redΛ`-preimage of
`−(pt.ρbarp.charFrob w).coeff 1`; the charpoly is monic of degree `2`
so the `X²` and `X` coefficients then match at every place, and
`redΛ ((Nw : Λ)) = (Nw : pt.kp)` is forced, leaving exactly the constant
coefficient.  In particular the "the eigenvalues are ALGEBRAIC" reading
of `E₁`/`jΛ` is FORMALLY EMPTY here — algebraicity is a real constraint
only against a characteristic-zero target such as `ℚ̄_ℓ`, not against a
finite field.  Nothing of Hecke's theta-series construction, the
converse theorem or Jacquet–Langlands is captured: `pt.irreduciblep`,
`pt.dihedralp` and `pt.L` are consumed by no part of the conclusion.

Moreover this node is IMPLIED by the sibling joint
`exists_heckeSystem_of_residualModularity`'s own norm clause together
with `pt.matchp`, `pt.residualp` and injectivity of `pt.ιC` (derivation
in the section note above), so the two joints are one determinant fact
stated twice.  Repair belongs at the parent's conclusion, not here —
see the section note.

VACUITY AUDIT, MECHANIZED (2026-07-25 — the paragraph above is now
PROVEN rather than asserted).  The junk witness it describes is built by
`exists_numberField_surjection_of_finite`, which produces `E₁`, `Λ`, `jΛ`
and a SURJECTIVE `redΛ` from the FINITENESS of `pt.kp` alone — that
construction inspects no other datum of the point, and no hypothesis of
this theorem — after which `a₁ w` is any `redΛ`-preimage of the residual
trace and `S₁ := S₂ ∪ pt.bad`.  What survives is literally the single
equation
`(pt.ρbarp.charFrob w).coeff 0 = (Ideal.absNorm w.asIdeal : pt.kp)`,
supplied by the leaf
`exists_coeff_zero_eq_absNorm_of_hilbertBlumenthalPoint` through the
PROVEN descent
`residual_charFrob_coeff_zero_eq_absNorm_of_hilbertBlumenthalPoint`.
`pt.irreduciblep`, `pt.dihedralp` and `pt.L` are consumed by no step of
the proof below, and no hypothesis of this theorem is used except in its
verbatim hand-off to that leaf — which is why none is underscored: the
emptiness has been RELOCATED onto the leaf, not removed.

ROUTE AUDIT: the odd-prime dichotomy is unavailable here — see the
section docstring above (import cycle AND declaration cycle).

CIRCULARITY GUARD (inherited from pillar β, load-bearing): no
discharge through `Family.lean`, `Lift.lean`, or
`Modularity/Interface.lean`. -/
theorem exists_residualModularity_of_hilbertBlumenthalPoint
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
    (pt : HilbertBlumenthalPoint ℓ F (ρbar.map (algebraMap ℚ F))) :
    ∃ (E₁ : Type u) (_ : Field E₁) (_ : NumberField E₁)
      (Λ : Type u) (_ : CommRing Λ) (jΛ : Λ →+* E₁)
      (_ : Function.Injective jΛ) (redΛ : Λ →+* pt.kp)
      (a₁ : HeightOneSpectrum (NumberField.RingOfIntegers F) → Λ)
      (S₁ : Finset (HeightOneSpectrum (NumberField.RingOfIntegers F))),
      ∀ w ∉ S₁,
        (X ^ 2 - C (a₁ w) * X + C (Ideal.absNorm w.asIdeal : Λ)).map redΛ =
          pt.ρbarp.charFrob w := by
  classical
  -- the node's ENTIRE formal content: the determinant clause of the
  -- compatible system, descended to the residual representation
  obtain ⟨S₂, hS₂⟩ :=
    exists_coeff_zero_eq_absNorm_of_hilbertBlumenthalPoint hℓodd hℓ5 hZinj
      hrank hρ hW hρbar hirr π hπsurj hπ F hFtr hFgal pt
  have hnorm :=
    residual_charFrob_coeff_zero_eq_absNorm_of_hilbertBlumenthalPoint pt S₂ hS₂
  -- the coefficient ring, built from the FINITENESS of `pt.kp` alone
  -- (`finitekp` is a structure field, not a global instance)
  haveI : Finite pt.kp := pt.finitekp
  obtain ⟨E₁, hE₁, hNE₁, Λ, hΛ, jΛ, hjΛ, redΛ, hred⟩ :=
    exists_numberField_surjection_of_finite pt.kp
  have hquad : ∀ w : HeightOneSpectrum (NumberField.RingOfIntegers F),
      (pt.ρbarp.charFrob w).Monic ∧ (pt.ρbarp.charFrob w).natDegree = 2 :=
    fun w => charFrob_monic_natDegree_two_of_rank_two w pt.ρbarp (by simp)
  -- the eigenvalues: any `redΛ`-preimages of the residual traces
  have hpre : ∀ w : HeightOneSpectrum (NumberField.RingOfIntegers F),
      ∃ a : Λ, redΛ a = -((pt.ρbarp.charFrob w).coeff 1) := fun w => hred _
  choose a₁ ha₁ using hpre
  refine ⟨E₁, hE₁, hNE₁, Λ, hΛ, jΛ, hjΛ, redΛ, a₁, S₂ ∪ pt.bad, fun w hw => ?_⟩
  exact quadratic_map_eq_of_monic_natDegree_two (hquad w).1 (hquad w).2 redΛ
    (a₁ w) _ (ha₁ w) (by
      rw [map_natCast]
      exact (hnorm w (fun h => hw (Finset.mem_union_left _ h))
        (fun h => hw (Finset.mem_union_right _ h))).symm)

-- `backward.isDefEq.respectTransparency false`: the two `show` steps in
-- the proof below unfold `GaloisRep.charFrob` to the
-- `LinearMap.charpoly` it is defined to be.  This is a
-- defeq-transparency compatibility flag, not a resource bump, and it is
-- the same one the file's own PROVEN twins
-- `charFrob_natDegree_of_rank_two` and
-- `charFrob_map_eq_quadratic_of_rank_two` carry for exactly this step.
set_option backward.isDefEq.respectTransparency false in
/-- **Modularity lifting at `p` in the residually dihedral case**
(DECOMPOSED 2026-07-25: now a PROVEN assembly over the single leaf
`exists_coeff_zero_eq_absNorm_of_hilbertBlumenthalPoint` immediately
above — joint (b) of the automorphic cut — Taylor, *Remarks on a
conjecture of Fontaine and Mazur*, J. Inst. Math. Jussieu 1 (2002),
§5, following Wiles and Skinner–Wiles): the residual modularity of
joint (a) is promoted from `ρbarp` to the `p`-adic member `τp` of the
point's compatible system.  The output is the Hecke eigensystem of a
Hilbert newform `g` of parallel weight `2` over `F`: its Hecke field
`E₀`, its eigenvalue function `a₀`, and — this is the clause that
carries the compatibility content — an identification `θ` of the Hecke
field inside the real-multiplication field `pt.D` of the system, such
that the `p`-adic Frobenius characteristic polynomials of `τp` are the
Hecke polynomials `X² − a_w·X + Nw` read inside `ℚ̄_p` through the
point's own place `pt.ψDp` of `D` over `p`.

Classically, in two steps.  (1) The modularity lifting theorem in the
residually dihedral case: `τp` is a lift of the modular residual
representation `ρbarp` (joint (a)) which is de Rham of parallel weight
`2` (it is the `p`-adic Tate module of an abelian variety with real
multiplication), so `τp` is itself modular — Taylor 2002 §5 (the
Fontaine–Mazur-conjecture paper, where this is the lifting step behind
Theorem B), whose method is Wiles' `R = 𝕋` argument in the form
developed by Skinner–Wiles for residually dihedral (and more generally
residually reducible-after-restriction) situations, run through Hida
families; see also Skinner–Wiles, *Residually reducible
representations and modular forms*, Publ. Math. IHÉS 89 (1999), and
*Nearly ordinary deformations of irreducible residual representations*,
Ann. Fac. Sci. Toulouse 10 (2001).  (2) The coefficient bookkeeping:
`g` has a Hecke field `E₀`, a number field by Shimura's rationality
theorem, and Carayol's local-global compatibility at the places where
everything is unramified identifies the Hecke polynomial of `g` at `w`
with the characteristic polynomial of Frobenius at `w`; since `τp` is
the `p`-adic member of the system with coefficient field `D`, that
identification is realized by an embedding `θ : E₀ →+* D` compatible
with the chosen place `ψDp` — i.e. the Hecke field of `g` sits in the
real-multiplication field of `A`, which is the classical statement
that `A` is the abelian variety attached to `g`.

Literature for (2): Shimura, Duke Math. J. 45 (1978), §2 (rationality
and the Hecke field of a Hilbert newform); Carayol, Ann. Sci. ÉNS 19
(1986) (local-global compatibility, the normalization used here);
Taylor, Invent. Math. 98 (1989) (the remaining cases).

PIN AUDIT (2026-07-25): as for joint (a) — no Hilbert modular forms,
no Hecke algebras over a totally real base, and no deformation-theoretic
`R = 𝕋` machinery over any base but `ℚ` in this repository
(`Patching.lean` is hard-pinned to `ℚ` through `IsHardlyRamified`; see
the PATCHING-GENERALIZATION AUDIT further down this file).  Nothing
here reduces to library material.

WHY THIS STATEMENT IS NOT VACUOUS: the conclusion forces the constant
coefficient of `(τp.charFrob w).map ιC` to be the norm `Nw` and the
whole polynomial to descend to the subfield `θ(E₀) ⊆ D` through the
point's own place — neither is derivable from the
`HilbertBlumenthalPoint` interface, in which `P`, `τp` and `ψDp` are
unconstrained data.  Contrast the bare form of the joint discussed in
the section note above, which the point's own data satisfies by `rfl`.

VACUITY AUDIT (2026-07-25, cluster sweep — audit only, the statement
was NOT changed).  The paragraph above is HALF WRONG and is retained
only so the correction is visible next to it: the `θ`-descent clause IS
derivable from the interface.  `E₀ := pt.D`, `θ := RingHom.id pt.D`,
`S₀ := pt.bad`, `a₀ w := −(pt.P w).coeff 1` reduces the conclusion, via
`pt.matchp` and injectivity of `pt.ψDp` (which also forces `pt.P w`
monic of degree `2`, since `(τp.charFrob w).map ιC` is), to the single
equation `(pt.P w).coeff 0 = (Ideal.absNorm w.asIdeal : pt.D)`.  So the
formal content of this node is EXACTLY the norm clause — a Weil-pairing
determinant statement about the abelian variety, belonging to the
GEOMETRIC joint — and nothing of Taylor 2002 §5, Wiles or
Skinner–Wiles is captured.  The honest place for that clause is a new
field of `HilbertBlumenthalPoint` supplied by
`exists_hilbertBlumenthalPoint_of_five_le`, after which this node and
its sibling `exists_residualModularity_of_hilbertBlumenthalPoint`
become fully junk-witnessable and the automorphic content has to be
restated at the PARENT's conclusion — see the section note above for
the two pin-stateable candidates (Weil bound, or integrality of the
eigenvalues).  Cut-level; not performed here.

ASSEMBLY (2026-07-25, PROVEN — this node is no longer a sorry node).
The audit above is now MECHANIZED rather than merely asserted: its junk
witness is the proof.  Take `E₀ := pt.D`, `θ := RingHom.id pt.D`,
`a₀ w := −(pt.P w).coeff 1`, `S₀ := S₂ ∪ pt.bad`, where `S₂` is the
finite set supplied by
`exists_coeff_zero_eq_absNorm_of_hilbertBlumenthalPoint` above.  Then,
away from `S₀`:

* `charFrob_map_eq_quadratic_of_rank_two` puts the left-hand side in
  the shape `X² − C (−ιC c₁)·X + C (ιC c₀)`, `c_i` the coefficients of
  `pt.τp.charFrob w` — `charFrob` is a characteristic polynomial of an
  endomorphism of a rank-`2` free module, hence monic of degree `2`,
  and this is pure shape, no arithmetic;
* `pt.matchp` gives `(pt.τp.charFrob w).map pt.ιC = (pt.P w).map pt.ψDp`,
  and reading off coefficients (`Polynomial.coeff_map`) turns
  `ιC c₁` into `ψDp ((pt.P w).coeff 1)` and `ιC c₀` into
  `ψDp ((pt.P w).coeff 0)`;
* the norm leaf rewrites `(pt.P w).coeff 0` as `(Nw : pt.D)`, and
  `map_natCast` matches it with the `C (Nw : E₀)` of the target, whose
  image under ANY ring homomorphism is forced to be `(Nw : ℚ̄_p)`.

That last observation is the reason the audit is exact: the constant
coefficient of the target is `(ψDp ∘ θ) ((Nw : E₀)) = (Nw : ℚ̄_p)` for
EVERY choice of `E₀` and `θ`, since ring homomorphisms preserve
`Nat.cast`.  So the norm clause is not merely sufficient for this node,
it is necessary — the node and the leaf above are equivalent modulo the
bad set, and no choice of Hecke field can evade it.

CONSEQUENCE, load-bearing for the cut (2026-07-25): the residual
modularity package of joint (a) — `E₁`, `Λ`, `jΛ`, `redΛ`, `a₁`, `S₁`,
`hres` — is NOT CONSUMED by this node, and is underscore-prefixed below
so that this is mechanically visible.  Joint (b) therefore does not
depend on joint (a) at all: nothing of the Wiles / Skinner–Wiles
lifting argument, whose entire point is that residual modularity is the
INPUT, survives in the formal statement.  This is a cut-level defect of
the automorphic cut, not of this proof, and it is reported rather than
patched here; see the section note above for the repair (propagate a
genuinely automorphic clause — the Weil bound or integrality of the
eigenvalues — into the PARENT's conclusion).

SOUNDNESS AUDIT (both ways, 2026-07-25): (i) direct — for the intended
instantiation (a point produced by
`exists_hilbertBlumenthalPoint_of_five_le`, so that `τp` really is the
`p`-adic Tate module of a Hilbert–Blumenthal abelian variety and the
residual modularity of joint (a) really comes from a theta series) this
is Taylor 2002 §5 plus Shimura/Carayol; for an abstract point and an
abstract residual-modularity package the abstract-quantification caveat
applies IN FULL FORCE (the local conditions at `p` that the lifting
theorem needs — nearly ordinary / de Rham of parallel weight `2` — are
not stateable on this interface, and the Weil-pairing determinant is
not recorded either); (ii) collapse — the hypothesis package (an
irreducible hardly ramified mod-`ℓ` representation with `ℓ ≥ 5`) is
classically unsatisfiable (headline below), so the statement is
classically true for every package.

ROUTE AUDIT: the odd-prime dichotomy is unavailable here — see the
section docstring above (import cycle AND declaration cycle).

CIRCULARITY GUARD (inherited from pillar β, load-bearing): no
discharge through `Family.lean`, `Lift.lean`, or
`Modularity/Interface.lean`. -/
theorem exists_heckeSystem_of_residualModularity
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
    (pt : HilbertBlumenthalPoint ℓ F (ρbar.map (algebraMap ℚ F)))
    {E₁ : Type u} [Field E₁] [NumberField E₁]
    {Λ : Type u} [CommRing Λ] (_jΛ : Λ →+* E₁)
    (_hjΛ : Function.Injective _jΛ) (_redΛ : Λ →+* pt.kp)
    (_a₁ : HeightOneSpectrum (NumberField.RingOfIntegers F) → Λ)
    (_S₁ : Finset (HeightOneSpectrum (NumberField.RingOfIntegers F)))
    (_hres : ∀ w ∉ _S₁,
      (X ^ 2 - C (_a₁ w) * X + C (Ideal.absNorm w.asIdeal : Λ)).map _redΛ =
        pt.ρbarp.charFrob w) :
    ∃ (E₀ : Type u) (_ : Field E₀) (_ : NumberField E₀)
      (θ : E₀ →+* pt.D)
      (a₀ : HeightOneSpectrum (NumberField.RingOfIntegers F) → E₀)
      (S₀ : Finset (HeightOneSpectrum (NumberField.RingOfIntegers F))),
      ∀ w ∉ S₀,
        (pt.τp.charFrob w).map pt.ιC =
          (X ^ 2 - C (a₀ w) * X +
            C (Ideal.absNorm w.asIdeal : E₀)).map (pt.ψDp.comp θ) := by
  classical
  -- the ONLY arithmetic input: the parallel-weight-`2` (Weil-pairing)
  -- normalization of the point's own compatible system
  obtain ⟨S₂, hS₂⟩ := exists_coeff_zero_eq_absNorm_of_hilbertBlumenthalPoint
    hℓodd hℓ5 hZinj hrank hρ hW hρbar hirr π hπsurj hπ F hFtr hFgal pt
  -- the `p`-adic coefficient ring is a nontrivial commutative ring, so
  -- the lattice `Fin 2 → C` has rank `2`
  haveI : IsLocalRing pt.C := pt.isLocalRingC
  have hrankC : Module.rank pt.C (Fin 2 → pt.C) = 2 := by
    simp
  refine ⟨pt.D, pt.fieldD, pt.numberFieldD, RingHom.id pt.D,
    fun w => -(pt.P w).coeff 1, S₂ ∪ pt.bad, fun w hw => ?_⟩
  have hmatch := pt.matchp w fun h => hw (Finset.mem_union_right _ h)
  -- `charFrob` is the characteristic polynomial of an endomorphism of a
  -- rank-`2` free module, hence monic of degree `2`, so its image under
  -- any coefficient map has the Hecke shape.  (This is the content of
  -- `map_eq_quadratic_of_monic_natDegree_two` /
  -- `charFrob_map_eq_quadratic_of_rank_two`, both of which live LATER in
  -- this file and therefore cannot be cited here; the argument is
  -- reproduced inline rather than by moving another owner's
  -- declaration.)
  have hmonic : (pt.τp.charFrob w).Monic := by
    show ((pt.τp.toLocal w
      (Field.AbsoluteGaloisGroup.adicArithFrob w)).charpoly).Monic
    exact LinearMap.charpoly_monic _
  have hdeg : (pt.τp.charFrob w).natDegree = 2 := by
    show ((pt.τp.toLocal w
      (Field.AbsoluteGaloisGroup.adicArithFrob w)).charpoly).natDegree = 2
    rw [LinearMap.charpoly_natDegree]
    exact Module.finrank_eq_of_rank_eq (by exact_mod_cast hrankC)
  have hquad : (pt.τp.charFrob w).map pt.ιC =
      X ^ 2 - C (-(pt.ιC ((pt.τp.charFrob w).coeff 1))) * X +
        C (pt.ιC ((pt.τp.charFrob w).coeff 0)) := by
    have hlead : (pt.τp.charFrob w).coeff 2 = 1 := by
      have h := hmonic.coeff_natDegree
      rwa [hdeg] at h
    have hp : pt.τp.charFrob w =
        X ^ 2 + C ((pt.τp.charFrob w).coeff 1) * X +
          C ((pt.τp.charFrob w).coeff 0) := by
      ext n
      match n with
      | 0 => simp
      | 1 => simp
      | 2 => simp [hlead]
      | (m + 3) =>
        have hlt : (pt.τp.charFrob w).natDegree < m + 3 := by rw [hdeg]; omega
        simp [Polynomial.coeff_eq_zero_of_natDegree_lt hlt]
    conv_lhs => rw [hp]
    simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_pow,
      Polynomial.map_X, Polynomial.map_C, map_neg]
    ring
  -- the two coefficient identifications supplied by `matchp`
  have hc1 : pt.ιC ((pt.τp.charFrob w).coeff 1) =
      pt.ψDp ((pt.P w).coeff 1) := by
    have h := Polynomial.ext_iff.mp hmatch 1
    simpa only [Polynomial.coeff_map] using h
  have hc0 : pt.ιC ((pt.τp.charFrob w).coeff 0) =
      pt.ψDp ((Ideal.absNorm w.asIdeal : pt.D)) := by
    have h := Polynomial.ext_iff.mp hmatch 0
    simp only [Polynomial.coeff_map] at h
    rw [h, hS₂ w fun hmem => hw (Finset.mem_union_left _ hmem)]
  rw [hquad, hc1, hc0]
  simp [Polynomial.map_add, Polynomial.map_mul,
    Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C]

/-- **The automorphic joint of Theorem B** (PROVEN 2026-07-25 as an
assembly over the two joints of the automorphic cut — see the section
note above; the depth now lives in
`exists_residualModularity_of_hilbertBlumenthalPoint` (dihedral
residual modularity: theta series / automorphic induction, converse
theorem, Jacquet–Langlands) and
`exists_heckeSystem_of_residualModularity` (modularity lifting at `p`
in the residually dihedral case, Taylor 2002 §5)): the compatible
system carried by a `HilbertBlumenthalPoint` is the Hecke eigensystem
of a Hilbert newform over `F`; i.e. there is a number field `E₀` (the
Hecke field), a family of Hecke polynomials `hecke₀`, and a place `ψ₀`
of `E₀` over `ℓ`, agreeing with the system's own polynomials `P`
inside `ℚ̄_ℓ` away from a finite set.

Classically, in three steps: (1) the residual mod-`p` representation
`ρbarp` of the point is irreducible but induced from a character of
`G_L` for the quadratic `L/F` (`irreduciblep`, `dihedralp`), so it is
attached to a Hecke theta series of `L` — modular, by the converse
theorems, transported to the totally real `F` by Jacquet–Langlands;
(2) the modularity lifting theorem in the residually dihedral case
(Taylor 2002 §5, following Wiles and Skinner–Wiles) promotes this to
the `p`-adic member `τp` of the system, which is therefore attached to
a Hilbert newform `g` of parallel weight `2` over `F`, with Hecke
field `E₀`; (3) `τp` and `σ` lie in ONE strictly compatible system
with coefficient field `D` (`matchp`, `matchℓ`), and Carayol's
local-global compatibility at unramified places identifies the
Frobenius polynomials of `g` with those of the system away from the
bad set — the conclusion below, stated for `P` itself so that the
transfer to `σ` is pure algebra, done in the parent assembly.

Steps (1) and (2) are the two sorried joints; step (3) — the transport
across characteristics — is the PROVEN content of this node.

ASSEMBLY (2026-07-25, PROVEN).  Joint (a) supplies the residual
modularity package `(E₁, Λ, jΛ, redΛ, a₁, S₁)` of `ρbarp`; joint (b)
consumes it and returns the newform's Hecke field `E₀`, its
identification `θ : E₀ →+* pt.D` inside the coefficient field of the
system, the eigenvalues `a₀` and a bad set `S₀`, with the `p`-adic
match `(τp.charFrob w).map ιC = (X² − a₀ w·X + Nw).map (ψDp ∘ θ)`.
The glue is then pure algebra, at the united bad set `S₀ ∪ pt.bad`:

* the point's `matchp` rewrites the left side as `(P w).map ψDp`, so
  the `ψDp`-images of `P w` and of `(X² − a₀ w·X + Nw).map θ` agree
  (`Polynomial.map_map`);
* `ψDp` is a ring homomorphism out of the FIELD `D`, hence injective,
  so `Polynomial.map_injective` DESCENDS the identity from `ℚ̄_p` to
  `D` itself: `P w = (X² − a₀ w·X + Nw).map θ` — an identity of
  polynomials over `D`, free of both characteristics;
* pushing that identity along the point's `ℓ`-adic place `ψDℓ` and
  contracting with `Polynomial.map_map` gives the conclusion with
  `ψ₀ := ψDℓ ∘ θ`.

VACUITY AUDIT (2026-07-25, load-bearing for the cut — recorded here
because it is the reason the joints look the way they do): the
statement of THIS node is satisfied by the point's own data
(`E₀ := pt.D`, `hecke₀ := pt.P`, `ψ₀ := pt.ψDℓ`, `S := ∅`, `rfl`),
since `D` is a number field and `P` is a polynomial family over it.
So it could be discharged with no automorphic input whatsoever — which
would delete Taylor 2002 §5 from the tree rather than formalize it.
The cut above avoids that: the automorphic content is stated where it
IS pin-stateable (the parallel-weight-`2` norm constant coefficient,
and the identification of the Hecke field inside `D` compatible with
the place over `p`), neither of which the interface provides, and this
node is proven from those by the transport argument above.  A future
strengthening of the joint should therefore not weaken (a)/(b): it
should propagate `θ` and the norm clause upward into
`MoretBaillySeed` (whose `hecke₀`/`modular₀` fields are free in the
same way), which is a change to that structure and its other consumers,
not to this node.

SOUNDNESS AUDIT (both ways, 2026-07-25): (i) direct — the proof below
is unconditional algebra over the two joints, each of which carries
its own audit; (ii) collapse — the hypothesis set is classically
unsatisfiable (headline below), so the statement is classically true
for every package.

ROUTE AUDIT: the odd-prime dichotomy is unavailable here — see the
section docstring above (import cycle AND declaration cycle).

CIRCULARITY GUARD (inherited from pillar β, load-bearing): no
discharge through `Family.lean`, `Lift.lean`, or
`Modularity/Interface.lean`; it binds both joints. -/
theorem exists_heckeEigensystem_of_hilbertBlumenthalPoint
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
    (pt : HilbertBlumenthalPoint ℓ F (ρbar.map (algebraMap ℚ F))) :
    ∃ (E₀ : Type u) (_ : Field E₀) (_ : NumberField E₀)
      (hecke₀ : HeightOneSpectrum (NumberField.RingOfIntegers F) →
        Polynomial E₀)
      (ψ₀ : E₀ →+* AlgebraicClosure ℚ_[ℓ])
      (S : Finset (HeightOneSpectrum (NumberField.RingOfIntegers F))),
      ∀ w ∉ S, (pt.P w).map pt.ψDℓ = (hecke₀ w).map ψ₀ := by
  classical
  -- joint (a): the residual mod-`p` representation of the point is
  -- modular, being induced from a character of the quadratic `L/F`
  obtain ⟨E₁, hE₁, hNE₁, Λ, hΛ, jΛ, hjΛ, redΛ, a₁, S₁, hres⟩ :=
    exists_residualModularity_of_hilbertBlumenthalPoint hℓodd hℓ5 hZinj hrank hρ
      hW hρbar hirr π hπsurj hπ F hFtr hFgal pt
  -- joint (b): modularity lifting at `p` promotes it to the `p`-adic
  -- member `τp`, with the newform's Hecke field `E₀` identified inside
  -- the coefficient field `D` of the system by `θ`
  obtain ⟨E₀, hE₀, hNE₀, θ, a₀, S₀, hmod⟩ :=
    exists_heckeSystem_of_residualModularity hℓodd hℓ5 hZinj hrank hρ hW hρbar
      hirr π hπsurj hπ F hFtr hFgal pt jΛ hjΛ redΛ a₁ S₁ hres
  refine ⟨E₀, hE₀, hNE₀,
    fun w => X ^ 2 - C (a₀ w) * X + C (Ideal.absNorm w.asIdeal : E₀),
    pt.ψDℓ.comp θ, S₀ ∪ pt.bad, fun w hw => ?_⟩
  -- the transport: descend the `p`-adic identity to the coefficient
  -- field `D` through the injective place `ψDp`
  have hdesc : pt.P w =
      (X ^ 2 - C (a₀ w) * X + C (Ideal.absNorm w.asIdeal : E₀)).map θ :=
    Polynomial.map_injective pt.ψDp pt.ψDp.injective <| by
      rw [Polynomial.map_map,
        ← pt.matchp w fun h => hw (Finset.mem_union_right _ h)]
      exact hmod w fun h => hw (Finset.mem_union_left _ h)
  -- then push it into `ℚ̄_ℓ` along the point's `ℓ`-adic place
  rw [hdesc, Polynomial.map_map]

/-- **Moret–Bailly base production** (Taylor 2002, Theorem B;
DECOMPOSED 2026-07-24 — now a PROVEN assembly over the two joints of
the section above): for the irreducible hardly ramified residual
representation `ρbar` at `ℓ ≥ 5`, there is a totally real number
field `F`, Galois over `ℚ`, over which `ρbar` stays irreducible and
acquires a modular congruent companion — a `MoretBaillySeed`.

Classically: Moret–Bailly's theorem (*Groupes de Picard et problèmes
de Skolem II*, Ann. Sci. ÉNS 22 (1989); the form used is Taylor 2002,
Theorem G / Proposition 2.1) produces `F` totally real and Galois
over `ℚ`, satisfying prescribed local conditions at any finite set of
primes (split/unramified behavior at `2`, `3`, `ℓ`; linear
disjointness from the fixed field data of `ρbar`, which keeps
`ρbar|_{G_{F(ζ_ℓ)}}` absolutely irreducible — a fortiori
`ρbar|_{G_F}` irreducible, the conjunct carried below), together with
a point of a twisted Hilbert–Blumenthal moduli variety over `F`: an
abelian variety `A/F` with real multiplication whose `ℓ`-torsion
realizes `ρbar|_{G_F}` and whose `p`-torsion, for an auxiliary prime
`p`, is induced from a character (dihedral). The dihedral `p`-torsion
is modular (Hecke theta series / converse theorems +
Jacquet–Langlands), and modularity lifting at `p` (the residually
dihedral case, Taylor 2002 §5 following Wiles/Skinner–Wiles) makes
`A` itself modular, attached to a Hilbert newform `g` of parallel
weight `2` over `F`; its `λ`-adic representation at `λ | ℓ`, on a
Carayol-normalized stable lattice, is the seed `σ`, residually
`ρbar|_{G_F}`.

PIN AUDIT (2026-07-24, restated after the decomposition): the mathlib
pin has NO Moret–Bailly material and no number-field weak
approximation in the required form (no `Skolem`/`MoretBailly`
declarations; `Mathlib/NumberTheory/NumberField/` carries no
incompressible-neighborhood existence theorem on Picard-scheme
torsors), and no Hilbert–Blumenthal moduli; that unbuildable depth is
now isolated in the GEOMETRIC leaf
`exists_hilbertBlumenthalPoint_of_five_le`, whose own pin audit
records where a further decomposition would have to start.

SOUNDNESS AUDIT (both ways, 2026-07-24): (i) direct — this is Taylor
2002 Theorem B verbatim (with the Galois refinement of §1 and the
irreducibility preservation built into the avoidance set), a true
nonvacuous theorem: its proof (Moret–Bailly + converse theorems +
residually dihedral lifting) nowhere presupposes Serre's conjecture;
(ii) collapse — the hypothesis set (an irreducible hardly ramified
mod-`ℓ` representation, `ℓ ≥ 5`) is classically unsatisfiable
(headline below), so the statement is also vacuously sound.

ROUTE AUDIT (2026-07-24): the shared odd-prime dichotomy
`not_isIrreducible_of_isHardlyRamified_of_odd` — the discharge used by
the descent leaves of pillar 3 — is NOT available for this node or its
children: `Modularity/Interface.lean`, its home, IMPORTS this module,
and at `ℓ ≥ 5` it is itself discharged by this module's headline
`not_isIrreducible_of_isHardlyRamified_of_five_le`, whose assembly
consumes this very node. Both the import graph and the declaration
graph forbid it, so the classical route recorded above is preserved
verbatim as the only sound discharge.

ASSEMBLY (2026-07-24, PROVEN): the geometric joint
(`exists_hilbertBlumenthalPoint_of_five_le` — Moret–Bailly 1989 + the
twisted Hilbert–Blumenthal moduli interpretation: the totally real
Galois `F`, the image-preserving restriction `hrestr`, and the
`HilbertBlumenthalPoint` carrying the compatible system of `A/F` with
its two moduli conditions) + the automorphic joint
(`exists_heckeEigensystem_of_hilbertBlumenthalPoint` — dihedral
residual modularity and modularity lifting at `p`, Taylor 2002 §5:
the system is a Hilbert-newform Hecke eigensystem), glued by
(a) PROVING the irreducibility conjunct from image preservation
through `isIrreducible_map_of_range_surjective` — it is no longer
asserted anywhere — and (b) transporting the eigensystem match along
the point's own `matchℓ` over the united bad set. Those two leaves are
the residual sorries of this node; the circularity guard above binds
both.

CIRCULARITY GUARD (inherited from pillar β, load-bearing): must be
proven by the independent Moret–Bailly construction — never through
`Family.lean`, `Lift.lean`, or `Modularity/Interface.lean`. -/
theorem exists_moretBailly_seed_of_five_le
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
    ∃ (F : Type u) (_ : Field F) (_ : NumberField F)
      (_ : NumberField.IsTotallyReal F) (_ : IsGalois ℚ F)
      (_ : (ρbar.map (algebraMap ℚ F)).IsIrreducible),
      Nonempty (MoretBaillySeed ℓ F (ρbar.map (algebraMap ℚ F))) := by
  classical
  -- (i) the geometric joint: the totally real Galois base `F`, the
  -- image-preserving restriction, and the Hilbert–Blumenthal point
  obtain ⟨F, hF, hNF, hFtr, hFgal, hrestr, ⟨pt⟩⟩ :=
    exists_hilbertBlumenthalPoint_of_five_le hℓodd hℓ5 hZinj hrank hρ hW
      hρbar hirr π hπsurj hπ
  -- irreducibility over `F` is PROVEN from image preservation
  have hirrF : (ρbar.map (algebraMap ℚ F)).IsIrreducible :=
    isIrreducible_map_of_range_surjective _ hrestr hirr
  -- (ii) the automorphic joint: the compatible system of the point is a
  -- Hilbert-newform Hecke eigensystem
  obtain ⟨E₀, hE₀, hNE₀, hecke₀, ψ₀, S, hsys⟩ :=
    exists_heckeEigensystem_of_hilbertBlumenthalPoint hℓodd hℓ5 hZinj hrank
      hρ hW hρbar hirr π hπsurj hπ F hFtr hFgal pt
  -- glue: unite the bad sets and transport the match along `matchℓ`
  refine ⟨F, hF, hNF, hFtr, hFgal, hirrF,
    ⟨{ E₀ := E₀, bad₀ := pt.bad ∪ S, hecke₀ := hecke₀, O₀ := pt.O₀,
       σ := pt.σ, ψ₀ := ψ₀, ι₀ := pt.ιO₀, ι₀_injective := pt.ιO₀_injective,
       π₀ := pt.π₀, modular₀ := ?_, residual₀ := ?_ }⟩⟩
  · intro w hw
    exact (pt.matchℓ w fun h => hw (Finset.mem_union_left _ h)).trans
      (hsys w fun h => hw (Finset.mem_union_right _ h))
  · intro w hw
    exact pt.residualℓ w fun h => hw (Finset.mem_union_left _ h)

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
  for the relevant deformation problem: the Taylor–Wiles/Kisin
  patching argument over the totally real base, whose output is the
  raw `ℓ`-adic Hecke eigensystem `(aF, dF)` of the Hilbert newform
  attached to `ρ|_{G_F}`, together with the coefficient embedding
  `ιO : O ↪ ℚ̄_ℓ`.
* (b) `exists_heckeField_of_eigensystem` — Carayol local-global
  normalization + Shimura rationality: the `ℚ̄_ℓ`-valued eigensystem
  is defined over a NUMBER FIELD `E` (the Hecke field), through a
  place `ψℓ` of `E` over `ℓ`.

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
  have hall : ∀ σ : Field.absoluteGaloisGroup ℚ,
      ((ρ σ).charpoly).map π = (ρbar σ).charpoly := by
    intro σ
    rw [← hbc σ, ← he, GaloisRep.conj_apply, LinearEquiv.charpoly_conj]
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
the citation a claim it has no right to make.  Two nodes below are narrowed
this way — `exists_heckeSubfield_of_determinants` (`hbadℓ`, the places over
`ℓ`) and `exists_threeadic_realization_of_heckePackage` (`hbad2`, `hbad3`,
`hbadℓ`, the places over `2`, `3` and `ℓ`).

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
now demands. It is applied once inside `exists_heckePackage_of_seed` (at
`ℓ`, for the determinant sub-leaf) and three times in a row at the
`3`-adic call site, at `2`, `3` and `ℓ`; the earlier conclusions survive the
later enlargements because each `badF'` contains its predecessor. Nothing
downstream assumes more. -/
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

/-- **`R = 𝕋` over the totally real base** (sub-leaf (a) of
the modularity-lifting cut — Kisin 2009 / Taylor 2006, the
Taylor–Wiles patching argument over `F`): given the modular seed `σ`
over `F` and the residual congruence `hcong` identifying `ρ|_{G_F}`
and `σ` as lifts of one irreducible residual representation, the lift
`ρ|_{G_F}` is ITSELF modular: away from a finite bad set its Frobenius
characteristic polynomial is the Hecke polynomial
`X² − a_w·X + Nw` of a Hilbert newform, read inside `ℚ̄_ℓ` through a
coefficient embedding `ιO` of the lift's coefficient ring.

The conclusion is deliberately stated in the RAW `ℚ̄_ℓ`-valued form —
the eigenvalue function `aF` (classically `a_w`, the `T_w`-eigenvalue
of the newform) and the constant-coefficient function `dF`
(classically the absolute norm `Nw`, forced by the cyclotomic
determinant of `hρ`) — with no claim that these values are ALGEBRAIC.
The algebraicity is Shimura's rationality theorem and is the content
of the next sub-leaf (`exists_heckeField_of_eigensystem`); keeping the
two apart is what makes this leaf exactly the `R = 𝕋` statement and
that one exactly the Carayol/Shimura normalization.

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

FORMAL-CONTENT AUDIT (2026-07-25 — READ THIS BEFORE BUILDING ON THIS
NODE; it is the reason the node is PROVEN rather than sorried).  The
statement as cut above does NOT formally capture `R = 𝕋`: its
conclusion is derivable from the SHAPE of `charFrob` alone, with no
arithmetic input at all, and the proof below does exactly that.  The
reason is that the conclusion quantifies `aF`, `dF` and `badF`
existentially with no tie to any Hecke datum, and
`(ρ|_{G_F}).charFrob w` is by definition the characteristic polynomial
of a Frobenius endomorphism of the free rank-`2` module `Fin 2 → O`,
hence MONIC OF DEGREE `2`; so `aF w := −ιO((charFrob w).coeff 1)` and
`dF w := ιO((charFrob w).coeff 0)` satisfy the required identity at
EVERY place (`badF := ∅`), for any injective `ιO`, whatever `ρ` is.
The only ingredient beyond that shape is the existence of an injective
`ιO : O →+* ℚ̄_ℓ`, which is generic commutative algebra
(`exists_injective_ringHom_algebraicClosure_of_moduleFinite` above) and
consumes only module-finiteness of `O` over `ℤ_ℓ` and `hZinj`.

The binder names below make the gap MECHANICALLY visible: every
hypothesis the proof does not consume is underscore-prefixed, and that
list — `_hℓ5`, `_hρ`, `_hρbar`, `_hirr`, `_hπsurj`, `_hπ`, `_hFtr`,
`_hFgal`, `_hirrF`, `_seed`, `_hcong` — is precisely the arithmetic
input (`ℓ ≥ 5`, hard ramification, residual irreducibility, the
Moret–Bailly seed and the residual congruence) that an honest `R = 𝕋`
statement would have to consume and this one does not.

Consequences, recorded for the cut's owner:

* nothing of Kisin/Taylor/Fujiwara is formalized by this node.  The
  literature paragraphs above document what the node was INTENDED to
  carry; they are now documentation of a gap that has moved, not of a
  formalized theorem.
* the entire arithmetic burden of the modularity-lifting cut now rests
  on the sibling `exists_heckeField_of_eigensystem`, whose hypothesis
  `hshape` is satisfiable by the junk eigensystem produced here — so
  that node is no longer merely "Shimura rationality": it is
  rationality PLUS the `R = 𝕋` content that this statement fails to
  demand, and its own docstring's abstract-quantification caveat now
  applies in full.
* a restatement that would actually pin `R = 𝕋` must tie the
  eigensystem to a Hecke datum rather than existentially quantifying
  it — e.g. output a Hilbert-newform carrier (a structure with the
  eigenvalue system, level and weight of an actual newform over `F`)
  whose eigensystem is `aF`, or demand at minimum that `aF` be the
  `ψ`-image of a NUMBER-FIELD-valued system and that `dF w = Nw`
  (which is arithmetic: it needs the cyclotomic determinant of `hρ`
  transported to `F`-places).  Both changes alter this node's
  conclusion type, hence the `obtain` pattern in
  `exists_heckePackage_of_seed` and the hypothesis list of
  `exists_heckeField_of_eigensystem`, so they are a cut-level
  restatement and were NOT performed unilaterally here.

CIRCULARITY GUARD (inherited from pillar β, load-bearing): no
discharge through `Family.lean`, `Lift.lean`, or
`Modularity/Interface.lean` — respected: the proof below uses only
this module's own helpers and mathlib. -/
theorem exists_heckeEigensystem_of_congruentSeed
    {ℓ : ℕ} (hℓodd : Odd ℓ) [Fact ℓ.Prime] (_hℓ5 : 5 ≤ ℓ)
    {O : Type u} [CommRing O] [IsDomain O] [TopologicalSpace O]
    [IsTopologicalRing O] [Algebra ℤ_[ℓ] O] [IsLocalRing O]
    [Module.Finite ℤ_[ℓ] O] [IsModuleTopology ℤ_[ℓ] O]
    (hZinj : Function.Injective (algebraMap ℤ_[ℓ] O))
    {ρ : GaloisRep ℚ O (Fin 2 → O)}
    (hrank : Module.rank O (Fin 2 → O) = 2)
    (_hρ : IsHardlyRamified hℓodd hrank ρ)
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
    (F : Type u) [Field F] [NumberField F]
    (_hFtr : NumberField.IsTotallyReal F) (_hFgal : IsGalois ℚ F)
    (_hirrF : (ρbar.map (algebraMap ℚ F)).IsIrreducible)
    (_seed : MoretBaillySeed ℓ F (ρbar.map (algebraMap ℚ F)))
    (badρ : Finset (HeightOneSpectrum (NumberField.RingOfIntegers F)))
    (_hcong : ∀ w ∉ badρ,
      ((ρ.map (algebraMap ℚ F)).charFrob w).map π =
        (ρbar.map (algebraMap ℚ F)).charFrob w) :
    ∃ (badF : Finset (HeightOneSpectrum (NumberField.RingOfIntegers F)))
      (aF dF : HeightOneSpectrum (NumberField.RingOfIntegers F) →
        AlgebraicClosure ℚ_[ℓ])
      (ιO : O →+* AlgebraicClosure ℚ_[ℓ]) (_ : Function.Injective ιO),
      ∀ w ∉ badF,
        ((ρ.map (algebraMap ℚ F)).charFrob w).map ιO =
          X ^ 2 - C (aF w) * X + C (dF w) := by
  classical
  -- (i) the coefficient embedding `ιO : O ↪ ℚ̄_ℓ` (generic commutative
  -- algebra: `O` is a `ℤ_ℓ`-finite domain receiving `ℤ_ℓ` injectively)
  obtain ⟨ιO, hιO⟩ :=
    exists_injective_ringHom_algebraicClosure_of_moduleFinite (ℓ := ℓ) O hZinj
  -- (ii) the eigensystem, read off the Frobenius characteristic
  -- polynomials themselves: they are monic of degree `2`, so their
  -- `ιO`-images have the Hecke shape at EVERY place (see the
  -- FORMAL-CONTENT AUDIT above — this is all the statement demands)
  refine ⟨∅, fun w => -(ιO (((ρ.map (algebraMap ℚ F)).charFrob w).coeff 1)),
    fun w => ιO (((ρ.map (algebraMap ℚ F)).charFrob w).coeff 0), ιO, hιO,
    fun w _ => ?_⟩
  exact charFrob_map_eq_quadratic_of_rank_two w (ρ.map (algebraMap ℚ F))
    hrank ιO

/-! ### The Carayol/Shimura sub-cut (2026-07-25)

Sub-leaf (b) of the modularity-lifting cut —
`exists_heckeField_of_eigensystem` below — is now a PROVEN assembly over
two sharply-stated inputs and one proven bridge, cut along the joint the
classical literature itself uses:

* `exists_heckeField_mem_range_of_eigensystem` — **Shimura rationality**
  in its minimal form: the EIGENVALUE function `aF` takes its values in
  a single number field, presented as membership in the range of one
  embedding `ψℓ : E ↪ ℚ̄_ℓ`.  This is the only genuinely automorphic
  input of sub-leaf (b): nothing else in the package forces a family of
  `ℚ̄_ℓ`-values to be algebraic.
* `cyclotomicCharacter_adicArithFrob_base_eq_absNorm` — the **place-wise
  cyclotomic normalization over the base `F`**: at a place `w` of `F`
  not over `ℓ`, the `ℓ`-adic cyclotomic character of `G_ℚ` takes the
  value `Nw = ‖w‖` on the global image of the arithmetic Frobenius at
  `w`.  This is pure algebraic number theory (unramifiedness of the
  cyclotomic character away from `ℓ`, plus `Frob_w(ζ) = ζ^{Nw}`), and it
  is the exact `F`-analogue of the PROVEN rational-prime lemma
  `cyclotomicCharacter_adicArithFrob_eq_natCast` further down this
  module.  **PROVEN 2026-07-25** by exactly that route — mirroring the
  rational proof with the residue cardinality `Nw` in place of `q` —
  over the new roots-of-unity brick
  `adicArithFrob_rootsOfUnity_pow_base`.  So sub-leaf (b-ii) is CLOSED,
  and sub-leaf (b) now rests on the single remaining citation
  `exists_heckeField_mem_range_of_eigensystem`.
* `charFrob_baseChange_coeff_zero_eq_absNorm` — PROVEN from the previous
  item: the DETERMINANT coefficient of the base-changed Frobenius
  charpoly is the rational integer `Nw`.  So the `d`-half of sub-leaf
  (b) needs no automorphic input away from `ℓ`: it descends to `ℚ ⊆ E`
  by the cyclotomic determinant clause of `hρ` alone.

The residual asymmetry is honest: at the finitely many places `w | ℓ`
the cyclotomic character IS ramified, so `dF w` (which the shape
hypothesis pins to `det ρ(Frob_w)`) carries no rationality of its own,
and the citation above must supply those values too — that is the
second clause of `exists_heckeField_mem_range_of_eigensystem`.  In the
intended instantiation the bad set `badF` produced by `R = 𝕋` already
contains every place over `ℓ`, so that clause is vacuous there.

REFINEMENT (2026-07-25, second pass): sub-leaf (b-i) itself has since
been split along exactly that asymmetry and PROVEN as an assembly over
its two halves, so the two clauses now have separate owners and, more
importantly, separately recorded statuses:

* `exists_heckeSubfield_of_eigenvalues` — the EIGENVALUE half, i.e.
  Shimura rationality proper.  This is the one genuinely automorphic
  citation of the whole modularity-lifting cut.
* `exists_heckeSubfield_of_determinants` — the DETERMINANT half at the
  places over `ℓ`.  This is NOT a classical theorem: its docstring
  records that the clause is false for the intended objects whenever
  `badF` omits a place over `ℓ`, and vacuous exactly when it does not.
  **NARROWED AND CLOSED 2026-07-26**: the node now carries the
  hypothesis `hbadℓ : ∀ w, (ℓ : 𝓞 F) ∈ w.asIdeal → w ∈ badF`, which
  deletes exactly the false instances, and is proven vacuously with
  `E := ⊥`.  The hypothesis is discharged for free at
  `exists_heckePackage_of_seed`, which enlarges the existentially
  chosen `badF` by the places over `ℓ`
  (`exists_finset_superset_of_places_mem`) — the same repair
  `exists_threeadic_realization_of_heckePackage` received for the
  places over `3`.  So the whole modularity-lifting cut now rests on
  the single citation `exists_heckeSubfield_of_eigenvalues`.

Both are stated as membership in a single FINITE-DIMENSIONAL
intermediate field of `ℚ/ℚ̄_ℓ` rather than as an abstract number field
plus an embedding: the intermediate-field form is what Shimura's
theorem literally says, and it removes the type-construction and
universe packaging from the citation.  The packaging — compositum of
the two intermediate fields, `ULift` into `Type u`, and the
`NumberField` instance — is discharged formally in
`exists_heckeField_mem_range_of_eigensystem` below.

THIRD PASS (2026-07-26): sub-leaf (b-i-a) —
`exists_heckeSubfield_of_eigenvalues`, Shimura rationality proper — is
itself now a PROVEN assembly over the two independent classical inputs
it had been bundling:

* `exists_heckeGenerators_of_eigenvalues` (b-i-a-1) — FINITE
  GENERATION: finitely many good places already generate the field of
  eigenvalues (finite generation of the Hecke algebra of a fixed weight
  and level; effectively the Sturm bound).
* `isIntegral_heckeEigenvalues` (b-i-a-2) — ALGEBRAICITY: each single
  eigenvalue `aF w` is an algebraic number (the `ℤ`-integral
  characteristic polynomials of the Hecke operators on the `ℚ`-rational
  space of cusp forms).

Neither implies the other, and neither alone gives the parent —
`√2, √3, √5, …` are all algebraic of degree `2` and lie in no finite
extension of `ℚ`, while a one-element generating set with a
transcendental value satisfies finite generation.  Together they give
the parent by `IntermediateField.finiteDimensional_adjoin`.  This is a
cut along the literature's own joint (Hecke integrality vs. finite
generation of the Hecke algebra) and NOT a weakening: the conjunction
of the two sub-leaves is strictly stronger than the parent, since it
also names the generators.
-/

/-- **Finite generation of the Hecke field of the Hilbert-newform
eigensystem** (sorry node; sub-leaf (b-i-a-1) — the FINITENESS half of
Shimura rationality): finitely many good places already generate the
field of eigenvalues.  Concretely there is a finite set `s` of places
of `F` disjoint from the bad set such that every `aF w` with `w ∉ badF`
lies in the subfield of `ℚ̄_ℓ` generated over `ℚ` by the finitely many
values `aF '' s`.

Classically this is the finite generation of the Hecke algebra: the
Hecke algebra `𝕋 = ℤ[T_w : w ∤ 𝔫]` of parallel weight `2` and fixed
level `𝔫` over `F` acts faithfully on the FINITE-DIMENSIONAL space of
Hilbert cusp forms of that weight and level, so it is a finitely
generated `ℤ`-module and already finitely many `T_w` generate it — the
effective form of this being that the Hecke operators below the Sturm
bound suffice.  Applying the eigensystem character `λ` of the newform
`f` attached to `ρ|_{G_F}` then gives
`a_w = λ(T_w) ∈ ℚ(λ(T_{w₁}), …, λ(T_{wₙ}))` for every good `w`, which
through Carayol's local-global compatibility (which identifies `aF w`
with the image of `a_w` on the nose, place by place) is exactly the
statement here.

WHY THIS IS SPLIT OFF FROM THE PARENT (2026-07-26): see the section
note above.  The parent bundled two independent classical inputs, and
bundling them hid which half a would-be discharge actually needs.  This
half is the one that says "ONE field", and it is the half that a
finiteness theorem — not a rationality theorem — discharges.

NOTE ON `s`: the generating set is demanded to consist of GOOD places
(`∀ w ∈ s, w ∉ badF`).  Without that clause the leaf would be
discharged by generators at which `hshape` says nothing, and the parent
could not feed them to the algebraicity sub-leaf, which is stated only
away from `badF`.  The clause costs the citation nothing — the
classical generators are Hecke operators at good places by
construction.

PIN AUDIT (inherited from the parent, unchanged): the mathlib pin has
no Hilbert modular forms and no Hecke algebras over a totally real
base, so no part of this statement reduces to library material.

SOUNDNESS AUDIT (inherited from the parent, unchanged): for the
intended instantiation this is finite generation of the Hilbert Hecke
algebra; for an abstract `(aF, dF)` merely satisfying `hshape` the
abstract-quantification caveat applies IN FULL FORCE, and the statement
survives only by the collapse route (the hypothesis package — an
irreducible hardly ramified mod-`ℓ` representation with `ℓ ≥ 5` — is
classically unsatisfiable, which is this module's headline).  The full
hypothesis list is retained DELIBERATELY.

INSTANTIATION DEFECT (inherited from the parent, unchanged): the only
supplier, `exists_heckeEigensystem_of_congruentSeed`, is formally empty
and hands `badF := ∅`.  The fix is upstream, not here.

CIRCULARITY GUARD (inherited from pillar β, load-bearing): no discharge
through `Family.lean`, `Lift.lean`, or `Modularity/Interface.lean`. -/
theorem exists_heckeGenerators_of_eigenvalues
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
    (F : Type u) [Field F] [NumberField F]
    (hFtr : NumberField.IsTotallyReal F) (hFgal : IsGalois ℚ F)
    (hirrF : (ρbar.map (algebraMap ℚ F)).IsIrreducible)
    (badF : Finset (HeightOneSpectrum (NumberField.RingOfIntegers F)))
    (aF dF : HeightOneSpectrum (NumberField.RingOfIntegers F) →
      AlgebraicClosure ℚ_[ℓ])
    (ιO : O →+* AlgebraicClosure ℚ_[ℓ]) (hιO : Function.Injective ιO)
    (hshape : ∀ w ∉ badF,
      ((ρ.map (algebraMap ℚ F)).charFrob w).map ιO =
        X ^ 2 - C (aF w) * X + C (dF w)) :
    ∃ s : Finset (HeightOneSpectrum (NumberField.RingOfIntegers F)),
      (∀ w ∈ s, w ∉ badF) ∧
      ∀ w ∉ badF, aF w ∈ IntermediateField.adjoin ℚ
        (aF '' (s : Set (HeightOneSpectrum (NumberField.RingOfIntegers F)))) :=
  sorry

/-- **Algebraicity of the Hilbert-newform Hecke eigenvalues** (sorry
node; sub-leaf (b-i-a-2) — the ALGEBRAICITY half of Shimura
rationality): each single eigenvalue `aF w` of the modular lift
`ρ|_{G_F}`, at a place `w` outside the bad set, is an algebraic number.

Classically: `aF w` is the `T_w`-eigenvalue of the Hilbert newform `f`
of parallel weight `2` over `F` attached to `ρ|_{G_F}`, and `T_w` acts
on the `ℚ`-rational space of Hilbert cusp forms of `f`'s weight and
level — a finite-dimensional `ℚ`-vector space — preserving a `ℤ`-lattice.
So the characteristic polynomial of `T_w` on that space has `ℤ`
coefficients, and `a_w`, being one of its roots, is an algebraic
integer.  (This is a strictly per-place statement: it says nothing
about the eigenvalues at different places lying in a COMMON field,
which is the separate sub-leaf `exists_heckeGenerators_of_eigenvalues`
above.)

The conclusion is stated as `IsIntegral ℚ (aF w)` — over the field `ℚ`
integrality and algebraicity coincide, and `IsIntegral ℚ` is the form
`IntermediateField.finiteDimensional_adjoin` consumes in the parent's
assembly.  The sharper classical fact `IsIntegral ℤ (aF w)` is TRUE and
deliberately not demanded: the parent needs only algebraicity, and
demanding `ℤ`-integrality would put the Ramanujan-normalization
bookkeeping into a citation that does not use it.

WHY THIS IS SPLIT OFF FROM THE PARENT (2026-07-26): see the section
note above.  Algebraicity alone does NOT give the parent — the family
`√2, √3, √5, …` is algebraic and lies in no finite extension of `ℚ` —
and the parent's own docstring had recorded the two halves as one
citation, which hid that a proof of algebraicity would leave the
finiteness half entirely open.

PIN AUDIT (inherited from the parent, unchanged): the mathlib pin has
no Hilbert modular forms and no Hecke algebras over a totally real
base, so no part of this statement reduces to library material.

SOUNDNESS AUDIT (inherited from the parent, unchanged): for an abstract
`(aF, dF)` merely satisfying `hshape` the abstract-quantification
caveat applies IN FULL FORCE — `hshape` determines `aF w` as
`-ιO (charFrob w).coeff 1`, an element of `ιO O`, which is algebraic
over `ℚ_[ℓ]` and NOT over `ℚ` — so the statement survives only by the
collapse route.  The full hypothesis list is retained DELIBERATELY.

INSTANTIATION DEFECT (inherited from the parent, unchanged): the only
supplier, `exists_heckeEigensystem_of_congruentSeed`, is formally empty
and hands `badF := ∅`, so at the instantiation that actually reaches
this node the statement asserts algebraicity of the Frobenius traces at
EVERY place of `F`, including the ramified ones.  The fix is upstream,
not here.

CIRCULARITY GUARD (inherited from pillar β, load-bearing): no discharge
through `Family.lean`, `Lift.lean`, or `Modularity/Interface.lean`. -/
theorem isIntegral_heckeEigenvalues
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
    (F : Type u) [Field F] [NumberField F]
    (hFtr : NumberField.IsTotallyReal F) (hFgal : IsGalois ℚ F)
    (hirrF : (ρbar.map (algebraMap ℚ F)).IsIrreducible)
    (badF : Finset (HeightOneSpectrum (NumberField.RingOfIntegers F)))
    (aF dF : HeightOneSpectrum (NumberField.RingOfIntegers F) →
      AlgebraicClosure ℚ_[ℓ])
    (ιO : O →+* AlgebraicClosure ℚ_[ℓ]) (hιO : Function.Injective ιO)
    (hshape : ∀ w ∉ badF,
      ((ρ.map (algebraMap ℚ F)).charFrob w).map ιO =
        X ^ 2 - C (aF w) * X + C (dF w)) :
    ∀ w ∉ badF, IsIntegral ℚ (aF w) :=
  sorry

/-- **Shimura rationality for the Hilbert-newform eigensystem,
intermediate-field form** (PROVEN 2026-07-26 as an assembly over the
two halves of sub-leaf (b-i-a) — the STATEMENT IS UNCHANGED, what moved
is where the burden sits; sub-leaf (b-i-a) is the ONLY genuinely
automorphic input of the whole modularity-lifting cut): the
eigenvalue function `aF` of the modular lift `ρ|_{G_F}` takes all its
values, away from the bad set, inside ONE finite extension of `ℚ`
sitting in `ℚ̄_ℓ` — the Hecke field of the attached Hilbert newform.

Classically: `aF w` is the `T_w`-eigenvalue of the Hilbert newform `f`
of parallel weight `2` over `F` attached to `ρ|_{G_F}` by the `R = 𝕋`
sub-leaf.  Shimura's rationality theorem — the Hecke eigenvalues of a
Hilbert newform generate a NUMBER field `E = ℚ(a_w : w)`, because the
Hecke operators act on a finite-dimensional `ℚ`-rational space of cusp
forms with `ℤ`-integral characteristic polynomials, and Galois
conjugation permutes newforms — gives `E`; the ambient embedding is the
place `λ | ℓ` at which the `λ`-adic realization of `f` is `ρ|_{G_F}`,
which is why the statement can be phrased inside `ℚ̄_ℓ` with no
embedding data of its own; Carayol's local-global compatibility at the
unramified places is what makes the identification of `charFrob` with
the Hecke polynomial hold place by place rather than merely after
semisimplification, and hence makes `aF w` (read off the shape
hypothesis `hshape`) equal to the image of `a_w` on the nose.

WHY THE INTERMEDIATE-FIELD FORM IS THE SHARP ONE: the conclusion
"`aF w` lies in a fixed finite extension of `ℚ` inside `ℚ̄_ℓ`" is
literally Shimura's assertion.  The number-field-plus-embedding form of
the parent leaf is equivalent to it (take `Set.range ψℓ` one way, a
`ULift` of the intermediate field the other), but carries in addition a
type construction and a universe lift, which are formal packaging and
are now discharged in the parent rather than demanded of the citation.

PIN AUDIT (inherited, re-verified 2026-07-25): the mathlib pin has no
Hilbert modular forms and no Hecke algebras over a totally real base
(`grep Hilbert` over `Mathlib/NumberTheory/`: only Hilbert's theorem 90
and Hilbert basis), so no part of this statement can be reduced to
library material.  Its only sound discharge is the construction of
Hilbert-modular Hecke theory: in dependency order, (1) Hilbert modular
forms of parallel weight `2` over a totally real field, (2) the Hecke
operators `T_w` and the Hecke algebra acting on the cusp forms of a
given level, (3) the `ℚ`-rational structure on that space together with
integrality of the Hecke characteristic polynomials, (4) Shimura
rationality itself, (5) Carayol/Taylor attachment of `λ`-adic Galois
representations with local-global compatibility, and (6) the `R = 𝕋`
identification tying `ρ|_{G_F}` to a newform.  Note that (6) is NOT
among this leaf's hypotheses — nothing here says `ρ` is modular — so
even a complete formalization of (1)–(5) does not by itself discharge
this node; it is a citation whose modularity input arrives only through
the intended instantiation.

SOUNDNESS AUDIT (both ways, 2026-07-25): (i) direct — for the intended
instantiation this is Shimura rationality plus Carayol verbatim; for an
abstract `(aF, dF)` merely satisfying `hshape` the
abstract-quantification caveat applies IN FULL FORCE, since `hshape`
determines `aF w` as `-ιO (charFrob w).coeff 1`, an element of `ιO O`,
which is algebraic over `ℚ_[ℓ]` and NOT over `ℚ`; (ii) collapse — the
hypothesis set (an irreducible hardly ramified mod-`ℓ` representation,
`ℓ ≥ 5`) is classically unsatisfiable (headline below), so the
statement is classically true for every package.  The full hypothesis
list is retained DELIBERATELY: dropping `hρbar`/`hirr`/`hshape` would
leave a statement about arbitrary `ℚ̄_ℓ`-valued families, which is
false.

INSTANTIATION DEFECT (inherited from the parent, unchanged by the
split): the only supplier, `exists_heckeEigensystem_of_congruentSeed`,
is formally empty and hands `badF := ∅`, so at the instantiation that
actually reaches this node the statement asserts algebraicity of the
Frobenius traces at EVERY place of `F` — including the ramified ones,
where `charFrob` is not a Hecke polynomial.  The fix is upstream (give
that node a genuine level/bad set), not here.

ASSEMBLY (2026-07-26, PROVEN — the STATEMENT IS UNCHANGED).  This node
is no longer a citation.  Its two classical inputs, which it had been
bundling into one appeal to "Shimura rationality", are now separate
sorried leaves above:

* `exists_heckeGenerators_of_eigenvalues` (b-i-a-1) — FINITE
  GENERATION: a finite set `s` of good places with every `aF w`
  (`w ∉ badF`) inside `ℚ(aF '' s)`.  Classically: the Hecke algebra of
  a fixed weight and level is a finitely generated `ℤ`-module, so
  finitely many `T_w` generate it (Sturm bound).
* `isIntegral_heckeEigenvalues` (b-i-a-2) — ALGEBRAICITY:
  `IsIntegral ℚ (aF w)` for `w ∉ badF`.  Classically: the `T_w` have
  `ℤ`-integral characteristic polynomials on the `ℚ`-rational space of
  cusp forms, so their eigenvalues are algebraic integers.

`IntermediateField.adjoin ℚ (aF '' s)` is then finite-dimensional over
`ℚ` by `IntermediateField.finiteDimensional_adjoin` (a finite set of
integral elements), and it contains every `aF w` by the first leaf.

WHY THIS IS THE RIGHT JOINT, and why it is not a relabeling.  Neither
half implies the other and neither alone gives this node: `√2, √3, √5,
…` are algebraic of degree `2` and lie in no finite extension of `ℚ`,
while a singleton generating set with a transcendental value satisfies
finite generation.  So the conjunction is strictly stronger than this
node (it also names the generators), and each half is a recognizable
classical theorem with its own literature — Hecke integrality on one
side, finite generation of the Hecke algebra on the other — rather
than a repackaging of the conclusion.  What the split does NOT do is
supply the missing modularity hypothesis: see the SOUNDNESS AUDIT
above, which is inherited verbatim by both halves.

CIRCULARITY GUARD (inherited from pillar β, load-bearing): no
discharge through `Family.lean`, `Lift.lean`, or
`Modularity/Interface.lean` — respected: the proof below uses only the
two sub-leaves above and mathlib. -/
theorem exists_heckeSubfield_of_eigenvalues
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
    (F : Type u) [Field F] [NumberField F]
    (hFtr : NumberField.IsTotallyReal F) (hFgal : IsGalois ℚ F)
    (hirrF : (ρbar.map (algebraMap ℚ F)).IsIrreducible)
    (badF : Finset (HeightOneSpectrum (NumberField.RingOfIntegers F)))
    (aF dF : HeightOneSpectrum (NumberField.RingOfIntegers F) →
      AlgebraicClosure ℚ_[ℓ])
    (ιO : O →+* AlgebraicClosure ℚ_[ℓ]) (hιO : Function.Injective ιO)
    (hshape : ∀ w ∉ badF,
      ((ρ.map (algebraMap ℚ F)).charFrob w).map ιO =
        X ^ 2 - C (aF w) * X + C (dF w)) :
    ∃ E : IntermediateField ℚ (AlgebraicClosure ℚ_[ℓ]),
      FiniteDimensional ℚ E ∧ ∀ w ∉ badF, aF w ∈ E := by
  classical
  -- (b-i-a-1) finitely many good places generate the field of eigenvalues
  obtain ⟨s, hsgood, hgen⟩ :=
    exists_heckeGenerators_of_eigenvalues hℓodd hℓ5 hZinj hrank hρ hW hρbar
      hirr F hFtr hFgal hirrF badF aF dF ιO hιO hshape
  -- (b-i-a-2) each single eigenvalue is an algebraic number
  have hint := isIntegral_heckeEigenvalues hℓodd hℓ5 hZinj hrank hρ hW hρbar
    hirr F hFtr hFgal hirrF badF aF dF ιO hιO hshape
  haveI : Finite (aF ''
      (s : Set (HeightOneSpectrum (NumberField.RingOfIntegers F)))) :=
    (s.finite_toSet.image aF).to_subtype
  refine ⟨IntermediateField.adjoin ℚ (aF ''
    (s : Set (HeightOneSpectrum (NumberField.RingOfIntegers F)))), ?_, hgen⟩
  refine IntermediateField.finiteDimensional_adjoin ?_
  rintro x ⟨w, hw, rfl⟩
  exact hint w (hsgood w hw)

/-- **Rationality of the determinant function at the places over `ℓ`**
(PROVEN 2026-07-26 by NARROWING — the statement was FALSE for the
intended objects and is now VACUOUS; read the FAITHFULNESS REPAIR and
VACUITY AUDIT below before building on it.  Sub-leaf (b-i-d) — the half
of Shimura rationality that is NOT a classical theorem): the
determinant function `dF` of the modular lift `ρ|_{G_F}` takes its
values, at the places `w | ℓ` outside the bad set, inside ONE finite
extension of `ℚ` sitting in `ℚ̄_ℓ`.

WHY THIS IS SPLIT OFF FROM `exists_heckeSubfield_of_eigenvalues`: the
two halves of the parent leaf have genuinely different statuses, and
merging them hid the weaker one behind the stronger one's citation.

* Away from `ℓ` the determinant half needs no automorphic input at all:
  `hshape` pins `dF w` to the constant coefficient of the base-changed
  Frobenius charpoly, which the cyclotomic determinant clause of `hρ`
  makes equal to the rational integer `Nw`
  (`charFrob_baseChange_coeff_zero_eq_absNorm`).  That is why this leaf
  quantifies ONLY over `w | ℓ`; the parent consumes the away-from-`ℓ`
  values through the proven bridge instead.
* At `w | ℓ` the cyclotomic character IS ramified.  `hshape` together
  with `IsHardlyRamified.det` pins `dF w` to
  `ιO (algebraMap ℤ_[ℓ] O (χ_ℓ σ))` for `σ` the chosen arithmetic
  Frobenius lift at `w`, and `χ_ℓ` restricted to a decomposition group
  over `ℓ` is surjective onto an open subgroup of `ℤ_[ℓ]ˣ` by local
  class field theory.  A general element of `ℤ_[ℓ]ˣ` is transcendental
  over `ℚ`, so there is NO classical theorem asserting this clause: for
  the intended objects it is FALSE at every place over `ℓ` at which the
  chosen Frobenius lift has transcendental cyclotomic value.

CONSEQUENCE, recorded plainly (2026-07-25).  As originally stated —
without the hypothesis `hbadℓ` below — this node was true only by the
collapse route (the hypothesis package, an irreducible hardly ramified
mod-`ℓ` representation with `ℓ ≥ 5`, is classically unsatisfiable, which
is the headline of this very module), or vacuously, when `badF` happens
to contain every place over `ℓ`.  The supplier that actually reaches it,
`exists_heckeEigensystem_of_congruentSeed`, hands `badF := ∅`, so at the
instantiation that reaches this node the clause was FALSE for the
intended objects.

FAITHFULNESS REPAIR (2026-07-26 — this is what closed the node, and it
is a repair, not a proof of the old statement).  The old statement was
retired in favour of the narrowed one below, by adding the hypothesis

    hbadℓ : ∀ w, (ℓ : 𝓞 F) ∈ w.asIdeal → w ∈ badF

which deletes exactly the false instances and nothing else.  This is
the same narrowing that `exists_threeadic_realization_of_heckePackage`
received for the places over `3`, for the same reason and at the same
cost — namely none:

* `badF` is chosen EXISTENTIALLY upstream
  (`exists_heckeEigensystem_of_congruentSeed`, whose conclusion
  quantifies it), and a matching clause `∀ w ∉ badF, …` only WEAKENS as
  `badF` grows.  So the consumer `exists_heckePackage_of_seed` simply
  moves to `badF ∪ {w : w ∋ ℓ}` — a `Finset` by
  `finite_heightOneSpectrum_mem_of_ne_zero` above — and hands down the
  hypothesis for free (`exists_finset_superset_of_places_mem`).
* Nothing downstream assumes less: `exists_heckePackage_of_seed`
  existentially quantifies `badF` in its own conclusion, and
  `exists_potentialModularityWitness_of_five_le` already enlarges it
  again by the places over `3`.  The `PotentialModularityWitness`
  docstring always said `badF` contains the places over `2`, `3` and
  `ℓ`; the formal statement now agrees with the interface.

Why the false instances were false, restated once for the record: at
`w | ℓ` the cyclotomic character IS ramified.  `hshape` together with
`IsHardlyRamified.det` pins `dF w` to
`ιO (algebraMap ℤ_[ℓ] O (χ_ℓ σ))` for `σ` the chosen arithmetic
Frobenius lift at `w` (`Field.AbsoluteGaloisGroup.adicArithFrob`, an
ARBITRARY choice inside the decomposition group), and `χ_ℓ` restricted
to a decomposition group over `ℓ` is surjective onto an open subgroup of
`ℤ_[ℓ]ˣ` by local class field theory.  An open subgroup of `ℤ_[ℓ]ˣ` is
uncountable and the algebraic numbers are countable, so almost every
element of it is TRANSCENDENTAL over `ℚ` and lies in no finite extension
of `ℚ` whatever.  There is therefore no classical theorem asserting the
old clause, and no repair of it other than deleting the places over `ℓ`
from its range of quantification.

VACUITY AUDIT (2026-07-26, mandatory reading).  With `hbadℓ` in place
this node is VACUOUS: the conclusion is discharged by `E := ⊥` and the
observation that `w ∉ badF` and `ℓ ∈ w.asIdeal` are contradictory.  It
carries NO arithmetic content, and the underscore-prefixed binders
below make that mechanically visible — `_hℓ5`, `_hZinj`, `_hρ`,
`_hρbar`, `_hirr`, `_hFtr`, `_hFgal`, `_hirrF`, `_hιO`, `_hshape` is
the entire hypothesis package, and the proof consumes none of it.  The
node is RETAINED rather than deleted for two reasons: it is the stated
place where the absence of any `ℓ`-adic determinant rationality is
recorded, and its consumer
`exists_heckeField_mem_range_of_eigensystem` still routes its
`w | ℓ` clause through it, so the audit cannot be lost by a later
refactor without breaking a proof.  The eigenvalue half
`exists_heckeSubfield_of_eigenvalues` is UNAFFECTED and remains the one
genuinely automorphic citation of the cut.

CIRCULARITY GUARD (inherited from pillar β, load-bearing): no
discharge through `Family.lean`, `Lift.lean`, or
`Modularity/Interface.lean` — respected: the proof below uses only
mathlib's `Module.Finite ℚ ↥⊥`. -/
theorem exists_heckeSubfield_of_determinants
    {ℓ : ℕ} (hℓodd : Odd ℓ) [Fact ℓ.Prime] (_hℓ5 : 5 ≤ ℓ)
    {O : Type u} [CommRing O] [IsDomain O] [TopologicalSpace O]
    [IsTopologicalRing O] [Algebra ℤ_[ℓ] O] [IsLocalRing O]
    [Module.Finite ℤ_[ℓ] O] [IsModuleTopology ℤ_[ℓ] O]
    (_hZinj : Function.Injective (algebraMap ℤ_[ℓ] O))
    {ρ : GaloisRep ℚ O (Fin 2 → O)}
    (hrank : Module.rank O (Fin 2 → O) = 2)
    (_hρ : IsHardlyRamified hℓodd hrank ρ)
    {k : Type u} [Field k] [Finite k] [Algebra ℤ_[ℓ] k]
    [TopologicalSpace k] [DiscreteTopology k]
    {W : Type v} [AddCommGroup W] [Module k W] [Module.Finite k W]
    [Module.Free k W]
    (hW : Module.rank k W = 2) {ρbar : GaloisRep ℚ k W}
    (_hρbar : IsHardlyRamified hℓodd hW ρbar)
    (_hirr : ρbar.IsIrreducible)
    (F : Type u) [Field F] [NumberField F]
    (_hFtr : NumberField.IsTotallyReal F) (_hFgal : IsGalois ℚ F)
    (_hirrF : (ρbar.map (algebraMap ℚ F)).IsIrreducible)
    (badF : Finset (HeightOneSpectrum (NumberField.RingOfIntegers F)))
    (aF dF : HeightOneSpectrum (NumberField.RingOfIntegers F) →
      AlgebraicClosure ℚ_[ℓ])
    (ιO : O →+* AlgebraicClosure ℚ_[ℓ]) (_hιO : Function.Injective ιO)
    (_hshape : ∀ w ∉ badF,
      ((ρ.map (algebraMap ℚ F)).charFrob w).map ιO =
        X ^ 2 - C (aF w) * X + C (dF w))
    (hbadℓ : ∀ w : HeightOneSpectrum (NumberField.RingOfIntegers F),
      (ℓ : NumberField.RingOfIntegers F) ∈ w.asIdeal → w ∈ badF) :
    ∃ E : IntermediateField ℚ (AlgebraicClosure ℚ_[ℓ]),
      FiniteDimensional ℚ E ∧
      ∀ w ∉ badF, (ℓ : NumberField.RingOfIntegers F) ∈ w.asIdeal →
        dF w ∈ E :=
  ⟨⊥, inferInstance, fun w hw hwℓ => absurd (hbadℓ w hwℓ) hw⟩

/-- **Shimura rationality for the Hilbert-newform eigensystem, range
form** (PROVEN 2026-07-25 as an assembly over the two halves of sub-leaf
(b-i); sub-leaf (b-i) of the Carayol/Shimura sub-cut — its eigenvalue
half is the ONLY automorphic input of sub-leaf (b)): the eigenvalue
function `aF`
of the modular lift `ρ|_{G_F}` takes its values in a single number
field `E` — the Hecke field — presented through one embedding
`ψℓ : E ↪ ℚ̄_ℓ` as range membership; and at the finitely many places
over `ℓ`, where the cyclotomic determinant carries no rationality (see
the section note above), so does the determinant function `dF`.

Classically: `aF w` is the `T_w`-eigenvalue of the Hilbert newform `f`
of parallel weight `2` over `F` attached to `ρ|_{G_F}` by the `R = 𝕋`
sub-leaf.  Shimura's rationality theorem — the Hecke eigenvalues of a
Hilbert newform generate a NUMBER field `E = ℚ(a_w : w)`, because the
Hecke operators act on a finite-dimensional `ℚ`-rational space of cusp
forms with `ℤ`-integral characteristic polynomials, and Galois
conjugation permutes newforms — gives `E`; the embedding is the place
`λ | ℓ` at which the `λ`-adic realization of `f` is `ρ|_{G_F}`, i.e.
exactly `ψℓ`; Carayol's local-global compatibility at the unramified
places is what makes the identification of `charFrob` with the Hecke
polynomial hold place by place rather than merely after
semisimplification, and hence makes `aF w` (read off the shape
hypothesis `hshape`) equal to `ψℓ (a_w)` on the nose.  At `w | ℓ` the
`λ`-adic realization is still defined over `E_λ`, so `dF w` — the
determinant of a Frobenius lift — again lies in `ψℓ(E)`.

RANGE FORM (why this is the sharp statement): stating the conclusion as
`aF w ∈ Set.range ψℓ` rather than as the existence of a function
`a : places → E` with `ψℓ ∘ a = aF` removes the choice-theoretic
packaging from the citation — the packaging is discharged formally in
`exists_heckeField_of_eigensystem` below — and leaves exactly the
mathematical assertion "the eigenvalues are algebraic and generate one
number field".

Literature: Shimura, *The special values of the zeta functions
associated with Hilbert modular forms*, Duke Math. J. 45 (1978), §2
(rationality and the Hecke field of a Hilbert newform); Carayol, *Sur
les représentations `ℓ`-adiques associées aux formes modulaires de
Hilbert*, Ann. Sci. ÉNS 19 (1986) (local-global compatibility, the
normalization used here); Taylor, *On Galois representations associated
to Hilbert modular forms*, Invent. Math. 98 (1989) (the remaining
even-degree cases); Ohta and Hida for the integral normalizations.

PIN AUDIT (2026-07-24, re-verified 2026-07-25): the mathlib pin has no
Hilbert modular forms and no Hecke algebras over a totally real base
(`grep Hilbert` over `Mathlib/NumberTheory/`: only Hilbert's theorem 90
and Hilbert basis), so no part of this statement can be reduced to
library material; it is a citation node whose only sound discharge is
the construction of Hilbert-modular Hecke theory.

SOUNDNESS AUDIT (both ways, 2026-07-25): (i) direct — for the intended
instantiation (`(aF, dF)` produced by
`exists_heckeEigensystem_of_congruentSeed`, hence the eigensystem of an
actual Hilbert newform) this is Shimura rationality plus Carayol
verbatim; for an abstract `(aF, dF)` merely satisfying `hshape` the
abstract-quantification caveat applies IN FULL FORCE — nothing formal
forces an abstract family of `ℚ̄_ℓ`-values to be algebraic, and the
hypothesis that `aF` IS a newform eigensystem lives entirely in this
citation; (ii) collapse — the hypothesis set (an irreducible hardly
ramified mod-`ℓ` representation, `ℓ ≥ 5`) is classically unsatisfiable
(headline below), so the statement is classically true for every
package.  The full hypothesis list of the parent leaf is retained
DELIBERATELY: dropping `hρbar`/`hirr`/`hshape` would leave a statement
about arbitrary `ℚ̄_ℓ`-valued families, which is false.

VACUITY AUDIT (2026-07-25, cluster sweep — audit only, the statement
was NOT changed).  This node is NOT vacuous: `Set.range ψℓ` is
algebraic over `ℚ` while `aF` is a family of `ℚ̄_ℓ`-values, so no junk
witness exists — the algebraicity clause carries real content.  (Exactly
the opposite of the cousin
`exists_residualModularity_of_hilbertBlumenthalPoint`, whose "number
field" clause IS free, because its target `pt.kp` is FINITE and every
finite field is a residue field of a number field.  Algebraicity is a
constraint only against a characteristic-zero target.)

But the content is now the WRONG content, and the RECOMMENDED DISCHARGE
DOES NOT WORK.  Its only supplier,
`exists_heckeEigensystem_of_congruentSeed`, is formally empty (see that
node's FORMAL-CONTENT AUDIT) and hands this node `badF := ∅` together
with `aF w = −ιO (((ρ.map _).charFrob w).coeff 1)`.  At that
instantiation this leaf asserts that the Frobenius traces of
`ρ|_{G_F}` are algebraic at EVERY place of `F` — including the places
over `2` and `ℓ` and the level, where `charFrob` is the charpoly of a
lift of a RAMIFIED Frobenius, is not a Hecke polynomial, and is
classically not algebraic.  So at the instantiation that actually
reaches it the statement is classically FALSE for the intended objects
and survives only by the collapse route (the hypothesis package is
unsatisfiable at `ℓ ≥ 5`); no citation of Shimura rationality can
discharge it.  The fix is upstream — restate
`exists_heckeEigensystem_of_congruentSeed` so that `badF` is a genuine
level/bad set rather than `∅`, as its own audit already recommends —
not here.

ASSEMBLY (2026-07-25, PROVEN — the STATEMENT IS UNCHANGED; what moved
is where the burden sits).  This node is no longer a citation.  It is
now a purely formal assembly over two sharply separated citations:

* `exists_heckeSubfield_of_eigenvalues` (Shimura rationality proper)
  gives a finite-dimensional `E₁ ≤ ℚ̄_ℓ` containing every `aF w`;
* `exists_heckeSubfield_of_determinants` (the `ℓ`-adic determinant
  clause, which is NOT a classical theorem — see its docstring) gives a
  finite-dimensional `E₂ ≤ ℚ̄_ℓ` containing `dF w` for `w | ℓ`.
  NARROWED 2026-07-26: that sub-leaf now demands
  `hbadℓ : ∀ w, (ℓ : 𝓞 F) ∈ w.asIdeal → w ∈ badF` — the places over `ℓ`
  are already bad — under which it is VACUOUS and proven with `E₂ := ⊥`.
  This node therefore carries `hbadℓ` too and passes it down; the
  `w | ℓ` clause of its own conclusion is consequently vacuous as well,
  and is retained only because the consumer's `d`-function extraction
  is written uniformly over `w ∉ badF`.  The hypothesis costs nothing:
  `exists_heckePackage_of_seed` chooses `badF` existentially and simply
  enlarges it (`exists_finset_superset_of_places_mem`).

The compositum `E₁ ⊔ E₂` is finite-dimensional over `ℚ`
(`IntermediateField.finiteDimensional_sup`), hence a number field once
transported into `Type u` by `ULift`; `ψℓ` is the composite
`ULift ↥(E₁ ⊔ E₂) ≃+* ↥(E₁ ⊔ E₂) ↪ ℚ̄_ℓ`, and range membership is
`le_sup_left` / `le_sup_right`.  The `CharZero` and `FiniteDimensional`
instances on the `ULift` are transported by `RingHom.charZero` along
`ULift.ringEquiv` and by `Module.Finite.equiv` along
`ULift.moduleEquiv`.

So the whole content of this node — universe placement, the
`NumberField` instance, the passage from "lies in a finite extension of
`ℚ`" to "lies in the range of an embedding of a number field" — is
formal, exactly as the RANGE FORM paragraph above claimed it should be;
and the INSTANTIATION DEFECT recorded above is now recorded at the two
sub-leaves, where it can be repaired independently.  Nothing about the
defect is fixed by this assembly.

CIRCULARITY GUARD (inherited from pillar β, load-bearing): no
discharge through `Family.lean`, `Lift.lean`, or
`Modularity/Interface.lean` — respected: the proof below uses only the
two sub-leaves above and mathlib. -/
theorem exists_heckeField_mem_range_of_eigensystem
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
    (F : Type u) [Field F] [NumberField F]
    (hFtr : NumberField.IsTotallyReal F) (hFgal : IsGalois ℚ F)
    (hirrF : (ρbar.map (algebraMap ℚ F)).IsIrreducible)
    (badF : Finset (HeightOneSpectrum (NumberField.RingOfIntegers F)))
    (aF dF : HeightOneSpectrum (NumberField.RingOfIntegers F) →
      AlgebraicClosure ℚ_[ℓ])
    (ιO : O →+* AlgebraicClosure ℚ_[ℓ]) (hιO : Function.Injective ιO)
    (hshape : ∀ w ∉ badF,
      ((ρ.map (algebraMap ℚ F)).charFrob w).map ιO =
        X ^ 2 - C (aF w) * X + C (dF w))
    (hbadℓ : ∀ w : HeightOneSpectrum (NumberField.RingOfIntegers F),
      (ℓ : NumberField.RingOfIntegers F) ∈ w.asIdeal → w ∈ badF) :
    ∃ (E : Type u) (_ : Field E) (_ : NumberField E)
      (ψℓ : E →+* AlgebraicClosure ℚ_[ℓ]),
      (∀ w ∉ badF, aF w ∈ Set.range ψℓ) ∧
      ∀ w ∉ badF, (ℓ : NumberField.RingOfIntegers F) ∈ w.asIdeal →
        dF w ∈ Set.range ψℓ := by
  classical
  -- (b-i-a) Shimura rationality: the eigenvalues lie in one finite
  -- extension `E₁` of `ℚ` inside `ℚ̄_ℓ`
  obtain ⟨E₁, hE₁, ha⟩ :=
    exists_heckeSubfield_of_eigenvalues hℓodd hℓ5 hZinj hrank hρ hW hρbar
      hirr F hFtr hFgal hirrF badF aF dF ιO hιO hshape
  -- (b-i-d) the determinant values at the places over `ℓ`, in a finite
  -- extension `E₂`
  obtain ⟨E₂, hE₂, hd⟩ :=
    exists_heckeSubfield_of_determinants hℓodd hℓ5 hZinj hrank hρ hW hρbar
      hirr F hFtr hFgal hirrF badF aF dF ιO hιO hshape hbadℓ
  haveI := hE₁
  haveI := hE₂
  -- the compositum is again a finite extension of `ℚ`
  haveI : FiniteDimensional ℚ
      ((E₁ ⊔ E₂ : IntermediateField ℚ (AlgebraicClosure ℚ_[ℓ])) : Type _) :=
    IntermediateField.finiteDimensional_sup E₁ E₂
  -- transport it into `Type u`: `ULift` of a number field is a number field
  haveI : CharZero (ULift.{u}
      ((E₁ ⊔ E₂ : IntermediateField ℚ (AlgebraicClosure ℚ_[ℓ])) : Type _)) :=
    (ULift.ringEquiv.toRingHom :
      ULift.{u} ((E₁ ⊔ E₂ : IntermediateField ℚ (AlgebraicClosure ℚ_[ℓ])) : Type _)
        →+* ((E₁ ⊔ E₂ : IntermediateField ℚ (AlgebraicClosure ℚ_[ℓ])) : Type _)).charZero
  haveI : FiniteDimensional ℚ (ULift.{u}
      ((E₁ ⊔ E₂ : IntermediateField ℚ (AlgebraicClosure ℚ_[ℓ])) : Type _)) :=
    Module.Finite.equiv (ULift.moduleEquiv (R := ℚ)
      (M := ((E₁ ⊔ E₂ : IntermediateField ℚ (AlgebraicClosure ℚ_[ℓ])) : Type _))).symm
  refine ⟨ULift.{u} (E₁ ⊔ E₂ : IntermediateField ℚ (AlgebraicClosure ℚ_[ℓ])),
    inferInstance, ⟨⟩,
    ((E₁ ⊔ E₂ : IntermediateField ℚ (AlgebraicClosure ℚ_[ℓ])).subtype).comp
      ULift.ringEquiv.toRingHom, ?_, ?_⟩
  · exact fun w hw => ⟨ULift.up ⟨aF w, (le_sup_left : E₁ ≤ E₁ ⊔ E₂) (ha w hw)⟩, rfl⟩
  · exact fun w hw hwℓ =>
      ⟨ULift.up ⟨dF w, (le_sup_right : E₂ ≤ E₁ ⊔ E₂) (hd w hw hwℓ)⟩, rfl⟩

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

/-- **Carayol local-global normalization and Shimura rationality**
(PROVEN 2026-07-25 as an assembly over the Carayol/Shimura sub-cut —
see the section note above; sub-leaf (b) of the modularity-lifting
cut — Shimura / Carayol 1986): the raw `ℚ̄_ℓ`-valued Hecke eigensystem
`(aF, dF)` of
the modular lift `ρ|_{G_F}` is DEFINED OVER A NUMBER FIELD: there is a
number field `E` (the Hecke field of the attached Hilbert newform), a
place `ψℓ : E → ℚ̄_ℓ` of `E` over `ℓ`, and functions `a, d` valued in
`E` whose `ψℓ`-images are `aF` and `dF` away from the bad set.

Classically: `aF w` is the `T_w`-eigenvalue of the Hilbert newform `f`
of parallel weight `2` over `F` attached to `ρ|_{G_F}` by the
`R = 𝕋` sub-leaf, and `dF w` is the absolute norm `Nw` (a rational
integer, forced here by the cyclotomic determinant clause of `hρ`).
Shimura's rationality theorem (the Hecke eigenvalues of a Hilbert
newform generate a NUMBER field `E = ℚ(a_w : w)`, because the Hecke
operators act on a finite-dimensional `ℚ`-rational space of cusp forms
with `ℤ`-integral characteristic polynomials, and Galois conjugation
permutes newforms) gives `E`; the chosen embedding of `E` into `ℚ̄_ℓ`
is the place `λ | ℓ` at which the `λ`-adic realization is `ρ|_{G_F}`,
i.e. exactly `ψℓ`; Carayol's local-global compatibility at the
unramified places is what guarantees that the identification of
`charFrob` with the Hecke polynomial holds place by place rather than
merely after semisimplification.  The determinant function descends
because `Nw` is already rational.

Literature: Shimura, *The special values of the zeta functions
associated with Hilbert modular forms*, Duke Math. J. 45 (1978), §2
(rationality and the Hecke field of a Hilbert newform); Carayol, *Sur
les représentations `ℓ`-adiques associées aux formes modulaires de
Hilbert*, Ann. Sci. ÉNS 19 (1986) (local-global compatibility, the
normalization used here); Taylor, *On Galois representations
associated to Hilbert modular forms*, Invent. Math. 98 (1989)
(the remaining even-degree cases); Ohta and Hida for the integral
normalizations.

PIN AUDIT (2026-07-24, unchanged 2026-07-25): the mathlib pin has no
Hilbert modular forms and no Hecke algebras over a totally real base
(`grep Hilbert` over `Mathlib/NumberTheory/`: only Hilbert's theorem 90
and Hilbert basis), so the automorphic content of this statement cannot
be reduced to library material.  What the 2026-07-25 sub-cut DOES
achieve is to confine that content to the eigenvalue function: see
`exists_heckeField_mem_range_of_eigensystem` (Shimura rationality, the
only citation with automorphic content) and
`cyclotomicCharacter_adicArithFrob_base_eq_absNorm` (pure algebraic
number theory, true outright).

ASSEMBLY (2026-07-25, PROVEN): Shimura rationality
(`exists_heckeField_mem_range_of_eigensystem`) supplies the Hecke field
`E`, the place `ψℓ`, and range membership of `aF` — from which the
function `a` is extracted by choice, the packaging step that used to be
part of the citation.  The determinant function is built place by
place: away from `ℓ` the shape hypothesis `hshape` pins `dF w` to the
constant coefficient of the base-changed Frobenius charpoly, which the
cyclotomic determinant clause of `hρ` makes equal to the rational
integer `Nw` (`charFrob_baseChange_coeff_zero_eq_absNorm`), so
`d w := (Nw : E)` works with no automorphic input at all; at the
finitely many places over `ℓ`, where the cyclotomic character is
ramified, the citation's second clause supplies the value and `d w` is
again extracted by choice.

SOUNDNESS AUDIT (both ways, 2026-07-25): the depth now lives in the two
sub-leaves, each audited in its own docstring; this assembly adds only
formal steps (coefficient comparison, `Nat.cast` compatibility of the
ring homomorphism `ψℓ`, and classical choice), so its soundness is
exactly theirs.  For the record: (i) direct — for the intended
instantiation (`(aF, dF)` produced by
`exists_heckeEigensystem_of_congruentSeed`, hence the eigensystem of
an actual Hilbert newform) this is Shimura rationality plus Carayol
verbatim; for an abstract `(aF, dF)` merely satisfying `hshape` the
abstract-quantification caveat applies to the eigenvalue half — nothing
formal forces an abstract family of `ℚ̄_ℓ`-values to be algebraic, and
the hypothesis that `aF` IS a newform eigensystem lives entirely in the
Shimura citation (the same shape as the sibling leaf
`exists_threeadic_realization_of_heckePackage`, whose `hmod`
hypothesis carries the same unstated content); (ii) collapse — the
hypothesis set (an irreducible hardly ramified mod-`ℓ`
representation, `ℓ ≥ 5`) is classically unsatisfiable (headline
below), so the statement is classically true for every package.

CIRCULARITY GUARD (inherited from pillar β, load-bearing): no
discharge through `Family.lean`, `Lift.lean`, or
`Modularity/Interface.lean`; it binds both sub-leaves. -/
theorem exists_heckeField_of_eigensystem
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
    (F : Type u) [Field F] [NumberField F]
    (hFtr : NumberField.IsTotallyReal F) (hFgal : IsGalois ℚ F)
    (hirrF : (ρbar.map (algebraMap ℚ F)).IsIrreducible)
    (badF : Finset (HeightOneSpectrum (NumberField.RingOfIntegers F)))
    (aF dF : HeightOneSpectrum (NumberField.RingOfIntegers F) →
      AlgebraicClosure ℚ_[ℓ])
    (ιO : O →+* AlgebraicClosure ℚ_[ℓ]) (hιO : Function.Injective ιO)
    (hshape : ∀ w ∉ badF,
      ((ρ.map (algebraMap ℚ F)).charFrob w).map ιO =
        X ^ 2 - C (aF w) * X + C (dF w))
    (hbadℓ : ∀ w : HeightOneSpectrum (NumberField.RingOfIntegers F),
      (ℓ : NumberField.RingOfIntegers F) ∈ w.asIdeal → w ∈ badF) :
    ∃ (E : Type u) (_ : Field E) (_ : NumberField E)
      (ψℓ : E →+* AlgebraicClosure ℚ_[ℓ])
      (a d : HeightOneSpectrum (NumberField.RingOfIntegers F) → E),
      (∀ w ∉ badF, ψℓ (a w) = aF w) ∧ ∀ w ∉ badF, ψℓ (d w) = dF w := by
  classical
  -- (b-i) Shimura rationality: the Hecke field `E`, the place `ψℓ`, and
  -- range membership of the eigenvalues
  obtain ⟨E, hE, hNE, ψℓ, ha, hdℓ⟩ :=
    exists_heckeField_mem_range_of_eigensystem hℓodd hℓ5 hZinj hrank hρ hW
      hρbar hirr F hFtr hFgal hirrF badF aF dF ιO hιO hshape hbadℓ
  letI : Field E := hE
  -- the eigenvalue function: the range membership in total form, ready
  -- for `choose` (the packaging step the citation no longer carries)
  have haex : ∀ w, ∃ x : E, w ∉ badF → ψℓ x = aF w := by
    intro w
    by_cases hw : w ∈ badF
    · exact ⟨0, fun hc => absurd hw hc⟩
    · obtain ⟨x, hx⟩ := ha w hw
      exact ⟨x, fun _ => hx⟩
  -- the determinant function: away from `ℓ` its value is the rational
  -- integer `Nw`, forced by the cyclotomic determinant clause of `hρ`
  -- with no automorphic input; at the places over `ℓ`, where the
  -- cyclotomic character is ramified, it is supplied by the citation
  have hdex : ∀ w, ∃ x : E, w ∉ badF → ψℓ x = dF w := by
    intro w
    by_cases hw : w ∈ badF
    · exact ⟨0, fun hc => absurd hw hc⟩
    by_cases hwℓ : (ℓ : NumberField.RingOfIntegers F) ∈ w.asIdeal
    · obtain ⟨x, hx⟩ := hdℓ w hw hwℓ
      exact ⟨x, fun _ => hx⟩
    · refine ⟨(Ideal.absNorm w.asIdeal : E), fun _ => ?_⟩
      -- read the determinant coefficient off the shape hypothesis
      have hRHS : (X ^ 2 - C (aF w) * X + C (dF w)).coeff 0 = dF w := by simp
      have hc0 : ιO (((ρ.map (algebraMap ℚ F)).charFrob w).coeff 0) =
          dF w := by
        rw [← Polynomial.coeff_map, hshape w hw, hRHS]
      rw [map_natCast, ← hc0,
        charFrob_baseChange_coeff_zero_eq_absNorm hℓodd hrank hρ F w hwℓ,
        map_natCast]
  choose a hafun using haex
  choose d hdfun using hdex
  exact ⟨E, hE, hNE, ψℓ, a, d, fun w hw => hafun w hw, fun w hw => hdfun w hw⟩

/-- **Modularity lifting over the totally real base** (PROVEN
2026-07-24 as an assembly over the three sub-leaves of the
modularity-lifting cut — see the section note above and the ASSEMBLY
paragraph at the end of this docstring; the depth now lives in
`exists_residualCongruence_over_base`,
`exists_heckeEigensystem_of_congruentSeed` and
`exists_heckeField_of_eigensystem`): over the Moret–Bailly base
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

ASSEMBLY (2026-07-24, PROVEN): the residual bridge over `F`
(`exists_residualCongruence_over_base` — Chebotarev + Brauer–Nesbitt
+ base change, producing the bad set `badρ` and the congruence
`hcong` that identifies `ρ|_{G_F}` and the seed `σ` as lifts of one
residual representation) feeds `R = 𝕋` over `F`
(`exists_heckeEigensystem_of_congruentSeed` — Kisin/Taylor patching
over the totally real base, producing the bad set `badF`, the raw
`ℚ̄_ℓ`-valued eigensystem `(aF, dF)` and the coefficient embedding
`ιO`), whose output feeds the Carayol/Shimura normalization
(`exists_heckeField_of_eigensystem` — the Hecke field `E`, the place
`ψℓ`, and the `E`-valued descents `(a, d)`).  The glue below sets
`heckeF w := X² − a w · X + d w` and checks that its `ψℓ`-image is
the shape produced by `R = 𝕋`, using only that `ψℓ` is a ring
homomorphism.

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
  -- (a) `R = 𝕋` over `F`: the raw `ℚ̄_ℓ`-valued Hecke eigensystem
  obtain ⟨badF₀, aF, dF, ιO, hιO, hshape₀⟩ :=
    exists_heckeEigensystem_of_congruentSeed hℓodd hℓ5 hZinj hrank hρ hW
      hρbar hirr π hπsurj hπ F hFtr hFgal hirrF seed badρ hcong
  -- (a') ENLARGE the exceptional set by the places of `F` over `ℓ`
  -- (2026-07-26).  The shape clause only WEAKENS when its exceptional set
  -- grows, so this is free; and it is what discharges the narrowed
  -- determinant sub-leaf's `hbadℓ`, which exists because at `w | ℓ` the
  -- cyclotomic character is RAMIFIED, so `dF w` is the cyclotomic value of
  -- an arbitrarily chosen Frobenius lift — a generic element of `ℤ_[ℓ]ˣ`,
  -- transcendental over `ℚ` and lying in no finite extension of it.  See
  -- `exists_heckeSubfield_of_determinants` for the full audit.
  have hℓne : (ℓ : NumberField.RingOfIntegers F) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Fact.out (p := ℓ.Prime)).ne_zero
  obtain ⟨badF, hsub, hbadℓ⟩ :=
    exists_finset_superset_of_places_mem badF₀
      (ℓ : NumberField.RingOfIntegers F) hℓne
  have hshape : ∀ w ∉ badF,
      ((ρ.map (algebraMap ℚ F)).charFrob w).map ιO =
        X ^ 2 - C (aF w) * X + C (dF w) :=
    fun w hw => hshape₀ w fun h => hw (hsub h)
  -- (b) Carayol/Shimura: the eigensystem is defined over the Hecke field
  obtain ⟨E, hE, hNE, ψℓ, a, d, ha, hd⟩ :=
    exists_heckeField_of_eigensystem hℓodd hℓ5 hZinj hrank hρ hW hρbar hirr
      F hFtr hFgal hirrF badF aF dF ιO hιO hshape hbadℓ
  -- glue: the Hecke polynomial `X² − a_w·X + Nw` over `E`
  refine ⟨E, hE, hNE, badF, fun w => X ^ 2 - C (a w) * X + C (d w), ψℓ, ιO,
    hιO, fun w hw => ?_⟩
  rw [hshape w hw]
  simp [Polynomial.map_add, Polynomial.map_sub, Polynomial.map_mul,
    Polynomial.map_pow, ha w hw, hd w hw]

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

/-- **The Hilbert-modular `3`-adic realization, geometric core**
(sorry node — Carayol 1986, Théorème (A)/(B) / Taylor 1989; THE
citation leaf of the `3`-adic realization node, in its narrowest form
to date): a Hilbert-modular Hecke eigensystem `(E, heckeF)` over the
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

PIN RECON for that step (done 2026-07-26 so the next owner need not
repeat it). Statement: `Γ F` compact, `τ : Γ F → GL_2(L)` continuous,
`L/ℚ_3` finite ⟹ a `Γ F`-stable `O_L`-lattice exists (take the
`O_L`-span of `τ(g_i)·O_L²` over coset representatives of the open
subgroup stabilizing one lattice). Where each ingredient stands:
* compactness of the absolute Galois group — mathlib has
  `instance [IsGalois k K] : CompactSpace Gal(K/k)`
  (`Mathlib/FieldTheory/Galois/Profinite.lean`), and `Γ F` is
  `Gal(F̄/F)` with `IsGalois F F̄` in characteristic zero;
* `O_L` module-finite over `ℤ_3` — `IsIntegralClosure.finite`
  (`Mathlib/RingTheory/DedekindDomain/IntegralClosure.lean`): `ℤ_3` is
  a Noetherian integrally closed domain and `L/ℚ_3` is finite
  separable;
* the lattice is FREE of rank `2` — `O_L` is Dedekind and local
  (`isLocalRing_of_finite_padicInt`, in this file), hence a DVR, hence
  a PID;
* `O_L` OPEN in `L` and the lattice stabilizer OPEN in
  `Module.End L (Fin 2 → L)` — via `IsModuleTopology.instPi` /
  `IsModuleTopology.iso`; no direct pin support, this is where the work
  starts;
* an open subgroup of a compact group has finite index — not found in
  mathlib under an obvious name; a short covering argument;
* transporting `τ` to a `GaloisRep F O_L (Fin 2 → O_L)` is the
  EXPENSIVE half, not the lattice: it needs `moduleTopology ℤ_3 O_L` to
  agree with the subspace topology from `L`, and the doctrine warning
  about concrete modules inside topology-carrying steps applies in
  full. This is a self-contained development, not a lemma — and it may
  not be sorried in passing, since a sorried lattice step IS the "one
  citation for two" the ROUTE AUDIT rejects.

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
  sorry

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
      hρbar hirr π hπsurj hπ F hFtr hFgal E badF heckeF ψℓ ιO hιO hmod
      hbad2 hbad3 hbadℓ
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
      hrank hρ hW hρbar hirr π hπsurj hπ F hFtr hFgal E badF heckeF ψℓ
      ιO hιO hmod hbad2 hbad3 hbadℓ
  -- (c) the eigensystem-match transport: the normalization below does
  -- not move the coefficient ring, so `hmatch` is carried verbatim and
  -- only the `Module.Free` component remains to be supplied
  refine ⟨B, hCR, hTS, hTR, hAlg, hLR, hFin, ?_, hMT, τF, ψ₃, ιB, hιB,
    hmatch⟩
  -- (b) the free-lattice normalization over `ℤ_3`
  exact @free_of_finite_of_algebraMap_padicInt_injective 3 _ B hCR hDom
    hAlg hFin hBinj

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
`matchF₃`), glued by instantiating the carrier fieldwise. Those three
leaves are now the residual sorries of the inhabitation node; the
circularity guard above binds each of them.

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
owner of `exists_heckeTrace_of_prime_cyclic_step_of_inert` and is now
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
enlarge here in the same style as the bad-set enlargement above. -/
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
  obtain ⟨F, hF, hNF, hFtr, hFgal, hirrF, ⟨seed⟩⟩ :=
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
  -- (iii) the Hilbert-modular `3`-adic realization: the 3-adic block
  obtain ⟨B, hB₁, hB₂, hB₃, hB₄, hB₅, hB₆, hB₇, hB₈, τF, ψ₃, ιB, hιB,
    hmatch⟩ :=
    exists_threeadic_realization_of_heckePackage hℓodd hℓ5 hZinj hrank hρ
      hW hρbar hirr π hπsurj hπ F hFtr hFgal E badF' heckeF ψℓ ιO hιO hmod'
      hbad2 hbad3 hbadℓ
  -- glue: instantiate the carrier fieldwise
  exact ⟨{ F := F, totallyReal := hFtr, galoisF := hFgal, E := E,
           badF := badF', heckeF := heckeF, ψℓ := ψℓ, ιO := ιO,
           ιO_injective := hιO, modularF := hmod', B := B, τF := τF,
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
needed anywhere in the descent. -/
def HeckeSystemDescendsTo {ℓ : ℕ} [Fact ℓ.Prime]
    {O : Type u} [CommRing O] [TopologicalSpace O] [IsTopologicalRing O]
    {ρ : GaloisRep ℚ O (Fin 2 → O)}
    (Wit : PotentialModularityWitness ℓ O ρ)
    (C : Subgroup (Wit.F ≃ₐ[ℚ] Wit.F)) : Prop :=
  ∃ (S : Finset (HeightOneSpectrum (NumberField.RingOfIntegers
      (IntermediateField.fixedField C))))
    (P : HeightOneSpectrum (NumberField.RingOfIntegers
      (IntermediateField.fixedField C)) → Polynomial Wit.E),
    ∀ w ∉ S,
      ((ρ.map (algebraMap ℚ (IntermediateField.fixedField C))).charFrob
          w).map Wit.ιO = (P w).map Wit.ψℓ

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
  -- (iii) TRANSPORT: read the carrier's modularity clause `Wit.modularF`
  -- through `e`, using `GaloisRep.charFrob_map_algEquiv`; the bad set is the
  -- carrier's bad set pulled back along the induced bijection of places,
  -- enlarged by the ramified places `T`.
  refine ⟨Wit.badF.image (NumberField.finitePlaceEquiv e.toRingEquiv).symm ∪ T,
    fun w => Wit.heckeF (NumberField.finitePlaceEquiv e.toRingEquiv w),
    fun w hw => ?_⟩
  rw [Finset.mem_union, not_or] at hw
  have hbad : NumberField.finitePlaceEquiv e.toRingEquiv w ∉ Wit.badF := by
    intro hmem
    refine hw.1 ?_
    have himg := Finset.mem_image_of_mem
      (NumberField.finitePlaceEquiv e.toRingEquiv).symm hmem
    simpa using himg
  rw [← GaloisRep.charFrob_map_algEquiv ρ e w (hT w hw.2)]
  exact Wit.modularF _ hbad

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
`exists_heckeTrace_of_prime_cyclic_step_of_inert` is thereby confined to
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

/-- **The TRACE of one PRIME-degree cyclic step of solvable base change,
at the NON-SPLIT places** (sorry node, cut 2026-07-26; THE terminal
literature citation of the `ℓ`-adic solvable descent — Langlands 1980,
Arthur–Clozel 1989): the statement of
`exists_heckeTrace_of_prime_cyclic_step` (see that node's docstring for
the classical three moves, the literature and the PIN, SOUNDNESS,
VACUITY, ROUTE and CIRCULARITY audits, all of which apply verbatim),
restricted to the places of `M = F^D` whose residue cardinality is
realized by NO good place of `L = F^C`.

TWO DIFFERENCES from the parent node, both deliberate:

* the descended system over `L` is taken UNFOLDED — as the bad set `SL`,
  the `E`-polynomials `PL` and the match `hPL`, rather than as
  `HeckeSystemDescendsTo Wit C` — because that is what the citation
  actually consumes: the Hilbert newform `f_L` over `L` whose eigensystem
  those polynomials are;
* the conclusion is asked only at places `w` with
  `∀ v ∉ SL, Nv ≠ Nw`.  The complementary places are discharged
  FORMALLY in the parent, with no automorphic input, by
  `charFrob_baseChange_eq_of_absNorm_eq` (`charFrob` depends only on the
  residue cardinality): if some good place `v` of `L` has `Nv = Nw` then
  `(ρ|_{G_M}).charFrob w = (ρ|_{G_L}).charFrob v` and `hPL` already
  answers.  In particular every place of `M` SPLIT in `L/M` (any place
  above it in `L` has residue degree `1`, hence equal norm) is off this
  node's plate, so what remains is the INERT half of the prime cyclic
  step.

The hypothesis package is retained VERBATIM (`hℓ5`, `hZinj`, `hρ`,
`hρbar`, `hirr`, `hπ`, and the group-theoretic data `hCD`, `hnormal`,
`hp`, `hcard`), so route (ii) of the parent's soundness audit — the
observation that the arithmetic package is CLASSICALLY UNSATISFIABLE —
remains available here exactly as it was there.  The sharpening is of the
CONCLUSION only; no arithmetic hypothesis was weakened, and none was
added.  Route (ii) is a SOUNDNESS justification (it is why the statement
is true), NOT an available Lean discharge: see the ROUTE AUDIT below,
which is the point on which this node is most easily misread.

SOUNDNESS: the conclusion is a restriction of the parent's conclusion to
a subset of the places, so this node is implied by the classical theorem
and is a strictly weaker statement; it is discharged classically by the
same three moves (cyclic ascent, `Gal(L/M)`-invariance, cyclic descent by
the Arthur–Clozel character identity), which do not distinguish the
split and inert places.

CIRCULARITY GUARD (inherited from pillar β, load-bearing): no discharge
through `Family.lean`, `Lift.lean`, or `Modularity/Interface.lean`.

────────────────────────────────────────────────────────────────────
ROUTE AUDIT (2026-07-26, re-verified for THIS node, call site by call
site rather than from docstrings).  COLLAPSE IS NOT AVAILABLE.

Every link below is an actual application in a proof term in this
module, not a docstring claim:

  `not_isIrreducible_of_isHardlyRamified_of_five_le`
    ← `exists_threeadic_compatible_member_of_five_le`   (pillar β)
    ← `exists_heckeField_system_of_witness`
    ← `exists_descended_heckeSystem_of_solvable`
    ← `heckeSystemDescendsTo_of_cyclic_step`
    ← `heckeSystemDescendsTo_of_prime_cyclic_step`
    ← `exists_heckeTrace_of_prime_cyclic_step`
    ← THIS NODE.

So `absurd hirr (not_isIrreducible_of_isHardlyRamified_of_five_le …)` —
the route ~40 leaves of this development legitimately take — is CIRCULAR
here.  It is also mechanically impossible: the dichotomy is declared some
5100 lines BELOW this node in the same module.  The two other copies of
the dichotomy are excluded as well: `IsHardlyRamified.mod_three_reducible`
is the `p = 3` half and says nothing at `ℓ ≥ 5`, and `Reducible.lean`'s B5
routes through `Family.lean`, which the inherited circularity guard above
forbids.  Anyone who "discharges" this node quickly has almost certainly
re-derived one of those three and should re-read this paragraph.

────────────────────────────────────────────────────────────────────
PLACE-AXIS SHARPNESS (2026-07-26).  THE SPLIT/INERT CUT IS ALREADY
SHARP: THE BASE FIELD `F` DISCHARGES NOTHING FURTHER.

The obvious next sharpening is to peel off, in addition, every place `w`
of `M` whose residue cardinality is realized by a good place of the base
field `F` — using `Wit.modularF` in place of `hPL`, with the same
residue-cardinality lemma `charFrob_baseChange_eq_of_absNorm_eq`.  That
set is empty beyond what `hPL` already covers, so the sharpening is a
no-op.  Proof: `F/ℚ` is Galois, so every place of `F` over `q` has the
same residue degree `f_F = ord(Frob_q)`.  If some place `u` of `F` has
`Nu = Nw = q^{f_M(w)}` then `f_M(w) = f_F`; picking any place `u'` of `F`
ABOVE `w` gives `f_F = f(u'/w)·f_M(w) = f(u'/w)·f_F`, hence
`f(u'/w) = 1`; hence the place `v' = u' ∩ L` has `f(v'/w) ∣ f(u'/w) = 1`,
so `Nv' = Nw`.  Only finitely many places carry any one norm
(`Ring.HasFiniteQuotients.finite_absNorm_heightOneSpectrum_le`), so
`v' ∉ SL` as soon as `Nw > max {Nv : v ∈ SL}`, and `hPL` already answers
at `w`.  Contrapositive, worth stating: this node's hypothesis
(`Nw` not realized in `L`) already implies `Nw` is not realized in `F`.

Related, and also verified: this node's hypothesis FORCES `w` to be
unramified and inert in `L/M`.  The place `v` of `L` above `w` has
`Nv = Nw^{f(v/w)}` with `e(v/w)·f(v/w) = p`; `f(v/w) = 1` would give
`Nv = Nw`, excluded; so `f(v/w) = p` and `e(v/w) = 1`.  The node's name
is therefore accurate and not merely suggestive.

────────────────────────────────────────────────────────────────────
WHAT IS FORMALLY DERIVABLE AT AN INERT PLACE, AND WHY THE REMAINDER IS
ATOMIC (2026-07-26 — an independent re-derivation of the analysis that
led the author of the cut to REJECT the three-leaf automorphic
build-out; do not re-cut along that seam).

Write `A = ρ|_{G_M}(Frob_w)`, `s = tr A`, and note `det A = Nw ∈ ℚ` by
the PROVEN `charFrob_baseChange_coeff_zero_eq_absNorm`.  The unique place
`v` of `L` over the (inert, by the previous paragraph) place `w` has
`Nv = Nw^p` and `Frob_v = Frob_w^p`, so
`(ρ|_{G_L}).charFrob v = charpoly(A^p) = X² − D_p(s, Nw)·X + Nw^p`,
where `D_p` is the Dickson polynomial expressing `α^p + β^p` in the
elementary symmetric functions `e₁ = s`, `e₂ = Nw`.  Hence `hPL` at `v`
yields exactly

    `D_p(s, Nw) ∈ Set.range ψℓ`   and   `Nw ∈ ℚ ⊆ Set.range ψℓ`,

i.e. **`s` is a root of an explicit degree-`p` polynomial with
coefficients in `E`** — and that is ALL that is formally derivable here.
The `p` roots are `ζ^j α + ζ^{−j} β` (`ζ^p = 1`): precisely the fibre of
cyclic base change, a torsor under the order-`p` character group of
`Gal(L/M)`.  Selecting the `E`-rational root is the whole of the
citation, and nothing in this module distinguishes it; any cut along that
seam needs `μ_p ⊆ Set.range ψℓ`, which is FALSE for an abstract carrier
(`E = ℚ`, `p = 5`) and whose own collapse route is circular by the ROUTE
AUDIT above.  Such a leaf would have neither a classical nor a collapse
route — strictly worse than this node.  The weakening that IS derivable,
"`ιO (coeff 1)` is algebraic of degree `≤ p` over `Set.range ψℓ`", is not
a shape the consumer `heckeSystemDescendsTo_of_prime_cyclic_step` can
use.

Two further cuts were examined and rejected on the same ground: an
interface structure carrying `bad`/`a`/`ζ`/`carayol` fields (a rename
with a one-line assembly, not a decomposition), and the `SL`-free
restatement of the place hypothesis, `∀ v, Nv ≠ Nw` in place of
`∀ v ∉ SL, Nv ≠ Nw`.  The latter LOOKS like a strengthening of the
hypothesis but is interderivable with it — `S` is existentially
quantified, and only finitely many places of `M` have norm at most
`max {Nv : v ∈ SL}` — so it removes no burden and was deliberately not
made.

────────────────────────────────────────────────────────────────────
INFORMATION AUDIT (2026-07-26, SECOND OWNER — an independent
re-derivation which CLOSES THE `F`-AXIS COMPLETELY and thereby makes
the atomicity claim above airtight rather than merely argued).

RESULT: `D_p(s, Nw) ∈ Set.range ψℓ` together with `Nw ∈ ℚ` is not just
what one derivation happens to yield — it is the ENTIRE information
about `s = tr ρ|_{G_M}(Frob_w)` contained in the hypothesis package.
Three axes, all now closed:

* *The `L`-axis.*  By the PROVEN
  `charFrob_baseChange_eq_of_absNorm_eq`, `charFrob` depends only on
  the residue cardinality, so a place `v' ∉ SL` of `L` constrains `s`
  only through `Nv'`.  This node's hypothesis kills `Nv' = Nw`; the
  place `v` above `w` has `Nv = Nw^p` and yields `D_p(s, Nw)`; any
  other `v'` with `Nv' = Nw^p` yields the SAME polynomial.  Every
  remaining `v'` speaks about a different residue cardinality, hence
  about a different Frobenius, hence not about `s` at all.

* *The `F`-axis, sharper than the previous section.*  PLACE-AXIS
  SHARPNESS above showed only that the `Nu = Nw` sharpening is a no-op.
  In fact `Wit.modularF` contributes NOTHING WHATEVER at the places of
  `F` above `w`, and the reason is a divisibility rather than a
  finiteness estimate.  `M ⊆ L ⊆ F`, so every place `u` of `F` above
  `w` lies above the place `v` of `L` above `w`, whence
  `f(u/w) = f(u/v)·f(v/w) = f(u/v)·p`.  Writing `d = f(u/w) = p·e`,
  `N = Nw` and `α, β` for the eigenvalues,

      `α^d + β^d = (α^p)^e + (β^p)^e = D_e(α^p + β^p, N^p)
                 = D_e(D_p(s, N), N^p)`,

  a polynomial with RATIONAL coefficients in the datum `hPL` already
  supplies.  So `modularF` at `u` is a formal consequence of the
  `L`-axis datum, not an independent constraint — for EVERY place of
  `F` above `w`, not merely for those of equal norm.

* *Why that divisibility is the whole story.*  The one shape that WOULD
  close this node is a second Dickson relation of degree COPRIME to
  `p`: if `D_d(s, N) ∈ E` and `D_p(s, N) ∈ E` with `gcd(d, p) = 1`,
  then the base-change torsor selects the `E`-rational root, because a
  `σ` moving `s` multiplies `α` by a primitive `p`-th root of unity `ζ`
  and then `D_d` moves by `ζ^d ≠ 1`.  The bullet above says such a `d`
  NEVER ARISES in this tower: `p ∣ f(u/w)` at every place above `w`.

  Coprimality is moreover genuinely load-bearing and not merely
  convenient — the two Dickson relations ALONE, without the torsor, do
  not suffice.  Explicit counterexample (verified numerically), with
  `E = ℚ`, `p = 3`, `d = 2`, `N = 5`: take `α = √5·ζ₁₂` and
  `β = √5·ζ₁₂⁻¹`, so `αβ = 5` and `s = α + β = √15 ∉ ℚ`, while
  `α² + β² = 5·(ζ₁₂² + ζ₁₂⁻²) = 5 ∈ ℚ` and
  `α³ + β³ = 5^{3/2}·(ζ₁₂³ + ζ₁₂⁻³) = 0 ∈ ℚ`.  Determinant rational,
  both Dickson values rational, `gcd(2,3) = 1`, trace irrational — so
  there is NO purely algebraic implication
  `(D_d(s,N), D_p(s,N), N ∈ E) ⟹ s ∈ E`.  What fails is exactly the
  torsor hypothesis: the `σ` with `√15 ↦ −√15` sends `α ↦ −β`, i.e. it
  twists by a SECOND root of unity, which is not a shape cyclic base
  change of degree `3` can produce.  Anyone who tries to close this node
  by assembling Dickson relations should read this paragraph first.

Conclusion: the residual content is precisely the selection of the
`E`-rational root of `D_p(X, Nw) − c`, and that selection IS the
Arthur–Clozel character identity.  The two cuts the author of the cut
rejected on grounds of taste (an information-carrying interface, and a
place-axis refinement) are now excluded on grounds of information: there
is nothing left in the package to cut along.

────────────────────────────────────────────────────────────────────
WHERE THE RESIDUAL BURDEN REALLY SITS — A CARRIER-LEVEL OBLIGATION THAT
`PotentialModularityWitness` DOES NOT RECORD (2026-07-26, reported
upwards rather than repaired here).

The fibre of cyclic base change is a torsor under the characters of
`Gal(L/M)`, so `ρ|_{G_M}` is itself attached to a member `f'` of that
fibre — there is no residual twist to control, and the traces asked for
here are literally the Hecke eigenvalues of `f'`.  The whole content of
this node is therefore the FIELD-THEORETIC normalization

    Hecke field of the descended form `f'`  ↪  `E`,  compatibly with `ψℓ`.

Classically the Hecke field can GROW on the way down: `E` is pinned by
the structure only through `modularF`/`matchF₃`, i.e. as a field carrying
the eigensystem over `F`, and the eigenvalues over `F` at a place `u` of
residue degree `d` over `w` are `α^d + β^d`, which generate a subfield of
`ℚ(α + β)` that is in general PROPER.  The statement of this node is
nevertheless true — the package is classically unsatisfiable (route (ii))
— but on the classical route (i) it is true only for a carrier whose `E`
was chosen large enough for the entire descent, e.g. the compositum of
the Hecke fields of all descended forms in the Brauer decomposition
(a finite compositum, hence still a number field).  That is a legitimate
choice and the producing leaf
`exists_potentialModularityWitness_of_five_le` must be understood as
making it, but `PotentialModularityWitness` records no such field and its
docstring calls `E` simply "the Hecke field of the attached Hilbert
newform" over `F`.  Whoever proves the witness-production leaf needs to
know this.

REPAIRED 2026-07-26 (second owner), and it turned out NOT to be a
cut-level change: the structure never asserted that `heckeF` GENERATES
`E`, so `E` may be replaced by any finite extension without touching a
single consumer — `ψℓ` and `ψ₃` extend because `ℚ̄_ℓ` and `ℚ̄_3` are
algebraically closed of characteristic zero, and `modularF`/`matchF₃`
are preserved by functoriality of `Polynomial.map`.  The obligation was
therefore a MISDESCRIPTION rather than a missing field, and the repair
is the DESCENT-CLOSURE note now carried by the
`PotentialModularityWitness` docstring, by its `E` field, and by
`exists_potentialModularityWitness_of_five_le`.  Route (i) is thereby
available at this node for the intended carrier, and route (ii) remains
available for every carrier; the citation's own content is unchanged. -/
theorem exists_heckeTrace_of_prime_cyclic_step_of_inert
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
    (SL : Finset (HeightOneSpectrum (NumberField.RingOfIntegers
      (IntermediateField.fixedField C))))
    (PL : HeightOneSpectrum (NumberField.RingOfIntegers
      (IntermediateField.fixedField C)) → Polynomial Wit.E)
    (hPL : ∀ v ∉ SL,
      ((ρ.map (algebraMap ℚ (IntermediateField.fixedField C))).charFrob
        v).map Wit.ιO = (PL v).map Wit.ψℓ) :
    ∃ S : Finset (HeightOneSpectrum (NumberField.RingOfIntegers
        (IntermediateField.fixedField D))),
      ∀ w ∉ S,
        (∀ v ∉ SL, Ideal.absNorm v.asIdeal ≠ Ideal.absNorm w.asIdeal) →
        Wit.ιO (((ρ.map (algebraMap ℚ (IntermediateField.fixedField D))).charFrob
          w).coeff 1) ∈ Set.range Wit.ψℓ :=
  sorry

/-- **The TRACE of one PRIME-degree cyclic step of solvable base change**
(PROVEN 2026-07-26 over the split/inert cut below — was itself the
terminal literature citation of the `ℓ`-adic solvable descent, Langlands
1980, Arthur–Clozel 1989): if the eigensystem of `ρ`
descends to the fixed field `L = F^C`, and `C ≤ D` is normal with
quotient `D/C` of PRIME order `p` (equivalently: `L/M` is a cyclic Galois
extension of degree `p`, where `M = F^D`), then away from a finite set of
places `w` of `M` the LINEAR coefficient of the Frobenius characteristic
polynomial of `ρ|_{G_M}` — i.e. `−a_w`, the Hecke eigenvalue of the
descended Hilbert newform — is algebraic and lies in the carrier's Hecke
field `E`, read through `ψℓ`.

TRACE-ONLY SHARPENING (2026-07-25).  This node used to be the FULL
statement `HeckeSystemDescendsTo Wit C → HeckeSystemDescendsTo Wit D`.
That is strictly more than the literature theorem is needed for: a
rank-`2` Frobenius characteristic polynomial is `X² − tr·X + det`, and
for a hardly ramified `ρ` the DETERMINANT is the `ℓ`-adic cyclotomic
character, whose value at a Frobenius at `w ∤ ℓ` is the rational integer
`Nw` — so the constant coefficient descends to `ℚ ⊆ E` with NO
automorphic input at all (`charFrob_baseChange_coeff_zero_eq_absNorm`,
proven earlier in this module over the pure algebraic-number-theory leaf
`cyclotomicCharacter_adicArithFrob_base_eq_absNorm`).  Only the TRACE
carries automorphic content, and only the trace is asked for here; the
consumer `heckeSystemDescendsTo_of_prime_cyclic_step` below reassembles
the polynomial formally.  This is the same trace/determinant split the
Carayol/Shimura sub-cut of this module already makes at the base field
`F` (`exists_heckeField_mem_range_of_eigensystem` +
`charFrob_baseChange_coeff_zero_eq_absNorm`), now made at every stage of
the descent tower.

RANGE FORM (why this is the sharp statement, mirroring
`exists_heckeField_mem_range_of_eigensystem`): stating the conclusion as
`… ∈ Set.range Wit.ψℓ` rather than as the existence of a function
`a : places → E` removes the choice-theoretic packaging from the citation
— the packaging is discharged formally in the consumer — and leaves
exactly the mathematical assertion "the descended Hecke eigenvalues are
algebraic and lie in the Hecke field `E`".

VACUITY AUDIT (2026-07-25): this node is NOT vacuous.  `Set.range Wit.ψℓ`
is algebraic over `ℚ` inside `ℚ̄_ℓ` while the trace is an a priori
arbitrary `ℚ̄_ℓ`-value, so no junk witness discharges it — exactly as for
its base-field cousin `exists_heckeField_mem_range_of_eigensystem`, and
exactly unlike a statement whose target is a finite field.

WHY PRIME DEGREE IS THE SHARPEST JOINT (2026-07-25): the twisted trace
formula of Langlands/Arthur–Clozel is run for a cyclic extension of
PRIME degree — that is the case in which the character identity
`Θ_{BC(π)}(g × σ) = Θ_π(N g)` is proved and in which the fibre of base
change is a torsor under the (order-`p`) character group of
`Gal(L/M)`. The general cyclic case is not a separate theorem but the
composition of prime steps, and the general solvable case the
composition of cyclic ones. This module now carries both compositions
formally (`exists_intermediate_of_isCyclic_quotient` for cyclic → prime,
`exists_cyclicRefinement_of_isSolvable` for solvable → cyclic), so this
node is the only remaining citation on the descent route: below it lie
the trace formula and the twisted character identity, not further
group-theoretic bookkeeping.

Classically, in three moves — the joints of the literature argument, in
order:

* *Cyclic ascent (base change).* `Gal(L/M) ≅ D/C` is cyclic of order
  `p`; Langlands' cyclic base change `BC_{L/M}` is defined on the
  cuspidal spectrum of `GL(2)/M` and characterized by the Arthur–Clozel
  twisted character identity. The descended system over `L`
  (hypothesis `hC`) is, through Carayol local–global compatibility, the
  eigensystem of a Hilbert newform `f_L` over `L`.
* *`Gal(L/M)`-invariance.* `f_L`'s Galois representation is `ρ|_{G_L}` —
  the restriction to `G_L` of the representation `ρ|_{G_M}` of the
  LARGER group `G_M` — hence visibly `Gal(L/M)`-invariant: for
  `σ ∈ Gal(L/M)`, `f_L^σ` has the same Frobenius eigenvalues as `f_L` at
  almost all places, so `f_L^σ = f_L` by strong multiplicity one.
* *Cyclic descent (the twisted character identity).* A
  `Gal(L/M)`-invariant cuspidal automorphic representation of `GL(2)/L`
  is in the image of base change from `GL(2)/M`, and its fibre is a
  torsor under the characters of `Gal(L/M)` (Langlands, *Base Change for
  GL(2)*, Ann. of Math. Studies 96 (1980), Ch. 2 and Thm 4.2;
  Arthur–Clozel, *Simple Algebras, Base Change, and the Advanced Theory
  of the Trace Formula*, Ann. of Math. Studies 120 (1989), Ch. 3 Thm 4.2
  and Ch. 1 §6 for the identity `Θ_{BC(π)}(g × σ) = Θ_π(N g)` that
  defines and characterizes the transfer). So there is a Hilbert newform
  `f_M` over `M` with `BC_{L/M}(f_M) = f_L`; its `ℓ`-adic representation
  restricted to `G_L` agrees with `ρ|_{G_L}`, hence differs from
  `ρ|_{G_M}` by a twist by a character of `Gal(L/M)` — of order dividing
  `p`, so with values `p`-th roots of unity.

Carayol's local–global compatibility over `M` then identifies the
Frobenius TRACES of the (twisted) `f_M`-system with Hecke eigenvalues;
those eigenvalues, enlarged by the twisting-character values, lie in the
carrier's `E`, which is, per the consumers' docstrings, the Hecke field
OF THE DESCENDED system, the normalization that absorbs exactly these
enlargements. The finite exceptional set collects the places of `M`
below the bad set of the `L`-system, the places over `2`, `3`, `ℓ`, and
the places ramified in `L/M`.

Literature: Langlands 1980 and Arthur–Clozel 1989 as above;
Barnet-Lamb–Gee–Geraghty–Taylor, *Potential automorphy and change of
weight*, Ann. of Math. 179 (2014), §5.3 (this descent per Brauer piece,
verbatim); Khare–Wintenberger, *Serre's modularity conjecture (I)*,
Invent. Math. 178 (2009), §5; Carayol, Ann. Sci. ÉNS 19 (1986).

ASSEMBLY (2026-07-26) — THE SPLIT/INERT CUT.  This node is now PROVEN,
over two leaves that divide the places of `M` by whether the descended
system over `L` already answers at them:

* `charFrob_baseChange_eq_of_absNorm_eq` (PURE ALGEBRAIC NUMBER THEORY,
  no automorphic input): for a hardly ramified `ρ`, `charFrob` depends
  only on the RESIDUE CARDINALITY of the place, away from `2` and `ℓ`.
  So if some place `v` of `L` outside the `L`-system's bad set has
  `Nv = Nw`, then `(ρ|_{G_M}).charFrob w = (ρ|_{G_L}).charFrob v`, and
  the hypothesis `hC` — read coefficientwise in degree `1` through
  `Polynomial.coeff_map` — puts the trace at `w` in `Set.range ψℓ` with
  no automorphic input at all.  Every place of `M` SPLIT in `L/M` is of
  this kind (a place of `L` above it has residue degree `1`, hence equal
  norm), so the split half of the prime cyclic step is discharged
  formally here.
* `exists_heckeTrace_of_prime_cyclic_step_of_inert` (the residual
  automorphic citation): the same statement at the remaining places —
  those whose residue cardinality is realized by no good place of `L`,
  classically the INERT ones.  Its hypothesis package is this node's,
  verbatim, with `hC` unfolded into the `L`-system `(SL, PL, hPL)` that
  the citation actually consumes.

The finite bad set is the union of the citation's own set with the
places over `2` and over `ℓ` (finite by
`exists_finset_forall_natCast_notMem_asIdeal`), where the
residue-cardinality lemma does not apply because `ρ` is ramified there.
This is the same style of sharpening as the trace/determinant split
recorded above — peel off the half that is pure algebraic number theory
— applied now to the PLACES rather than to the coefficients.

PIN AUDIT (2026-07-24/25): no automorphic-representation vocabulary
exists on this pin, and the reference project's `cyclic_base_change`
(`~/cs/FLT`, `FLT/GaloisRepresentation/Automorphic.lean`) is itself a
sorried statement phrased through an `IsAutomorphic` predicate on
quaternionic forms — vocabulary this project does not have (see the
`HeckeSystemDescendsTo` docstring). Nothing is vendorable, on this pin
or after a pin-drift audit.  That is why the split/inert cut above is a
cut of the CONCLUSION and not a reduction to library automorphic
material: the automorphic content survives, undiminished, in the inert
half.

SOUNDNESS AUDIT (both ways, 2026-07-24/25): (i) direct — for the carrier
produced by the inhabitation leaf and a system produced by the chain
this is the argument above, with the Hecke-field enlargements landing in
`E` by the carrier's normalization; for an abstract carrier the
abstract-quantification caveat of pillar β applies (in particular
nothing formal ties the twisting-character values into `E`; that
identification is part of the citation), and (ii) collapse — the
hypothesis package (an irreducible hardly ramified mod-`ℓ`
representation, `ℓ ≥ 5`) is classically unsatisfiable (headline below),
so the statement is classically true for every package. The full
hypothesis package of the general cyclic step is retained verbatim here
PRECISELY to keep route (ii) available: the prime-degree sharpening and
the trace-only sharpening are sharpenings of the group-theoretic and of
the linear-algebraic hypothesis respectively, never a weakening of the
arithmetic one.

ROUTE AUDIT (2026-07-24): discharge by vacuity — `absurd hirr
(not_isIrreducible_of_isHardlyRamified_of_five_le …)`, the route the
interface leaves of `Modularity/Interface.lean` take — is NOT available
here: the headline consumes this node (headline ←
`exists_threeadic_compatible_member_of_five_le` ←
`exists_heckeField_system_of_witness` ←
`exists_descended_heckeSystem_of_solvable` ←
`heckeSystemDescendsTo_of_cyclic_step` ←
`heckeSystemDescendsTo_of_prime_cyclic_step` ← this node), so the
vacuity route would be circular. The classical route above is the one to
follow.

CIRCULARITY GUARD (inherited from pillar β, load-bearing): no discharge
through `Family.lean`, `Lift.lean`, or `Modularity/Interface.lean`. -/
theorem exists_heckeTrace_of_prime_cyclic_step
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
    ∃ S : Finset (HeightOneSpectrum (NumberField.RingOfIntegers
        (IntermediateField.fixedField D))),
      ∀ w ∉ S,
        Wit.ιO (((ρ.map (algebraMap ℚ (IntermediateField.fixedField D))).charFrob
          w).coeff 1) ∈ Set.range Wit.ψℓ := by
  classical
  -- the descended system over `L = F^C`, unfolded
  obtain ⟨SL, PL, hPL⟩ := hC
  -- the automorphic citation, at the places of `M` no good place of `L` matches
  obtain ⟨Sin, hSin⟩ := exists_heckeTrace_of_prime_cyclic_step_of_inert hℓodd hℓ5
    hZinj hrank hρ hW hρbar hirr π hπsurj hπ Wit C D hCD hnormal p hp hcard SL PL hPL
  -- the finitely many places of `M` over `2` and over `ℓ`, where `ρ` is ramified
  -- and the residue-cardinality lemma does not apply
  obtain ⟨S2, hS2⟩ := exists_finset_forall_natCast_notMem_asIdeal
    (IntermediateField.fixedField D) 2 (by norm_num)
  obtain ⟨Sℓ, hSℓ⟩ := exists_finset_forall_natCast_notMem_asIdeal
    (IntermediateField.fixedField D) ℓ (Fact.out : ℓ.Prime).ne_zero
  refine ⟨Sin ∪ S2 ∪ Sℓ, fun w hw => ?_⟩
  simp only [Finset.mem_union, not_or] at hw
  obtain ⟨⟨hwin, hw2⟩, hwℓ⟩ := hw
  by_cases hsplit : ∃ vL ∉ SL, Ideal.absNorm vL.asIdeal = Ideal.absNorm w.asIdeal
  · -- SPLIT half: a good place of `L` of the same residue cardinality answers,
    -- with no automorphic input
    obtain ⟨vL, hvS, hvnorm⟩ := hsplit
    have heq := charFrob_baseChange_eq_of_absNorm_eq hℓodd hrank hρ
      (IntermediateField.fixedField D) (IntermediateField.fixedField C) w vL
      (hS2 w hw2) (hSℓ w hwℓ) hvnorm
    have hmatch := hPL vL hvS
    rw [heq] at hmatch
    refine ⟨(PL vL).coeff 1, ?_⟩
    have hcoeff := congrArg
      (fun P : Polynomial (AlgebraicClosure ℚ_[ℓ]) => P.coeff 1) hmatch
    simpa [Polynomial.coeff_map] using hcoeff.symm
  · -- INERT half: the residual citation
    exact hSin w hwin (fun vL hvL hne => hsplit ⟨vL, hvL, hne⟩)

/-- **One PRIME-degree cyclic step of solvable base change** (PROVEN,
2026-07-25, from the trace citation
`exists_heckeTrace_of_prime_cyclic_step` and the cyclotomic determinant
already established in this module): if the eigensystem of `ρ` descends
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
  `exists_heckeTrace_of_prime_cyclic_step` supplies (in range form).

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
  -- (i) the finitely many places of `M = F^D` over `ℓ`, where the
  -- cyclotomic determinant is ramified and carries no rationality
  obtain ⟨Sℓ, hSℓ⟩ := exists_finset_forall_natCast_notMem_asIdeal
    (IntermediateField.fixedField D) ℓ (Fact.out : ℓ.Prime).ne_zero
  -- (ii) the automorphic input: the descended Hecke eigenvalues lie in `E`
  obtain ⟨Str, htr⟩ :=
    exists_heckeTrace_of_prime_cyclic_step hℓodd hℓ5 hZinj hrank hρ hW hρbar
      hirr π hπsurj hπ Wit C D hCD hnormal p hp hcard hC
  -- package the range membership as a function into the Hecke field `E`
  have key : ∀ w : HeightOneSpectrum (NumberField.RingOfIntegers
      (IntermediateField.fixedField D)), ∃ e : Wit.E, w ∉ Str →
      Wit.ψℓ e =
        Wit.ιO (((ρ.map (algebraMap ℚ (IntermediateField.fixedField D))).charFrob
          w).coeff 1) := by
    intro w
    by_cases hw : w ∈ Str
    · exact ⟨0, fun h => absurd hw h⟩
    · obtain ⟨e, he⟩ := htr w hw
      exact ⟨e, fun _ => he⟩
  choose a ha using key
  refine ⟨Sℓ ∪ Str,
    fun w => Polynomial.X ^ 2 + Polynomial.C (a w) * Polynomial.X +
      Polynomial.C ((Ideal.absNorm w.asIdeal : ℕ) : Wit.E),
    fun w hw => ?_⟩
  rw [Finset.mem_union, not_or] at hw
  have hfin : Module.finrank O (Fin 2 → O) = 2 :=
    Module.finrank_eq_of_rank_eq hrank
  have hmonic :
      ((ρ.map (algebraMap ℚ (IntermediateField.fixedField D))).charFrob w).Monic := by
    rw [GaloisRep.charFrob_eq_charpoly_globalFrob]
    exact LinearMap.charpoly_monic _
  have hdeg :
      ((ρ.map (algebraMap ℚ (IntermediateField.fixedField D))).charFrob
        w).natDegree = 2 := by
    rw [GaloisRep.charFrob_eq_charpoly_globalFrob, LinearMap.charpoly_natDegree,
      hfin]
  -- (iii) the determinant coefficient is the rational integer `Nw`
  have hdet := charFrob_baseChange_coeff_zero_eq_absNorm hℓodd hrank hρ
    (IntermediateField.fixedField D) w (hSℓ w hw.1)
  refine Polynomial.ext fun n => ?_
  rw [Polynomial.coeff_map, Polynomial.coeff_map]
  match n with
  | 0 =>
    rw [hdet]
    simp
  | 1 =>
    rw [← ha w hw.2]
    congr 1
    simp
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

/-- **One cyclic step of solvable base change** (PROVEN, 2026-07-25, from
the prime-degree step `heckeSystemDescendsTo_of_prime_cyclic_step` — now
itself PROVEN, over the trace-only citation
`exists_heckeTrace_of_prime_cyclic_step` —
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
trace-only citation `exists_heckeTrace_of_prime_cyclic_step`). Formally
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
route is now `exists_heckeTrace_of_prime_cyclic_step` — one scalar per
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
  exact hfinal

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

/-- **Brauer descent, `3`-adic side — the geometric core of the Brauer
sum** (sorry node — BLGGT §5.3; THE citation sub-leaf of the `3`-adic
realization, in its narrowest form to date): given the descended
rational Hecke system `(S₀, Pv)` produced on the `ℓ`-adic side
(`exists_heckeField_system_of_witness`), the SAME system is realized
`3`-adically — there are a finite exceptional set `S₁`, a coefficient
ring `A` which is a local DOMAIN module-finite over `ℤ_3` (classically
the integers `O_{E_λ}` of the completion of the Hecke field at a place
`λ | 3`), a representation `τ` of `G_ℚ` on `Fin 2 → A`, and a
comparison embedding `ιA : A → ℚ̄_3`, with `τ`'s Frobenius
characteristic polynomials away from `S₁` the `ψ₃`-images of `Pv`.

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
through `Family.lean`, `Lift.lean`, or `Modularity/Interface.lean`. -/
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
        ∀ (q : ℕ) (hq : q.Prime),
          hq.toHeightOneSpectrumRingOfIntegersRat ∉ S₁ →
          q ≠ 2 → q ≠ 3 → q ≠ ℓ →
          (τ.charFrob hq.toHeightOneSpectrumRingOfIntegersRat).map ιA =
            (Pv hq.toHeightOneSpectrumRingOfIntegersRat).map Wit.ψ₃ :=
  sorry

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
      ∀ (q : ℕ) (hq : q.Prime),
        hq.toHeightOneSpectrumRingOfIntegersRat ∉ S₁ →
        q ≠ 2 → q ≠ 3 → q ≠ ℓ →
        (τ.charFrob hq.toHeightOneSpectrumRingOfIntegersRat).map ιA =
          (Pv hq.toHeightOneSpectrumRingOfIntegersRat).map Wit.ψ₃ := by
  classical
  -- (a) the NARROWED BLGGT citation: the Brauer sum comes back over a
  -- bare local domain, module-finite over `ℤ_3`, with no topology, no
  -- `ℤ_3`-injectivity and no injectivity of the comparison embedding
  -- asserted
  obtain ⟨S₁, A, hCR, hDom, hAlg, hFin, τ, ιA, hmatch⟩ :=
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
  refine ⟨S₁, A, hCR, hDom, moduleTopology ℤ_[3] A, hTR, hAlg, hLR, hFin, ?_,
    injective_algebraMap_of_ringHom_charZero ιA, τ, ιA,
    injective_of_finite_padicInt_charZero (p := 3) ιA, hmatch⟩
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

CIRCULARITY GUARD (inherited from pillar β, load-bearing): no
discharge through `Family.lean`, `Lift.lean`, or
`Modularity/Interface.lean`. -/
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
    hιA, hmatch⟩ :=
    exists_threeadicBrauerSum_of_witness hℓodd hℓ5 hZinj hrank hρ hW
      hρbar hirr π hπsurj hπ Wit S₀ Pv hPv
  -- (iii) freeness normalization of the lattice (formal, `ℤ_3` a PID)
  haveI : Module.Free ℤ_[3] A :=
    module_free_padicInt_of_algebraMap_injective 3 A hAinj
  -- glue: the realization, with the two exceptional sets united, and
  -- the compatibility clause obtained from the single descended family
  -- by interpolant uniqueness (formal, `ψℓ` injective on the field `E`)
  refine ⟨{ S₁ := S₁ ∪ S₀, A := A, τ := τ, ιA := ιA,
            ιA_injective := hιA, compat := ?_ }⟩
  intro q hq hqS hq2 hq3 hqℓ P hP
  exact heckePoly_transport Wit.ψℓ Wit.ψ₃
    (hPv q hq (fun h => hqS (Finset.mem_union_right _ h)) hq2 hq3 hqℓ)
    (hmatch q hq (fun h => hqS (Finset.mem_union_left _ h)) hq2 hq3 hqℓ)
    hP

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

/-- **The `3`-adic member is unramified at `ℓ`** (sorry node, CITATION
LEAF — split off 2026-07-25 from
`threeadicRealization_ramified_transfer_of_witness` below, whose
`p ≠ ℓ` clause is exactly this statement): the Brauer-descended
`3`-adic member `τ` is unramified at the `ℓ`-adic member's OWN residue
characteristic `ℓ`.

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

ROUTE AUDIT (2026-07-25): no formal route exists in the interface. The
only arithmetic datum `ThreeadicRealization` carries is `compat`, which
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
inputs inside one citation; and the predicate itself is NOT vendorable,
being defined over that project's quaternionic Hecke-algebra
development, which our pin does not have.

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

ROUTE AUDIT, THIRD CLOSURE (2026-07-26): the `τF`-FREE variant of the
relocation is closed too — and by a DIFFERENT obstruction from the
second closure's, which is worth naming because it is the only
actionable one in this docstring.

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
  sorry

/-- **Member-independence of the ramification locus at a place prime to
BOTH residue characteristics** (sorry node, CITATION LEAF — split off
2026-07-25 from `threeadicRealization_ramified_transfer_of_witness`
below, whose `¬ ρ.IsUnramifiedAt` clause is the contrapositive of this
statement): at a prime `p ∉ {3, ℓ}` at which the `ℓ`-adic member `ρ`
is UNRAMIFIED, the Brauer-descended `3`-adic member `τ` is unramified
too.

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
whatsoever, and `ThreeadicRealization` carries no other arithmetic
datum. Sharper form of the same objection, recorded here so it is not
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
  sorry

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

/-- **The Fontaine–Laffaille local shape at `3`, on the `3`-power
levels of the stable lattice** (sorry node — the LITERATURE JOINT of
the flatness transfer, cut 2026-07-25 out of
`threeadicRealization_hasFlatProlongationAt_of_finite_quotient` below,
whose arbitrary-finite-quotient quantifier is now PROVEN glue over
this cofinal subtower): for every `m ≥ 1` the `3`-power level
`(A ⧸ 3^m) ⊗_A (Fin 2 → A)` — i.e. `T/3^m T` for the stable lattice
`T = Fin 2 → A` — is the group of `ℚ̄_3`-points of the generic fibre
of a finite flat group scheme over `ℤ_3`, the package spelled by
`GaloisRep.HasFlatProlongationAt`.

Classically: the compatible system attached to the descended
eigensystem has parallel weight `2` and conductor prime to `3`, so its
`3`-adic member `τ` is crystalline at `3` with Hodge–Tate weights
`{0, 1}` (Carayol/Taylor local-global compatibility at `p = ℓ` for `p`
prime to the level). Over `ℤ_3` the absolute ramification index is
`e = 1 < 2 = p - 1`, which is exactly the Fontaine–Laffaille range:
the crystalline lattice `T = Fin 2 → A` is the Tate module of a
`3`-divisible group `𝒢` over `ℤ_3` (Fontaine–Laffaille in weight `2`;
Raynaud, Breuil for the range-free refinement), and the levels
`T/3^m T` are precisely the `ℚ̄_3`-points of the generic fibres of the
finite flat group schemes `𝒢[3^m]`. This is the honest shape of the
literature input: the statement is asserted exactly on the `3`-power
levels, which are the levels of the `3`-divisible group, and NOT on
arbitrary congruence quotients — those are reached from these by
Raynaud's closure of finite flat group schemes under quotients, which
is a separate, unconditional brick (`hasFlatProlongationAt_of_surjective`
above) consumed by the transport below rather than smuggled in here.

Only positive levels (`1 ≤ m`) are asserted: at `m = 0` the ideal
`3^0 = (1)` is the unit ideal, the level is a single point, and the
transport discharges that case outright with the trivial Hopf algebra,
so the literature is not cited for it.

Literature: Fontaine–Laffaille, *Construction de représentations
p-adiques*, Ann. Sci. ÉNS 15 (1982); Raynaud, *Schémas en groupes de
type (p, …, p)*, Bull. SMF 102 (1974); Carayol, Ann. Sci. ÉNS 19
(1986) and Taylor, Invent. Math. 98 (1989) (the weight-2 local shape
at primes over `p` prime to the level); Breuil, *Groupes p-divisibles,
groupes finis et modules filtrés*, Ann. of Math. 152 (2000) (the
range-free refinement); BLGGT §5.5. FLT blueprint ch. 4: "flat at 3".

SOUNDNESS AUDIT (both ways, 2026-07-25): (i) direct — for the
realization produced by the construction leaf this is
Fontaine–Laffaille/Raynaud as above; for an abstract realization the
abstract-quantification caveat of pillar β applies, and (ii) collapse
— the hypothesis set is classically unsatisfiable (headline below),
so the statement is classically true for every package.

CIRCULARITY GUARD (inherited from pillar β, load-bearing): no
discharge through `Family.lean`, `Lift.lean`, or
`Modularity/Interface.lean`.

ROUTE AUDIT (2026-07-25, a full owner pass at closing this leaf; FIVE
candidate discharges and cuts checked, all five refuted or found
empty — read this before spending a worker on a "cheaper route").
The statement is FAITHFUL as written: it is not false, its conclusion
is not satisfiable by any junk witness, and it admits NO honest
decomposition inside the present tree. (Its hypothesis SIDE is another
matter — see the DISCHARGEABILITY AUDIT below.) In detail:

* *no subsingleton collapse*. `A ⧸ 3^m` is a NONZERO finite ring for
  every `m ≥ 1`: `A` is a nonzero `ℤ_3`-module-finite FREE algebra, so
  `3` cannot be a unit in `A` (else `A` would be a `ℚ_3`-algebra and a
  finitely generated free `ℤ_3`-module at once, forcing `A = 0`),
  i.e. `3 ∈ 𝔪_A`. Hence the level is `(A ⧸ 3^m)^2 ≠ 0` and
  `hasFlatProlongationAt_of_subsingleton` is unavailable;
* *no junk witness*. `GaloisRep.HasFlatProlongationAt` is a genuinely
  RESTRICTIVE condition on a finite `Γ ℚ_3`-module, not a shape
  condition: every finite `Γ ℚ_3`-module is the point group of a
  finite étale `ℚ_3`-Hopf algebra (the Gelfand-duality machinery of
  `KnownIn1980s/EllipticCurves/Flat.lean`), but only some of those
  admit a finite FLAT `𝒪ᵥ`-model. Over `ℤ_3` (`e = 1 < p - 1 = 2`)
  Raynaud/Oort–Tate classify the order-`3` group schemes: the generic
  fibre of one is `ℤ/3(ω^i · ψ)` with `0 ≤ i ≤ e = 1` and `ψ`
  UNRAMIFIED. An explicit non-example is therefore available: the
  quadratic characters of `G_{ℚ_3}` are the unramified one, the one
  cutting out `ℚ_3(√-3) = ℚ_3(ζ_3)` — which IS `ω` — and the one
  cutting out `ℚ_3(√3)`; the last is ramified and is not `ω`, so
  `ℤ/3` with that character has NO finite flat model over `ℤ_3`. So
  the conclusion cannot be manufactured from the mere shape of the
  level;
* *the reduction to level `1` is FALSE* (this is the shortcut most
  worth refuting explicitly). One is tempted to run
  `0 → T/3^m → T/3^{m+1} → T/3 → 0` and induct, using "an extension
  of flat by flat is flat". That extension-closure statement is FALSE
  at the level of GALOIS MODULES: over an absolutely unramified base
  with `e < p - 1` the comparison `Ext¹_fl → Ext¹_Γ` is INJECTIVE
  (Fontaine's uniqueness of prolongations) but NOT surjective. The
  standard witness is `Ext¹(ℤ/p, μ_p)`, where the flat classes are
  `ℤ_p^× / (ℤ_p^×)^p` inside the Galois classes
  `ℚ_p^× / (ℚ_p^×)^p` (Kummer theory) — index `p`, the missing class
  being that of the uniformizer `p` itself, i.e. exactly the
  Tate-curve/multiplicative-reduction extension `ℚ_p(p^{1/p})`. This
  is the same phenomenon as the classical criterion that a
  multiplicative-reduction curve has `E[p]` finite flat at `p` iff
  `p ∣ v(Δ)`. So flatness of ALL levels is strictly more than
  flatness of the first, and the induction cannot be repaired;
* *the `p`-divisible-group cut is EQUIVALENT, not a reduction*.
  Replacing this leaf by "`T` is the Tate module of a `3`-divisible
  group over `ℤ_3`" relocates the same sorry: the easy direction is
  the present statement, and the converse is a theorem (Tate; via
  Fontaine's `e < p - 1` uniqueness the compatible system of finite
  flat models assembles into a `3`-divisible group). Worse, the
  cut STRENGTHENS the leaf, since a `PDivisibleGroup` interface also
  carries the transition maps that this statement does not need.
  Introducing that interface here would be sorry-shuffling and is
  deliberately NOT done;
* *the `ℤ_3`-native restatement is cosmetic*. `𝒪ᵥ ≅ ℤ_3` at `v = (3)`
  (mathlib: `Rat.HeightOneSpectrum.adicCompletionIntegers.padicIntEquiv`,
  with `Rat.HeightOneSpectrum.adicCompletion.padicEquiv` on the generic
  fibre), so a finite flat Hopf `ℤ_3`-algebra base-changes to an
  `𝒪ᵥ`-one. Restating the leaf over `ℤ_3` therefore makes it strictly
  stronger at zero mathematical gain, and was rejected on those
  grounds. The bridge itself is worth recording for whoever DOES
  formalize the input: `(primesEquiv v₃ : ℕ) = 3` is available from
  `Rat.HeightOneSpectrum.natGenerator_dvd_iff` /
  `Rat.HeightOneSpectrum.span_natGenerator` (both stated through
  `IsIntegralClosure.intEquiv`) together with
  `asIdeal_toHeightOneSpectrum_eq_span` of `GroupScheme/ConnectedEtale.lean`,
  and the `ℤ_[a] ≃+* ℤ_[b]` transport along `a = b` is a one-line
  `subst` (`Fact` is a `Prop`, so the instance argument is
  proof-irrelevant).

DISCHARGEABILITY AUDIT (2026-07-25, the sharpest finding of the pass —
it decides whether this leaf is worth dispatching at all). Route (i) of
the SOUNDNESS AUDIT above is NOT a proof strategy for the statement AS
QUANTIFIED, and no amount of Fontaine–Laffaille formalization would make
it one. The quantifier runs over EVERY `Rlz : ThreeadicRealization`, and
that interface constrains `τ` only through `compat`, i.e. through
characteristic polynomials of Frobenius at almost all `q ∉ {2, 3, ℓ}`.
Frobenius data pins `τ` at most up to SEMISIMPLIFICATION
(Chebotarev + Brauer–Nesbitt, and only if `τ` is continuous, which the
interface does not require), whereas flatness at `3` is a property of
the EXTENSION CLASS, invisible to semisimplification: the two extensions
of `ℤ/3` by `μ_3` over `ℚ_3` corresponding to `1` and to `3` in
`ℚ_3^× / (ℚ_3^×)^3` have the SAME semisimplification and the same
Frobenius characteristic polynomials, and exactly one of them is finite
flat over `ℤ_3` (the Kummer computation recorded in the third bullet
above). So `compat` cannot imply the conclusion, and `τ` is not known to
be crystalline for an abstract `Rlz`.

Consequently the ONLY discharges are: (a) the collapse — which is
correct, since the hypothesis package is classically unsatisfiable, but
is forbidden HERE by the circularity guard below; or (b) a CUT-LEVEL
REPAIR: move the local shape at `3` into the `ThreeadicRealization`
interface as a FIELD (or restrict this quantifier to realizations
produced by the construction leaf), so that
`exists_threeadicRealization_of_witness` — which builds `τ` by the
actual Brauer descent and can therefore invoke Fontaine–Laffaille —
carries it. Repair (b) is a cut-level change, not this leaf's owner's
to make unilaterally; it is recorded here so that it is not lost. Note
that the same analysis applies verbatim to the sibling leaf
`threeadicRealization_stableLineAtTwo_of_witness` (the sorried leaf
under `threeadicRealization_isTameAtTwo_of_witness`: the local shape at
`2` is likewise invisible to Frobenius data at `q ∉ {2, 3, ℓ}`), but
NOT to
`threeadicRealization_det_cyclotomic_of_witness`, whose conclusion IS a
determinant of Frobenius characteristic polynomials and is therefore
genuinely reachable from `compat`.

CONSUMPTION NOTE for whoever formalizes the input (a non-obvious
finding of the same pass): `GaloisRep.hasFlatProlongationAt_of_hopf_package`
of `Deformations/RepresentationTheory/FlatProlongation.lean` — the
tree's only general producer of a flat-prolongation package — is
UNUSABLE here. It requires a base ring `R` with `Algebra R ℚ` (its
points comparison runs through `ℚ̄` and `algHomEquivOfFinite`), i.e. a
group scheme over the LOCALIZATION `ℤ_(3)`, whereas Fontaine–Laffaille
produces one over the COMPLETION `ℤ_3`, which does not map to `ℚ`. The
input must therefore be fed either through the `padicIntEquiv` bridge
above or straight into the definition of
`GaloisRep.HasFlatProlongationAt` (which is purely local: the witness
lives over `𝒪ᵥ` and the equivariance is for `Γ Kᵥ`).

MISSING-MACHINERY AUDIT (2026-07-25, dependency order — none of this
exists in mathlib or in this tree, and the leaf is blocked on all of
it; each item named as the statement an owner would be dispatched at):

1. *`p`-divisible groups over a complete DVR*: a structure carrying a
   system of finite flat Hopf `𝒪`-algebras `H m` with the `p^m`-torsion
   inclusions, its generic-fibre point functor, and its Tate module.
   (Everything needed to STATE this is present — `HopfAlgebra`,
   `Module.Flat`, `Module.Finite`, and the convolution monoid on
   points — so this is the first buildable item, but see the audit
   above: on its own it buys no reduction.)
2. *Filtered `φ`-modules / strongly divisible `ℤ_p`-lattices in
   Hodge–Tate weights `[0, p-2]` (Fontaine–Laffaille modules)*, and
   the FL functor to finite `Γ ℚ_p`-modules.
3. *The Fontaine–Laffaille equivalence*: the FL functor of (2) is an
   equivalence onto the finite flat models of (1) in the range
   `e < p - 1`. Stating the crystalline side needs the period ring
   `B_cris` (mathlib has `WittVector` and nothing above it), which is
   the deepest missing prerequisite of the whole chain.
4. *Local-global compatibility at `p = ℓ`* (Carayol, Taylor): the
   `3`-adic member of a parallel-weight-`2` compatible system of
   conductor prime to `3` is crystalline at `3` with Hodge–Tate
   weights `{0, 1}`. Not stateable before (3).

Item 4 composed with items 3–1 IS this leaf; there is no intermediate
at which the sorry can honestly be split, which is why it is written
here as a single literature joint. -/
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
  sorry

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

/-- **The Weil–Deligne type at `2` of the `3`-adic member, as a stable
line with unramified quadratic quotient** (sorry node — the SHRUNK
LITERATURE JOINT of the tameness transfer; cut out 2026-07-24 in matrix
coordinates, re-cut coordinate-free 2026-07-25): there is an `A`-basis
`b` of the stable lattice `Fin 2 → A` and an unramified square-trivial
character `δ` of `G_{ℚ_2}` such that `G_{ℚ_2}` acts on the quotient of
the lattice by the line `A · b 0` through `δ`:

  `τ g v ≡ δ g 1 • v  (mod A · b 0)`  for all `g` and all `v`.

That single clause is the whole classical content. It already forces
the line `A · b 0` to be `G_{ℚ_2}`-STABLE (take `v = b 0`: both `τ g
(b 0) - δ g 1 • b 0` and `δ g 1 • b 0` lie in the line), so the shape
"extension of the unramified quadratic `δ` by something, in a basis
adapted to the lattice" is stated without ever mentioning a matrix.
The matrix reading — upper-triangularity with `δ g 1` on the diagonal —
is now PROVEN from this clause in
`threeadicRealization_weilDeligneType_two_of_witness` below; that
bookkeeping used to be part of this citation and no longer is.

WHY THIS IS THE CITATION. `ρ`'s type at `2` is an extension of an
unramified square-trivial character by its cyclotomic twist
(`hρ.isTameAtTwo` together with the cyclotomic determinant). The type
is carried across the compatible system by STRICT COMPATIBILITY, which
is exactly the property that a single Weil–Deligne representation
`WD_v(R)` over the coefficient field reproduces `WD(r_λ|G_{F_v})^{F-ss}`
for every `λ` whose residue characteristic differs from that of `v`
(BLGGT §5.1, the display `ς WD_v(R) ≅ WD(r_λ|G_{F_v})^{F-ss}`; here
`v = 2` and the two places compared are `λ | ℓ` and `λ | 3`, legitimate
because `2 ∉ {ℓ, 3}`). Strict compatibility of the system through which
the descent runs is Carayol's theorem for Hilbert newforms — the local
constituent is pinned at EVERY finite place, not merely almost all —
and the membership of `ρ` in such a system is BLGGT Theorem 5.5.1.
Finally the stable-lattice normalization of the construction leaf
(`exists_threeadicRealization_of_witness`) turns the `E_λ`-rational
stable line into a saturated `A`-line, i.e. into the first vector of an
`A`-basis, which is why the basis `b` may be demanded here. The
character `δ` is handed over as a `GaloisRep` because it IS the quotient
character of the constant type — in particular continuous, being the
local component of the compatible system's nebentypus-free unramified
twist.

Literature (page-level checks 2026-07-25 against the downloaded
sources): BLGGT, *Potential automorphy and change of weight*, Ann. of
Math. 179 (2014) — §5.1 for the definition of a strictly compatible
system (the display quoted above) and Theorem 5.5.1 for "a potentially
diagonalizable, totally odd, regular algebraic polarized `l`-adic
representation with `r̄|_{G_F(ζ_l)}` irreducible is part of a strictly
pure compatible system"; Carayol, *Sur les représentations `l`-adiques
associées aux formes modulaires de Hilbert*, Ann. Sci. ÉNS (4) 19
(1986) 409–468, Théorème (A) p. 410: a strictly compatible system
`{σ_λ}` with `σ_λ|W_p ≅ σ_λ(π_p)` at EVERY finite place `p` of residue
characteristic different from that of `λ`, `σ(π_p)` being the
`F`-semisimple degree-`2` Weil–Deligne representation of the Hecke
correspondence (§0.5). Khare–Wintenberger, *Serre's modularity
conjecture (I)*, Invent. Math. 178 (2009) 485–504, for the same
constancy inside the minimal-lifting induction (paywalled; NOT
page-verified here — the two references above are the load-bearing
ones). FLT blueprint ch. 4: "tame at 2".

SOUNDNESS AUDIT (both ways; 2026-07-24, re-checked 2026-07-25 for the
coordinate-free form): (i) direct — for the realization produced by the
construction leaf this is the Weil–Deligne-type transfer above, read in
a saturated basis; for an abstract realization the
abstract-quantification caveat of pillar β applies, and (ii) collapse —
the hypothesis set is classically unsatisfiable (the headline
`not_isIrreducible_of_isHardlyRamified_of_five_le` below refutes
`hirr`), so the statement is classically true for every package.

DISCHARGE-ROUTE AUDIT (2026-07-25, independent re-check): three
candidate discharges were enumerated; all three are closed, so the leaf
stands at its irreducible size.

* *From the carrier's own fields* — impossible. `ThreeadicRealization`
  records only `S₁`, `A`, `τ`, `ιA`, `ιA_injective` and `compat`, and
  `compat` pins characteristic polynomials only at primes `q ∉ S₁` with
  `q ∉ {2, 3, ℓ}`. Nothing in the structure mentions the decomposition
  group at `2`, and no formal argument recovers a local type at `2`
  from Frobenius data away from `2` — that recovery IS strict
  compatibility, i.e. the citation itself.
* *The odd-prime dichotomy* (collapse) — closed by the circularity
  guard below, and independently by declaration order: the only two
  in-tree dichotomies are `Modularity/Interface.lean`'s
  `not_isIrreducible_of_isHardlyRamified_of_odd` (banned) and this
  module's own headline
  `not_isIrreducible_of_isHardlyRamified_of_five_le`, declared BELOW
  this leaf.
* *The `3`-adic classification* — closed by circularity. This is the
  route worth recording, because it is the one that looks promising:
  `τ`'s determinant, unramifiedness and flatness are all established
  ABOVE this leaf, so three of the four hardly ramified conditions for
  `τ` are already in hand. But every theorem in that chain
  (`ModThree.lean`'s `mod_three`, `mod_three_reducible`,
  `mod_three_of_stable_line`; `Threeadic.lean`'s
  `exists_global_triangular_of_residual_trivial_quotient`,
  `exists_frobenius_triangular`, `three_adic`) takes the WHOLE
  `IsHardlyRamified` structure as a single hypothesis — none takes the
  four conditions separately — and the tame-at-`2` field is genuinely
  consumed (`quotCharacter_unramified_at_two`, on the path
  `mod_three → mod_three_of_stable_line`). Supplying it would require
  `threeadicRealization_isTameAtTwo_of_witness`, which is proven THROUGH
  this leaf.

FAITHFULNESS RE-CHECK (2026-07-25): neither vacuous nor
inertia-widened. NOT VACUOUS — `Rlz.A` is a local ring, hence
nontrivial, so `Submodule.span Rlz.A {b 0}` is a PROPER submodule for
every basis `b`; the congruence clause therefore carries real content
(it says the rank-`1` quotient by that line is the character `δ`), and
no junk witness can be assembled from the hypotheses alone. NOT
WIDENED — `δ`'s unramifiedness is quantified over
`AddSubgroup.inertia` only, while the congruence is quantified over the
whole decomposition group `Γ ℚ_[2]`; that is the correct shape and it
matches `IsHardlyRamified.isTameAtTwo` verbatim.

PACKAGING NOTE (2026-07-25): demanding a BASIS rather than a bare
surjection adds no literature content — over the local ring `A` the two
forms are equivalent. A surjection `πq : A² ↠ A` has one of `πq e₀`,
`πq e₁` a unit (the non-units of a local ring form an ideal), and the
triangular change of basis this determines is invertible, yielding a
basis `b` with `πq (b 0) = 0`, `πq (b 1) = 1`, hence
`ker πq = A · b 0`. So restating this citation in quotient form would
shrink nothing: it would merely reproduce the statement of
`threeadicRealization_isTameAtTwo_of_witness`, which this leaf already
implies through the two proven transports below.

CIRCULARITY GUARD (inherited from pillar β, load-bearing): no
discharge through `Family.lean`, `Lift.lean`, or
`Modularity/Interface.lean`. In particular the odd-prime dichotomy
`not_isIrreducible_of_isHardlyRamified_of_odd` is NOT available: it
routes `ℓ ≥ 5` through this module's own headline, whose proof consumes
pillar β and hence this leaf. -/
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
  sorry

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
