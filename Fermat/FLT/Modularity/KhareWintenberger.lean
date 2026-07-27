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
-- the Raynaud quotient-closure brick in its NEUTRAL HOME (2026-07-25):
-- `GaloisRep.HasFlatProlongationAt.of_surjective`, re-homed below the
-- `Interface.lean` ↔ this-module import cycle so that
-- `hasFlatProlongationAt_of_surjective` below can consume it. See that
-- module's header for the duplication/unification audit.
import Fermat.FLT.Deformations.RepresentationTheory.RaynaudQuotient
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

@[expose] public section

namespace GaloisRepresentation.Modularity

open IsDedekindDomain Polynomial

universe u v

/-- **Pillar α — Khare–Wintenberger minimal lifting** (sorry node): an
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
  `2` over `F` attached to `ρ|_{G_F}`: `E` is its Hecke field (a
  number field, by Shimura's rationality), `heckeF w` its Hecke
  polynomial `X² − a_w·X + Nw` away from the finite bad set `badF`
  (the level of `f` and the places over `2`, `3` and `ℓ`).
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
  /-- The Hecke field of the attached Hilbert newform. -/
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
  `exists_heckeSystem_of_residualModularity`, the two sorried leaves
  that replace it): the
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
`exists_totallyReal_point_of_geometricallyIrreducible` (SORRY —
Moret–Bailly 1989 Thm 1.3), and
`exists_twistedHilbertBlumenthalModuli_of_five_le` (SORRY — Taylor
2002 §2). `exists_hilbertBlumenthalPoint_of_five_le` itself is now
PROVEN and is no longer a leaf. -/

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

/-- **Moret–Bailly's existence theorem for global points with prescribed
local behaviour** (sorry node — pure algebraic geometry, no arithmetic of
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

CIRCULARITY GUARD: this is a statement of algebraic geometry with no
Galois-representation hypotheses, so no route through `Family.lean`,
`Lift.lean` or `Modularity/Interface.lean` could even be relevant; it
must be proven by the geometric argument (Picard-scheme torsors over an
incompressible neighbourhood) recorded above. -/
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
      HasRationalPoint fX F :=
  sorry

/-- **The twisted Hilbert–Blumenthal moduli variety** (sorry node — the
MODULI INPUT ALONE, Taylor 2002 §2 via Shimura's theory of
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

This leaf is what remains of the geometric joint after Moret–Bailly's
theorem is split off above: it contains no existence-of-global-points
content whatsoever, only the construction and the moduli
interpretation of one variety.

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
        Nonempty (HilbertBlumenthalPoint ℓ F (ρbar.map (algebraMap ℚ F))) :=
  sorry

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

/-- **Residual modularity in the dihedral case** (sorry node; joint
(a) of the automorphic cut — Hecke theta series / automorphic
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
          pt.ρbarp.charFrob w :=
  sorry

/-- **Modularity lifting at `p` in the residually dihedral case**
(sorry node; joint (b) of the automorphic cut — Taylor, *Remarks on a
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
    {Λ : Type u} [CommRing Λ] (jΛ : Λ →+* E₁)
    (hjΛ : Function.Injective jΛ) (redΛ : Λ →+* pt.kp)
    (a₁ : HeightOneSpectrum (NumberField.RingOfIntegers F) → Λ)
    (S₁ : Finset (HeightOneSpectrum (NumberField.RingOfIntegers F)))
    (hres : ∀ w ∉ S₁,
      (X ^ 2 - C (a₁ w) * X + C (Ideal.absNorm w.asIdeal : Λ)).map redΛ =
        pt.ρbarp.charFrob w) :
    ∃ (E₀ : Type u) (_ : Field E₀) (_ : NumberField E₀)
      (θ : E₀ →+* pt.D)
      (a₀ : HeightOneSpectrum (NumberField.RingOfIntegers F) → E₀)
      (S₀ : Finset (HeightOneSpectrum (NumberField.RingOfIntegers F))),
      ∀ w ∉ S₀,
        (pt.τp.charFrob w).map pt.ιC =
          (X ^ 2 - C (a₀ w) * X +
            C (Ideal.absNorm w.asIdeal : E₀)).map (pt.ψDp.comp θ) :=
  sorry

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
  module — the recommended discharge is to mirror that proof with the
  residue cardinality `Nw` in place of `q`.
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
-/

/-- **Shimura rationality for the Hilbert-newform eigensystem, range
form** (sorry node; sub-leaf (b-i) of the Carayol/Shimura sub-cut — the
ONLY automorphic input of sub-leaf (b)): the eigenvalue function `aF`
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
not here.  Until that happens this node should not be dispatched as a
proof target.

CIRCULARITY GUARD (inherited from pillar β, load-bearing): no
discharge through `Family.lean`, `Lift.lean`, or
`Modularity/Interface.lean`. -/
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
        X ^ 2 - C (aF w) * X + C (dF w)) :
    ∃ (E : Type u) (_ : Field E) (_ : NumberField E)
      (ψℓ : E →+* AlgebraicClosure ℚ_[ℓ]),
      (∀ w ∉ badF, aF w ∈ Set.range ψℓ) ∧
      ∀ w ∉ badF, (ℓ : NumberField.RingOfIntegers F) ∈ w.asIdeal →
        dF w ∈ Set.range ψℓ :=
  sorry

/-- **The `ℓ`-adic cyclotomic character at a Frobenius of the base `F`**
(sorry node; sub-leaf (b-ii) of the Carayol/Shimura sub-cut — pure
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

RECOMMENDED DISCHARGE (2026-07-25): this is the exact `F`-analogue of
the PROVEN rational-prime lemma
`cyclotomicCharacter_adicArithFrob_eq_natCast` later in this module
(with `q` replaced by the residue cardinality `Nw`).  That proof runs:
`PadicInt.ext_of_toZModPow` to reduce to level `ℓⁿ`,
`cyclotomicCharacter.toZModPow` plus `modularCyclotomicCharacter.unique`
to identify the value with the exponent of the Frobenius action on
`μ_{ℓⁿ}`, and `AlgHom.IsArithFrobAt.apply_of_pow_eq_one` for that
action — the last step needing `ℓ` to be a unit in the local integers
at `w`, which is exactly `hwℓ`, and the residue cardinality identity
`Nat.card (𝓞_F ⧸ w) = Ideal.absNorm w.asIdeal` (mathlib's
`Ideal.absNorm_apply`/`Submodule.cardQuot`).  Only the residue-field
cardinality bookkeeping differs from the rational case, where it is
`natCard_residue_quotient_toHeightOneSpectrum`.

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
        ℤ_[ℓ]ˣ) : ℤ_[ℓ]) = (Ideal.absNorm w.asIdeal : ℤ_[ℓ]) :=
  sorry

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
        X ^ 2 - C (aF w) * X + C (dF w)) :
    ∃ (E : Type u) (_ : Field E) (_ : NumberField E)
      (ψℓ : E →+* AlgebraicClosure ℚ_[ℓ])
      (a d : HeightOneSpectrum (NumberField.RingOfIntegers F) → E),
      (∀ w ∉ badF, ψℓ (a w) = aF w) ∧ ∀ w ∉ badF, ψℓ (d w) = dF w := by
  classical
  -- (b-i) Shimura rationality: the Hecke field `E`, the place `ψℓ`, and
  -- range membership of the eigenvalues
  obtain ⟨E, hE, hNE, ψℓ, ha, hdℓ⟩ :=
    exists_heckeField_mem_range_of_eigensystem hℓodd hℓ5 hZinj hrank hρ hW
      hρbar hirr F hFtr hFgal hirrF badF aF dF ιO hιO hshape
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
  obtain ⟨badF, aF, dF, ιO, hιO, hshape⟩ :=
    exists_heckeEigensystem_of_congruentSeed hℓodd hℓ5 hZinj hrank hρ hW
      hρbar hirr π hπsurj hπ F hFtr hFgal hirrF seed badρ hcong
  -- (b) Carayol/Shimura: the eigensystem is defined over the Hecke field
  obtain ⟨E, hE, hNE, ψℓ, a, d, ha, hd⟩ :=
    exists_heckeField_of_eigensystem hℓodd hℓ5 hZinj hrank hρ hW hρbar hirr
      F hFtr hFgal hirrF badF aF dF ιO hιO hshape
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
(PROVEN, 2026-07-25; first of the four coefficient-ring bricks that
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

CITATION-SHRINKING CUT (2026-07-25). This leaf replaces the earlier
`exists_threeadic_realization_domain_of_heckePackage` citation, which
is now a PROVEN assembly over it. Five of that statement's components
were pulled out of the citation and proven in-tree as the four bricks
above; the citation now asserts strictly less:

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
  rather than one assumption plus one step.

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
which is why those have been split off and proven (four bricks above,
plus `free_of_finite_of_algebraMap_padicInt_injective`).

RESIDUAL BOOKKEEPING NOT YET PULLED OUT (audited 2026-07-25, recorded
so it is not re-scanned from scratch): `IsLocalRing B` stays in the
citation. It is TRUE for the produced ring but its formal proof from
"domain, module-finite over `ℤ_3`" needs a Henselian/completeness
input — the maximal ideals of such a `B` all lie over `(3)` (that part
is formal, `Algebra.IsIntegral.isField_iff_isField`), but their
UNIQUENESS is exactly uniqueness of the extension of the `3`-adic
valuation to `Frac B`. The pin has `HenselianRing` and
`IsAdicComplete.henselianRing` but no instance connecting them to
module-finite algebras (no `HenselianLocalRing` use anywhere outside
its defining file), no `IsNonarchimedeanLocalField` instance for finite
extensions of `ℚ_p`, and only the unbundled `spectralNorm` layer — so
the bridge would have to be built (idempotent lifting along
`3`-adic completeness of a finite free `ℤ_3`-module, then
"connected finite ring is local"). That is a self-contained
commutative-algebra project, not a shrinking of the geometry.

Also audited and deliberately NOT done: restating the matching clause
as the pair `ιB (tr τF(Frob_w)) = ψ₃ a_w`, `ιB (det τF(Frob_w)) =
ψ₃ d_w` (the "eigenvalue-to-trace dictionary"). Both sides of the
present clause are monic of degree `2` (`hmod` forces `heckeF w` to be
one), so the trace/determinant form is EQUIVALENT, not weaker: it
would relocate polynomial bookkeeping into this file without removing
anything from the citation.

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
        (heckeF w).map ψℓ) :
    ∃ (B : Type u) (_ : CommRing B) (_ : IsDomain B) (_ : IsLocalRing B)
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
`carayol_threeadic_realization_of_heckePackage` plus the four
coefficient-ring bricks proven above — the module topology is a ring
topology and is the module topology
(`isTopologicalRing_moduleTopology_of_finite`), and both injectivity
components follow from the existence of the comparison embedding into
the characteristic-zero field `ℚ̄_3`
(`injective_of_finite_padicInt_charZero`,
`injective_algebraMap_of_ringHom_charZero`). Nothing else changes: the
coefficient ring, the representation, the place `ψ₃`, the embedding
`ιB` and the Hecke-polynomial matching clause are carried verbatim
from the citation, so there is no lattice change and no charpoly to
re-compute.

See `carayol_threeadic_realization_of_heckePackage` for the full
literature, pin, route and soundness audits (including what was
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
        (heckeF w).map ψℓ) :
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
  -- back as a bare local domain, module-finite over `ℤ_3`, with no
  -- topology, no `ℤ_3`-injectivity and no injectivity of the comparison
  -- embedding asserted
  obtain ⟨B, hCR, hDom, hLR, hAlg, hFin, τF, ψ₃, ιB, hmatch⟩ :=
    carayol_threeadic_realization_of_heckePackage hℓodd hℓ5 hZinj hrank hρ hW
      hρbar hirr π hπsurj hπ F hFtr hFgal E badF heckeF ψℓ ιO hιO hmod
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
    injective_of_finite_padicInt_charZero (p := 3) ιB, hmatch⟩

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
  asserts the topology on the coefficient ring, nor either injectivity
  component) — the sole residual sorry of the node is now that core;
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
        (heckeF w).map ψℓ) :
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
      ιO hιO hmod
  -- (c) the eigensystem-match transport: the normalization below does
  -- not move the coefficient ring, so `hmatch` is carried verbatim and
  -- only the `Module.Free` component remains to be supplied
  refine ⟨B, hCR, hTS, hTR, hAlg, hLR, hFin, ?_, hMT, τF, ψ₃, ιB, hιB,
    hmatch⟩
  -- (b) the free-lattice normalization over `ℤ_3`
  exact @free_of_finite_of_algebraMap_padicInt_injective 3 _ B hCR hDom
    hAlg hFin hBinj

/-- **Carrier inhabitation — potential modularity of the KW lift**
(sorry node — Taylor's theorem, the analytic core of pillar β): the
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
circularity guard above binds each of them. -/
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
  -- (iii) the Hilbert-modular `3`-adic realization: the 3-adic block
  obtain ⟨B, hB₁, hB₂, hB₃, hB₄, hB₅, hB₆, hB₇, hB₈, τF, ψ₃, ιB, hιB,
    hmatch⟩ :=
    exists_threeadic_realization_of_heckePackage hℓodd hℓ5 hZinj hrank hρ
      hW hρbar hirr π hπsurj hπ F hFtr hFgal E badF heckeF ψℓ ιO hιO hmod
  -- glue: instantiate the carrier fieldwise
  exact ⟨{ F := F, totallyReal := hFtr, galoisF := hFgal, E := E,
           badF := badF, heckeF := heckeF, ψℓ := ψℓ, ιO := ιO,
           ιO_injective := hιO, modularF := hmod, B := B, τF := τF,
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

/-- **One PRIME-degree cyclic step of solvable base change** (sorry node;
THE terminal literature citation of the `ℓ`-adic solvable descent —
Langlands 1980, Arthur–Clozel 1989): if the eigensystem of `ρ` descends
to the fixed field `L = F^C`, and `C ≤ D` is normal with quotient `D/C`
of PRIME order `p` (equivalently: `L/M` is a cyclic Galois extension of
degree `p`, where `M = F^D`), then the eigensystem descends to `M`.

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
Frobenius characteristic polynomials of the (twisted) `f_M`-system with
Hecke polynomials; their coefficients — Hecke eigenvalues of `f_M`
enlarged by the twisting-character values — lie in the carrier's `E`,
which is, per the consumers' docstrings, the Hecke field OF THE
DESCENDED system, the normalization that absorbs exactly these
enlargements. The new bad set collects the places of `M` below the bad
set of the `L`-system, the places over `2`, `3`, `ℓ`, and the places
ramified in `L/M`.

Literature: Langlands 1980 and Arthur–Clozel 1989 as above;
Barnet-Lamb–Gee–Geraghty–Taylor, *Potential automorphy and change of
weight*, Ann. of Math. 179 (2014), §5.3 (this descent per Brauer piece,
verbatim); Khare–Wintenberger, *Serre's modularity conjecture (I)*,
Invent. Math. 178 (2009), §5; Carayol, Ann. Sci. ÉNS 19 (1986).

PIN AUDIT (2026-07-24/25): no automorphic-representation vocabulary
exists on this pin, and the reference project's `cyclic_base_change`
(`~/cs/FLT`, `FLT/GaloisRepresentation/Automorphic.lean`) is itself a
sorried statement phrased through an `IsAutomorphic` predicate on
quaternionic forms — vocabulary this project does not have (see the
`HeckeSystemDescendsTo` docstring). Nothing is vendorable, on this pin
or after a pin-drift audit.

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
PRECISELY to keep route (ii) available: the prime-degree sharpening is a
sharpening of the group-theoretic hypothesis only, never a weakening of
the arithmetic one.

ROUTE AUDIT (2026-07-24): discharge by vacuity — `absurd hirr
(not_isIrreducible_of_isHardlyRamified_of_five_le …)`, the route the
interface leaves of `Modularity/Interface.lean` take — is NOT available
here: the headline consumes this node (headline ←
`exists_threeadic_compatible_member_of_five_le` ←
`exists_heckeField_system_of_witness` ←
`exists_descended_heckeSystem_of_solvable` ←
`heckeSystemDescendsTo_of_cyclic_step` ← this node), so the vacuity
route would be circular. The classical route above is the one to follow.

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
    HeckeSystemDescendsTo Wit D :=
  sorry

/-- **One cyclic step of solvable base change** (PROVEN, 2026-07-25, from
the prime-degree citation `heckeSystemDescendsTo_of_prime_cyclic_step`
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
by `heckeSystemDescendsTo_of_prime_cyclic_step` (the citation). Formally
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
field** (sorry node; the per-induced-piece citation leaf of the
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
refines a cyclic quotient into prime steps — so the arithmetic citation
of the descent route is now `heckeSystemDescendsTo_of_prime_cyclic_step`,
the prime-degree statement that the literature actually proves.

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

/-- **Some Brauer piece has a degree-one place above almost every
rational prime** (sorry node; the arithmetic core of the induced-trace
expansion below, and the ONLY place in the descent where the Brauer
decomposition is used): given a Brauer decomposition of the trivial
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

MISSING MACHINERY (named in dependency order for the fleet; none of it
is in mathlib at the current pin, and none of it is in this project):

1. the arithmetic Frobenius `Frob_q ∈ Gal(F/ℚ)` of a rational prime
   unramified in a finite Galois extension `F/ℚ`, as an element of the
   FINITE Galois group — this project has only the local
   `Field.AbsoluteGaloisGroup.adicArithFrob : Γ ℚ_q`, and the bridge
   between them (the decomposition group at a chosen prime of `F` over
   `q`, and its surjection onto the residue Galois group) is absent;
2. finiteness of the set of rational primes ramified in a number field;
3. the double-coset parametrisation of `Ideal.primesOver q (𝓞 (F^H))`
   for `H ≤ Gal(F/ℚ)`, with `Ideal.inertiaDeg` of the prime attached to
   `H x ⟨σ⟩` computed as the least `d ≥ 1` with `x σᵈ x⁻¹ ∈ H`;
4. functoriality of `IsDedekindDomain.HeightOneSpectrum.adicCompletion`
   along `Ideal.under`: for `w | q` a LOCAL ring hom `ℚ_q →+* K_w`
   compatible with `ℚ → K`, together with the identification of its
   residue cardinality with `Nat.card (𝓞_K / w)`.

Item 4 is the only one whose statement is already essentially present in
this project — `IsDedekindDomain.HeightOneSpectrum.adicCompletionMap`
(used by `Field.absoluteGaloisGroup.exists_conj_map_adicArithFrob_ringEquiv`)
builds exactly such a map from a ring hom of the DEDEKIND domains that
respects the valuations; what is missing is its instance for an
extension of number fields at a prime above.

SOUNDNESS AUDIT: NOT vacuous. The conclusion asserts the EXISTENCE of a
degree-one place, which fails for a fixed `i` (a rational prime inert in
`Kᵢ` has none) and is rescued only by `hbrauer` together with the
vanishing `hφ0`; both are load-bearing, as is `[IsGalois ℚ F]` (without
it there is no `Frob_q` in `F ≃ₐ[ℚ] F` and the double-coset description
fails). When `n = 0` the hypothesis `hbrauer` reads `0 = 1` in `ℂ` and
the statement is vacuously true, as it must be. No representation
theory, no `ℓ` and no modularity enter this leaf — it is pure algebraic
number theory, which is why it is cut out here. -/
theorem exists_degreeOnePlace_of_brauer
    {F : Type*} [Field F] [NumberField F] [IsGalois ℚ F]
    (n : ℕ) (H : Fin n → Subgroup (F ≃ₐ[ℚ] F))
    (φ : Fin n → (F ≃ₐ[ℚ] F) → ℂ) (c : Fin n → ℚ)
    (hφ0 : ∀ i, ∀ g ∉ H i, φ i g = 0)
    (hφ1 : ∀ i, φ i 1 = 1)
    (hφmul : ∀ i, ∀ a ∈ H i, ∀ b ∈ H i, φ i (a * b) = φ i a * φ i b)
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
                (algebraMap ℚ (IntermediateField.fixedField (H i))) :=
  sorry

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
the descended pieces** (sorry node; the induced-character unwinding of
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

CITATION-SHRINKING CUT (2026-07-25). This leaf replaces the earlier
`exists_threeadicBrauerSum_of_witness` citation, which is now a PROVEN
assembly over it. Five components of that statement were pulled out of
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
  assumption plus a step.

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
  realizations.

So the leaf stays in lattice (coefficient-ring) form — the same
conclusion, for the same reason, that the twin node reached ("that cut
would trade one citation for two"). Also audited and deliberately NOT
done, for the reason recorded at the twin: restating the matching clause
as the trace/determinant pair. Both sides here are monic of degree `2`
(`hPv` forces `Pv v` to be, through the injective `Wit.ψℓ`), so that
form is EQUIVALENT, not weaker — it would relocate polynomial
bookkeeping into this file without removing anything from the citation.
`IsLocalRing A` likewise stays, for the Henselian-input reason recorded
at the twin.

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
      (A : Type u) (_ : CommRing A) (_ : IsDomain A) (_ : IsLocalRing A)
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
  obtain ⟨S₁, A, hCR, hDom, hLR, hAlg, hFin, τ, ιA, hmatch⟩ :=
    blggt_threeadicBrauerSum_of_witness hℓodd hℓ5 hZinj hrank hρ hW hρbar
      hirr π hπsurj hπ Wit S₀ Pv hPv
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
(sorry node): the Brauer-descended `3`-adic member has cyclotomic
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

/-- **Member-independence of the ramification locus away from `3`**
(sorry node, CITATION LEAF — isolated 2026-07-25 out of
`exists_conductor_threeadicRealization_of_witness`, whose conductor
bookkeeping is PROVEN below over it): every prime `p ≠ 3` at which the
Brauer-descended `3`-adic member `τ` genuinely RAMIFIES is distinct
from `ℓ`, and is a prime at which the `ℓ`-adic member `ρ` itself
genuinely ramifies.

This is the sharpest form of the Carayol joint: it is purely LOCAL (one
prime at a time), carries no existential and no finiteness-of-
ramification bookkeeping, and is exactly the conjunction of the two
literature inputs the conductor statement needs.

* For `p ∤ 3ℓ` it is the member-independence half of Carayol's
  local-global compatibility: the Weil–Deligne parameter at a place `p`
  prime to BOTH residue characteristics is independent of the member of
  the compatible system, so a ramified parameter on the `3`-adic member
  `τ` is a ramified parameter on the `ℓ`-adic member `ρ`.
* The clause `p ≠ ℓ` is the Fontaine–Laffaille/Carayol input at the
  `ℓ`-adic member's own residue characteristic: `ρ` is FLAT at `ℓ`
  (`hρ.isFlat`), i.e. crystalline of Hodge–Tate weights `{0, 1}`, which
  is the local condition corresponding to level prime to `ℓ`, so `ℓ`
  does not divide the level of the descended eigensystem and `τ` is
  unramified at `ℓ` — hence a prime where `τ` ramifies cannot be `ℓ`.

Note what is NOT asserted: nothing about `p = 3` (the residue
characteristic of `τ`, where the flatness node
`threeadicRealization_isFlat_of_witness` carries the local condition
instead), and no claim that any prime ramifies. Consequently the
statement is satisfiable by a member unramified everywhere away from
`3`, which is precisely the classical expectation here — the conductor
of the system divides `2`.

Literature: Carayol, *Sur les représentations `ℓ`-adiques associées aux
formes modulaires de Hilbert*, Ann. Sci. ÉNS 19 (1986) (local-global
compatibility); Khare–Wintenberger, *Serre's modularity conjecture
(I)*, Invent. Math. 178 (2009), §5 (strict compatibility away from the
residue characteristic); BLGGT, *Potential automorphy and change of
weight*, Ann. of Math. 179 (2014), §5.5; Fontaine–Laffaille,
*Construction de représentations p-adiques*, Ann. Sci. ÉNS 15 (1982)
(flat at `ℓ` ⟺ level prime to `ℓ` in weight `2`).

ROUTE AUDIT (2026-07-25): the *charFrob cut* out of `Rlz.compat` is
again rejected here for the reason recorded at the consumer — `compat`
equates characteristic polynomials of Frobenius at unramified places
away from the finite set `Rlz.S₁` and therefore carries no inertia
information whatsoever, and `ThreeadicRealization` carries no other
arithmetic datum. No formal route to an inertia statement exists in the
interface, which is why this is cut as a literature joint.

SOUNDNESS AUDIT (both ways, 2026-07-25): (i) direct — for the
realization produced by the construction leaf this is Carayol's theorem
as cited, applied to the descended eigensystem on both sides of the
compatible family; for an abstract realization the
abstract-quantification caveat of pillar β applies, and (ii) collapse —
the hypothesis set is classically unsatisfiable (headline at the end of
this module), so the statement is classically true for every package.

CIRCULARITY GUARD (inherited from pillar β, load-bearing): no discharge
through `Family.lean`, `Lift.lean`, or `Modularity/Interface.lean`. -/
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
        ¬ ρ.IsUnramifiedAt hp.toHeightOneSpectrumRingOfIntegersRat :=
  sorry

/-- **Carayol local-global compatibility away from the residue
characteristic — the conductor of the descended system** (PROVEN
2026-07-25 over the sharper local citation leaf
`threeadicRealization_ramified_transfer_of_witness`): the
Brauer-descended `3`-adic member `τ` has a
conductor `N` in the usual sense, namely

* `τ` is unramified at every prime `p ∤ 3N` (clause 1), and
* every prime `p ∤ 3` dividing `N` is a prime at which the `ℓ`-adic
  member `ρ` itself genuinely ramifies, and is distinct from `ℓ`
  (clause 2).

The literature content of this node — that the conductor is an
invariant of the compatible system away from the residue characteristic
— is now carried by ONE sharper, purely local citation leaf,
`threeadicRealization_ramified_transfer_of_witness` (immediately above):
every prime `p ≠ 3` at which `τ` ramifies is a prime `≠ ℓ` at which `ρ`
ramifies. That leaf is exactly Carayol's member-independence of the
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

The residual sorry of this node is therefore exactly the one citation
leaf, and the two hardly ramified inputs it is cut against
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

/-- **Raynaud quotient closure, in prolongation form** (PROVEN
2026-07-25, by RE-HOMING rather than by a third proof — see the HOME
AUDIT below, which is now discharged): a `G_ℚ`-equivariant QUOTIENT of a
Galois representation which has a flat prolongation at `v` again has a
flat prolongation at `v`.

Proof: `GaloisRep.HasFlatProlongationAt.of_surjective` of the new module
`Deformations/RepresentationTheory/RaynaudQuotient.lean`, which is the
architecturally neutral home the HOME AUDIT below asks for. The
mathematics is the (α)–(δ) route sketched below, already PROVEN in the
tree as `Interface.lean`'s `IsFlatPointsGroupAt.of_surjective` over the
two sorry-free bricks `exists_etale_subBialgebra_of_points_surjective`
and `exists_hopfOrder_of_subBialgebra`; the only thing that was missing
here was IMPORT REACHABILITY, and that is what the new module supplies.
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
this brick). RESOLVED THE SAME DAY, and the resolution is recorded at
the end of this audit; the analysis below is kept because it is what
dictated the shape of the fix. The same Raynaud content exists in the
tree ONCE more, as
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
performs the unification should move BOTH, not restate a third copy.

RESOLUTION (2026-07-25). Both objections are dodged by a NEW SIBLING of
`FlatProlongation.lean` rather than an edit to it:
`Deformations/RepresentationTheory/RaynaudQuotient.lean`, imported only
by THIS module. Nothing under the `ModThree.lean` cone is disturbed
(the new module is not in it), and `Interface.lean` is not touched at
all (its copies stay, so its separate owner is undisturbed). The new
module carries the WHOLE `IsFlatPointsGroupAt` development inside
`namespace RaynaudQuotient` — the carrier and its repackaging iff, the
tensor/base-change point glue, the closure properties `of_addEquiv`,
`of_subsingleton`, `prod`, `of_injective`, `pi`, the Hopf-order
helpers, and the two quotient bricks with `of_surjective` — so the two
copies cannot clash when `Interface.lean` transitively imports it; and
it exports the prolongation-level
`GaloisRep.HasFlatProlongationAt.of_surjective` consumed just below.
NO THIRD COPY of the mathematics was written: the declarations were
re-homed character-for-character, which is checkable mechanically.

The scope is the whole development rather than the quotient half alone
because TWO further leaves want the other halves and are blocked by the
same cycle one level lower: `hasFlatProlongationAt_of_prod_injection`
and `hasFlatProlongationAt_of_pi_surjection`, both in
`GaloisRepresentation/HardlyRamified/Deformation.lean`, which cannot
import `Modularity/*` at all. `RaynaudQuotient.lean` is outside that
file's import cone, so both become three-line assemblies over it; they
are left to their own owners. What remains of the unification is a pure
DELETION in `Interface.lean` (replace its copied declarations by
`export RaynaudQuotient (…)`), left to that file's owner. -/
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
  GaloisRep.HasFlatProlongationAt.of_surjective h e hsurj he

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
