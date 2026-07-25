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
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
-- the potential-modularity carrier's fields (totally real base field,
-- Galois enabling hypothesis for Brauer induction) live in these:
public import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
public import Mathlib.FieldTheory.Galois.Basic
-- proof-only imports: the PROVEN 3-adic classification (Family-free —
-- see the module docstring for why `Lift.lean`/`Family.lean` must NOT
-- be imported), the shared Family-free deformation development (the
-- 2026-07-24 pillar-α proof-sharing refactor: it discharges pillar α
-- via `exists_hardlyRamified_lift_of_five_le`, and `Lift.lean`'s B6a
-- consumes the SAME development at `k = ZMod ℓ`), and the
-- matrix-charpoly bridges
import Fermat.FLT.GaloisRepresentation.HardlyRamified.Deformation
import Fermat.FLT.GaloisRepresentation.HardlyRamified.Threeadic
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
  sorried): Moret–Bailly's existence theorem for global points with
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
  the second moduli condition).
* **the residual-surjectivity joint** (the same leaf's `hrestr`
  conjunct): Moret–Bailly's `F` is chosen linearly disjoint from the
  splitting field of `ρbar`, so restriction to `G_F` PRESERVES THE
  IMAGE of `ρbar` — the sharp, pin-stateable form of the avoidance
  condition. The irreducibility conjunct of Theorem B is then no
  longer assumed: it is PROVEN from image preservation by
  `isIrreducible_map_of_range_surjective` below.
* **the automorphic joint**
  (`exists_heckeEigensystem_of_hilbertBlumenthalPoint`, sorried): the
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

/-- **The geometric joint of Theorem B** (sorry node — Moret–Bailly
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

PIN AUDIT (2026-07-24): the mathlib pin has NO Moret–Bailly material
(no `Skolem`/`MoretBailly` declarations, no incompressible-neighborhood
existence theorem on Picard-scheme torsors) and no number-field weak
approximation in the required form, and no Hilbert–Blumenthal moduli;
a further decomposition of THIS leaf would have to begin by building
weak approximation on the twisted Hilbert modular variety, i.e. by
building algebraic geometry that the pin does not carry.

SOUNDNESS AUDIT (both ways, 2026-07-24): (i) direct — this is Taylor
2002 §2 with the Galois refinement of §1, a true nonvacuous theorem
whose proof nowhere presupposes Serre's conjecture; (ii) collapse —
the hypothesis set (an irreducible hardly ramified mod-`ℓ`
representation, `ℓ ≥ 5`) is classically unsatisfiable (headline
below), so the statement is also vacuously sound.

ROUTE AUDIT: the odd-prime dichotomy is unavailable here — see the
section docstring above (import cycle AND declaration cycle).

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
      Nonempty (HilbertBlumenthalPoint ℓ F (ρbar.map (algebraMap ℚ F))) :=
  sorry

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

/-- **The automorphic joint of Theorem B** (sorry node — dihedral
residual modularity + modularity lifting at `p`, Taylor 2002 §5): the
compatible system carried by a `HilbertBlumenthalPoint` is the Hecke
eigensystem of a Hilbert newform over `F`; i.e. there is a number
field `E₀` (the Hecke field), a family of Hecke polynomials `hecke₀`,
and a place `ψ₀` of `E₀` over `ℓ`, agreeing with the system's own
polynomials `P` inside `ℚ̄_ℓ` away from a finite set.

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

SOUNDNESS AUDIT (both ways, 2026-07-24): (i) direct — for the intended
instantiation (a point produced by
`exists_hilbertBlumenthalPoint_of_five_le`) this is Taylor 2002 §5;
for an abstract point the abstract-quantification caveat of pillar β
applies (that the compatible system really is the system of an abelian
variety with real multiplication lives in this citation), and (ii)
collapse — the hypothesis set is classically unsatisfiable (headline
below), so the statement is classically true for every package.

ROUTE AUDIT: the odd-prime dichotomy is unavailable here — see the
section docstring above (import cycle AND declaration cycle).

CIRCULARITY GUARD (inherited from pillar β, load-bearing): no
discharge through `Family.lean`, `Lift.lean`, or
`Modularity/Interface.lean`. -/
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
      ∀ w ∉ S, (pt.P w).map pt.ψDℓ = (hecke₀ w).map ψ₀ :=
  sorry

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

/-- **The residual bridge over the Moret–Bailly base** (sorry node;
sub-leaf (c) of the modularity-lifting cut — Chebotarev +
Brauer–Nesbitt + base change): the Khare–Wintenberger lift `ρ`,
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

PIN AUDIT (2026-07-24): the ingredients exist in-tree but on the
WRONG side of the import graph for a direct discharge here —
`exists_conj_of_charFrob_eq_away` and `charFrob_baseChange` both live
in `Modularity/Patching.lean`, which is downstream of this module's
consumer chain; the circularity guard below forbids importing it.  A
future discharge extracts them into a Family-free shared module
exactly as the 2026-07-24 pillar-α refactor did for the deformation
development (`HardlyRamified/Deformation.lean`), then proves this leaf
by restriction of the conjugating isomorphism plus place-by-place
`charFrob` comparison.  That extraction is the recommended attack.

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
          (ρbar.map (algebraMap ℚ F)).charFrob w :=
  sorry

/-- **`R = 𝕋` over the totally real base** (sorry node; sub-leaf (a) of
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
        (ρbar.map (algebraMap ℚ F)).charFrob w) :
    ∃ (badF : Finset (HeightOneSpectrum (NumberField.RingOfIntegers F)))
      (aF dF : HeightOneSpectrum (NumberField.RingOfIntegers F) →
        AlgebraicClosure ℚ_[ℓ])
      (ιO : O →+* AlgebraicClosure ℚ_[ℓ]) (_ : Function.Injective ιO),
      ∀ w ∉ badF,
        ((ρ.map (algebraMap ℚ F)).charFrob w).map ιO =
          X ^ 2 - C (aF w) * X + C (dF w) :=
  sorry

/-- **Carayol local-global normalization and Shimura rationality**
(sorry node; sub-leaf (b) of the modularity-lifting cut — Shimura /
Carayol 1986): the raw `ℚ̄_ℓ`-valued Hecke eigensystem `(aF, dF)` of
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

PIN AUDIT (2026-07-24): the mathlib pin has no Hilbert modular forms
and no Hecke algebras over a totally real base (`grep Hilbert` over
`Mathlib/NumberTheory/`: only Hilbert's theorem 90 and Hilbert basis),
so no part of this statement can be reduced to library material; it is
a sharply-stated citation node whose only sound discharge is the
construction of Hilbert-modular Hecke theory.

SOUNDNESS AUDIT (both ways, 2026-07-24): (i) direct — for the intended
instantiation (`(aF, dF)` produced by
`exists_heckeEigensystem_of_congruentSeed`, hence the eigensystem of
an actual Hilbert newform) this is Shimura rationality plus Carayol
verbatim; for an abstract `(aF, dF)` merely satisfying `hshape` the
abstract-quantification caveat applies IN FULL FORCE — nothing formal
forces an abstract family of `ℚ̄_ℓ`-values to be algebraic, and the
hypothesis that `aF` IS a newform eigensystem lives entirely in this
citation (the same shape as the sibling leaf
`exists_threeadic_realization_of_heckePackage`, whose `hmod`
hypothesis carries the same unstated content); (ii) collapse — the
hypothesis set (an irreducible hardly ramified mod-`ℓ`
representation, `ℓ ≥ 5`) is classically unsatisfiable (headline
below), so the statement is classically true for every package.

CIRCULARITY GUARD (inherited from pillar β, load-bearing): no
discharge through `Family.lean`, `Lift.lean`, or
`Modularity/Interface.lean`. -/
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
      (∀ w ∉ badF, ψℓ (a w) = aF w) ∧ ∀ w ∉ badF, ψℓ (d w) = dF w :=
  sorry

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

/-- **The Hilbert-modular `3`-adic realization, integral-domain form**
(sorry node — Carayol 1986 / Taylor 1989; THE citation leaf of the
`3`-adic realization node): a Hilbert-modular Hecke eigensystem
`(E, heckeF)` over the totally real field `F` — witnessed as modular
by the `ℓ`-adic matching clause `hmod` for the lift `ρ` — has a
`3`-adic Galois realization: a representation `τF` of `G_F` on a
stable lattice over a local DOMAIN `B` which is module-finite over
`ℤ_3` and contains `ℤ_3` (classically the integers of the completion
`E_λ`, `λ | 3`), with the same Hecke polynomials through a place `ψ₃`
of `E` over `3`.

This is the sharpest citation-only form of the node: everything here
is produced verbatim by the construction, and the one structural
property the consumer additionally wants — `ℤ_3`-FREENESS of `B` — is
NOT asserted here, because it is a formal consequence of the rest
(`free_of_finite_of_algebraMap_padicInt_injective` above). The
consumer `exists_threeadic_realization_of_heckePackage` is therefore a
PROVEN assembly over this single leaf.

Literature: Carayol, *Sur les représentations ℓ-adiques associées aux
formes modulaires de Hilbert*, Ann. Sci. ÉNS 19 (1986) (construction
and local-global compatibility for `[F : ℚ]` odd, or via
Jacquet–Langlands at a finite place); Taylor, *On Galois
representations associated to Hilbert modular forms*, Invent. Math. 98
(1989) (the remaining even-degree cases, by congruences); the stable
lattice exists because `G_F` is compact and `E_λ` is local (standard:
Serre, *Abelian ℓ-adic representations*, I §1), and `B` is then the
ring of integers of `E_λ` — a local domain, module-finite over `ℤ_3`,
into which `ℤ_3` embeds.

PIN AUDIT (2026-07-24): the mathlib pin has no Hilbert modular forms,
no Shimura curves and no automorphic Galois representations of any
kind (`grep Hilbert.*modular`, `grep Shimura` over `Mathlib/`: nothing
in this direction), so the construction itself is irreducibly a
citation. What the pin DOES have is the commutative algebra of the
lattice step, which is why that half has been split off and proven.

ROUTE AUDIT (dichotomy, 2026-07-24). Two routes to the `3`-adic
member of the compatible system were weighed at this joint:

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

SOUNDNESS AUDIT (both ways, 2026-07-24): (i) direct — for the intended
instantiation (`(E, heckeF)` the eigensystem of the Hilbert newform
attached to `ρ|_{G_F}` by `exists_heckePackage_of_seed`) this is
Carayol/Taylor verbatim; for an abstract eigensystem merely satisfying
`hmod` the abstract-quantification caveat applies (the hypothesis that
`heckeF` IS a newform eigensystem lives in this citation), and (ii)
collapse — the hypothesis set (an irreducible hardly ramified mod-`ℓ`
representation, `ℓ ≥ 5`) is classically unsatisfiable (headline
below), so the statement is classically true for every package.

CIRCULARITY GUARD (inherited from pillar β, load-bearing): no
discharge through `Family.lean`, `Lift.lean`, or
`Modularity/Interface.lean`. -/
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
      ∀ w ∉ badF, (τF.charFrob w).map ιB = (heckeF w).map ψ₃ :=
  sorry

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

* (a) the CITATION half,
  `exists_threeadic_realization_domain_of_heckePackage` — the
  automorphic construction of the `3`-adic representation with the
  right Frobenius characteristic polynomials, over the coefficient
  ring the construction literally produces: a local DOMAIN,
  module-finite over `ℤ_3`, containing `ℤ_3`. This is the sole
  residual sorry of the node, and it is strictly weaker than the
  statement it replaces (it does not assert `ℤ_3`-freeness);
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

/-- **Cyclic refinement of a solvable subgroup** (sorry node; FOUNDER
leaf, pure finite group theory — the group-theoretic engine of the
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
the step condition being vacuous. -/
theorem exists_cyclicRefinement_of_isSolvable {G : Type*} [Group G]
    [Finite G] (H : Subgroup G) (hH : IsSolvable H) :
    ∃ (n : ℕ) (C : ℕ → Subgroup G),
      C 0 = ⊥ ∧ C n = H ∧
      ∀ i < n, C i ≤ C (i + 1) ∧
        ∃ _ : ((C i).subgroupOf (C (i + 1))).Normal,
          IsCyclic (C (i + 1) ⧸ (C i).subgroupOf (C (i + 1))) :=
  sorry

/-- **The base of the descent chain — the witness's own eigensystem,
read over `F^⊥`** (sorry node; a pure TRANSPORT leaf, no arithmetic
content): the carrier's modularity clause `Wit.modularF` is a statement
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

WHY IT IS A LEAF (2026-07-24): the transport is not formally free on
this pin. `GaloisRep.map` is defined through
`Field.absoluteGaloisGroup.map`, which "relies on an arbitrarily chosen
embedding of the algebraic closures" (`GaloisRep.lean`), and `charFrob`
is evaluated at `Field.AbsoluteGaloisGroup.adicArithFrob`, itself
defined through an arbitrary choice of a valuation on the algebraic
closure extending `v`. Independence of `charFrob` from those choices
(equivalently: its invariance under the conjugation relating two
choices) is exactly the missing API — `GaloisRep.charFrob` has no
transport lemma along an `AlgEquiv` of number fields anywhere in the
project or in the pin. Writing that API is the content of this leaf; it
is FORMAL work, not literature, and it is independent of everything
else in the descent.

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
    HeckeSystemDescendsTo Wit ⊥ :=
  sorry

/-- **One cyclic step of solvable base change** (sorry node; THE
literature node of the `ℓ`-adic solvable descent — Langlands 1980,
Arthur–Clozel 1989): if the eigensystem of `ρ` descends to the fixed
field `L = F^C`, and `C ≤ D` is normal with CYCLIC quotient `D/C`
(equivalently: `L/M` is a cyclic Galois extension, where `M = F^D`),
then the eigensystem descends to `M`.

Classically, in three moves — the joints of the literature argument, in
order:

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
vendorable. This is the terminal citation node of the descent: below it
lie the trace formula and the twisted character identity, not further
Galois-theoretic bookkeeping.

SOUNDNESS AUDIT (both ways, 2026-07-24): (i) direct — for the carrier
produced by the inhabitation leaf and a system produced by the chain
this is the argument above, with the Hecke-field enlargements landing
in `E` by the carrier's normalization; for an abstract carrier the
abstract-quantification caveat of pillar β applies (in particular
nothing formal ties the twisting-character values into `E`; that
identification is part of the citation), and (ii) collapse — the
hypothesis package is classically unsatisfiable (headline below), so
the statement is classically true for every package.

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
    HeckeSystemDescendsTo Wit D :=
  sorry

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
`heckeSystemDescendsTo_of_cyclic_step` (the literature node: one cyclic
step of base change and descent), glued by induction on the chain
index through the shared shape `HeckeSystemDescendsTo`. The fixed
fields are taken as restrictions from `ℚ` at every stage, so the
induction needs no compatibility of restrictions along the tower.
Those three leaves are now the residual sorries of this node; the
circularity guard above binds the two arithmetic ones (the refinement
leaf is pure group theory — nothing arithmetic to route through).

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

/-- **Brauer gluing, trace coefficient — the induced-character
expansion** (sorry node; the arithmetic HALF of the Brauer gluing
below, and the only coefficient carrying automorphy content): given a
Brauer decomposition of the trivial character of `Gal(F/ℚ)` into
solvable-induced one-dimensional pieces (`hbrauer`) and, for each
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
through `Family.lean`, `Lift.lean`, or `Modularity/Interface.lean`. -/
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
    (φ : Fin n → (Wit.F ≃ₐ[ℚ] Wit.F) → ℂ) (c : Fin n → ℤ)
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
          ∈ Set.range Wit.ψℓ :=
  sorry

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
stays inside the citation leaf `exists_threeadicBrauerSum_of_witness`
below, which produces the Brauer sum already in coefficient-ring
(lattice) form — classically the integers `O_{E_λ}` of the completion.
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

/-- **Brauer descent, `3`-adic side — the virtual sum is a true
representation on a stable lattice** (sorry node; the citation
sub-leaf of the `3`-adic realization, BLGGT §5.3): given the descended
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

PIN AUDIT (2026-07-24): the lattice step is NOT separable into an
in-tree formal lemma at this pin — mathlib carries no stable-lattice
material for compact groups (see
`module_free_padicInt_of_algebraMap_injective` above), so the leaf is
stated directly in lattice (coefficient-ring) form, exactly the shape
the realization carrier and the proven `3`-adic classification
consume. What was split off as formal is the freeness normalization
(that lemma) and the interpolant uniqueness (`heckePoly_transport`).

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
          (Pv hq.toHeightOneSpectrumRingOfIntegersRat).map Wit.ψ₃ :=
  sorry

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
on a stable lattice (`exists_threeadicBrauerSum_of_witness`, the
single residual citation sub-leaf of this node — BLGGT §5.3) + two
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

/-- **Carayol local-global compatibility away from the residue
characteristic — the conductor of the descended system** (sorry node,
CITATION LEAF): the Brauer-descended `3`-adic member `τ` has a
conductor `N` in the usual sense, namely

* `τ` is unramified at every prime `p ∤ 3N` (clause 1), and
* every prime `p ∤ 3` dividing `N` is a prime at which the `ℓ`-adic
  member `ρ` itself genuinely ramifies, and is distinct from `ℓ`
  (clause 2).

This is exactly the literature joint of the ramification transfer, and
nothing more: it is the statement that the conductor is an invariant of
the compatible system away from the residue characteristic. Clause 1 is
Carayol's local-global compatibility at the places `p ∤ 3` (the
automorphic side is unramified at every place prime to the level, and
the Weil–Deligne parameter of the Galois side at such a place matches
it, so inertia at `p` acts trivially on `τ`). Clause 2 is the
member-independence half of the same compatibility, read on the
`ℓ`-adic member of the same system: a place `p ∤ 3` in the support of
the conductor carries a ramified Weil–Deligne parameter, and that
parameter is member-independent for `p` prime to BOTH residue
characteristics, so `ρ` is ramified at `p` too; the extra clause
`p ≠ ℓ` is the Fontaine–Laffaille/Carayol input at the `ℓ`-adic
member's own residue characteristic — `ρ` is FLAT at `ℓ`
(`hρ.isFlat`), i.e. crystalline of Hodge–Tate weights `{0, 1}`, which
is the local condition corresponding to level prime to `ℓ`, so `ℓ`
does not divide the conductor.

Note that no numerical value of `N` is asserted here: the numerical
"conductor divides `2`" of the informal argument is DERIVED from these
two clauses together with the hardly ramified hypotheses on `ρ` in the
consumer below (`threeadicRealization_isUnramified_of_witness`), which
is where the transport lives. Correspondingly this leaf is stated with
`N` existentially quantified, so any correct route to the conductor —
via the level of the descended Hilbert newform, via the Artin conductor
of `τ`, or via the local Langlands parameters — may discharge it.

Literature: Carayol, *Sur les représentations `ℓ`-adiques associées aux
formes modulaires de Hilbert*, Ann. Sci. ÉNS 19 (1986) (local-global
compatibility fixing the conductor); Khare–Wintenberger, *Serre's
modularity conjecture (I)*, Invent. Math. 178 (2009), §5 (strict
compatibility away from the residue characteristic); BLGGT, *Potential
automorphy and change of weight*, Ann. of Math. 179 (2014), §5.5
(strict compatibility of the constructed system); Fontaine–Laffaille,
*Construction de représentations p-adiques*, Ann. Sci. ÉNS 15 (1982)
(flat at `ℓ` ⟺ level prime to `ℓ` in weight `2`).

SOUNDNESS AUDIT (both ways, 2026-07-24): (i) direct — for the
realization produced by the construction leaf this is Carayol's
theorem as cited, applied to the descended eigensystem on both sides of
the compatible family; for an abstract realization the
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
`Modularity/Interface.lean`. -/
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
          ¬ ρ.IsUnramifiedAt hp.toHeightOneSpectrumRingOfIntegersRat) :=
  sorry

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

/-- **The Fontaine–Laffaille local shape at `3`** (sorry node — the
literature joint of the flatness transfer, isolated 2026-07-24 out of
`threeadicRealization_isFlat_of_witness`, whose open-ideal transport
is PROVEN below): every NONTRIVIAL finite congruence quotient
`(A ⧸ I) ⊗_A (Fin 2 → A)` of the Brauer-descended `3`-adic member is
the group of `ℚ̄_3`-points of the generic fibre of a finite flat group
scheme over `ℤ_3` — the package spelled by
`GaloisRep.HasFlatProlongationAt`.

Classically: the compatible system attached to the descended
eigensystem has parallel weight `2` and conductor prime to `3`, so its
`3`-adic member `τ` is crystalline at `3` with Hodge–Tate weights
`{0, 1}` (Carayol/Taylor local-global compatibility at `p = ℓ` for `p`
prime to the level). Over `ℤ_3` the absolute ramification index is
`e = 1 < 2 = p - 1`, which is exactly the Fontaine–Laffaille range:
the crystalline lattice `Fin 2 → A` is the Tate module of a
`3`-divisible group over `ℤ_3` (Raynaud/Fontaine–Laffaille in weight
`2`), the Fontaine–Laffaille functor from finite flat `3`-group
schemes over `ℤ_3` to finite `G_{ℚ_3}`-modules is exact and fully
faithful, and its essential image is closed under subobjects and
quotients. The finite quotient `(A ⧸ I) ⊗_A (Fin 2 → A)` of the
stable lattice therefore prolongs — "every finite quotient of the
stable lattice prolongs", the blueprint's "flat at 3".

Only NONTRIVIAL quotients (`I ≠ ⊤`) are asserted: at `I = ⊤` the
congruence quotient is a single point and the transport below
discharges the case outright with the trivial Hopf algebra
(`GaloisRep.hasFlatProlongationAt_of_subsingleton`), so the literature
is not cited for it. Openness of `I` is likewise not assumed — the
transport converts it into the finiteness hypothesis, which is the
form the Fontaine–Laffaille statement takes.

Literature: Fontaine–Laffaille, *Construction de représentations
p-adiques*, Ann. Sci. ÉNS 15 (1982); Raynaud, *Schémas en groupes de
type (p, …, p)*, Bull. SMF 102 (1974); Carayol, Ann. Sci. ÉNS 19
(1986) and Taylor, Invent. Math. 98 (1989) (the weight-2 local shape
at primes over `p` prime to the level); Breuil, *Groupes p-divisibles,
groupes finis et modules filtrés*, Ann. of Math. 152 (2000) (the
range-free refinement); BLGGT §5.5. FLT blueprint ch. 4: "flat at 3".

SOUNDNESS AUDIT (both ways, 2026-07-24): (i) direct — for the
realization produced by the construction leaf this is
Fontaine–Laffaille/Raynaud as above; for an abstract realization the
abstract-quantification caveat of pillar β applies, and (ii) collapse
— the hypothesis set is classically unsatisfiable (headline below),
so the statement is classically true for every package.

CIRCULARITY GUARD (inherited from pillar β, load-bearing): no
discharge through `Family.lean`, `Lift.lean`, or
`Modularity/Interface.lean`. -/
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
        (Fact.out : Nat.Prime 3)) :=
  sorry

/-- **Condition transfer, flatness at `3` — Fontaine–Laffaille**
(DECOMPOSED 2026-07-24 — now a PROVEN transport over the single
literature leaf
`threeadicRealization_hasFlatProlongationAt_of_finite_quotient`
above): the Brauer-descended `3`-adic member is flat at `3` in the
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

/-- **The Weil–Deligne type at `2` of the `3`-adic member, in lattice
coordinates** (sorry node — the LITERATURE JOINT of the tameness
transfer, cut out 2026-07-24): there is an `A`-basis of the stable
lattice `Fin 2 → A` in which the whole decomposition group at `2` acts
through UPPER-triangular matrices, the diagonal `(1,1)`-entry being the
scalar `δ g 1` of an unramified square-trivial character `δ` of
`G_{ℚ_2}`.

This is exactly the classical statement "the Weil–Deligne parameter of
the compatible system at `2` is constant away from the residue
characteristic (`2 ≠ 3`) and equals that of the hardly ramified `ρ`",
written in the coordinates the lattice provides: `ρ`'s type at `2` is
an extension of an unramified square-trivial character by its
cyclotomic twist (`hρ.isTameAtTwo` together with the cyclotomic
determinant), the type is carried across the system by strict
compatibility (Khare–Wintenberger (I) §5; Carayol local–global
compatibility at the bad places, applied to the descended Hilbert
newform, whose conductor is pinned by the witness's conductor data),
and the stable-lattice normalization of the construction leaf
(`exists_threeadicRealization_of_witness`) turns the `E_λ`-rational
stable line into a saturated `A`-line, i.e. into the first vector of an
`A`-basis. The character `δ` is handed over as a `GaloisRep` because it
IS the quotient character of the constant type — in particular
continuous, being the local component of the compatible system's
nebentypus-free unramified twist.

Literature: Khare–Wintenberger, *Serre's modularity conjecture (I)*,
Invent. Math. 178 (2009), §5 (strict compatibility of Weil–Deligne
parameters away from the residue characteristic); BLGGT, *Potential
automorphy and change of weight*, Ann. of Math. 179 (2014), §5.5;
Carayol, *Sur les représentations ℓ-adiques associées aux formes
modulaires de Hilbert*, Ann. Sci. ÉNS 19 (1986) (local–global
compatibility at the bad places). FLT blueprint ch. 4: "tame at 2".

SOUNDNESS AUDIT (both ways, 2026-07-24): (i) direct — for the
realization produced by the construction leaf this is the
Weil–Deligne-type transfer above, read in a saturated basis; for an
abstract realization the abstract-quantification caveat of pillar β
applies, and (ii) collapse — the hypothesis set is classically
unsatisfiable (the headline
`not_isIrreducible_of_isHardlyRamified_of_five_le` below refutes
`hirr`), so the statement is classically true for every package.

CIRCULARITY GUARD (inherited from pillar β, load-bearing): no
discharge through `Family.lean`, `Lift.lean`, or
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
            (Rlz.τ.map (algebraMap ℚ ℚ_[2]) g) 1 1 = δ g 1 :=
  sorry

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
