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
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
-- pillar-γ proof-only imports (see the module docstring's import note):
-- the Family-free Chebotarev/Brauer–Nesbitt machinery and its Kolchin
-- ingredients
import Fermat.FLT.GaloisRepresentation.Chebotarev
import Fermat.FLT.GaloisRepresentation.BrauerNesbitt
import Mathlib.Tactic.NoncommRing

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

/-- **Moret–Bailly base production** (sorry node — Taylor 2002,
Theorem B): for the irreducible hardly ramified residual
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

PIN AUDIT (2026-07-24): the mathlib pin has NO Moret–Bailly material
and no number-field weak approximation in the required form (no
`Skolem`/`MoretBailly` declarations; `Mathlib/NumberTheory/
NumberField/` carries no incompressible-neighborhood existence
theorem on Picard-scheme torsors), so this leaf is a sharply-stated
citation node; a future decomposition would begin with weak
approximation on the twisted Hilbert modular variety.

SOUNDNESS AUDIT (both ways, 2026-07-24): (i) direct — this is Taylor
2002 Theorem B verbatim (with the Galois refinement of §1 and the
irreducibility preservation built into the avoidance set), a true
nonvacuous theorem: its proof (Moret–Bailly + converse theorems +
residually dihedral lifting) nowhere presupposes Serre's conjecture;
(ii) collapse — the hypothesis set (an irreducible hardly ramified
mod-`ℓ` representation, `ℓ ≥ 5`) is classically unsatisfiable
(headline below), so the statement is also vacuously sound.

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
      Nonempty (MoretBaillySeed ℓ F (ρbar.map (algebraMap ℚ F))) :=
  sorry

/-- **Modularity lifting over the totally real base** (sorry node —
Kisin/Taylor MLT + Carayol local-global): over the Moret–Bailly base
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

MLT-SHARING NOTE (2026-07-24): the project's deformation-theoretic
patching vocabulary (`Patching.lean`: `HardlyRamifiedFiniteDeformation`,
strict Mazur representability, `exists_conj_of_charFrob_eq_away`) is
pinned to base field `ℚ` — `IsHardlyRamified` itself hard-codes the
local conditions at the rational places `2` and `ℓ` — so this leaf
cannot yet be discharged through a shared general-base MLT node; if
`Patching.lean`'s pillars are later generalized over a totally real
base, this leaf is the natural consumer.

CIRCULARITY GUARD (inherited from pillar β, load-bearing): no
discharge through `Family.lean`, `Lift.lean`, or
`Modularity/Interface.lean`. -/
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
          (heckeF w).map ψℓ :=
  sorry

/-- **The Hilbert-modular `3`-adic realization** (sorry node —
Carayol 1986 / Taylor 1989): a Hilbert-modular Hecke eigensystem
`(E, heckeF)` over the totally real field `F` — witnessed as modular
by the `ℓ`-adic matching clause `hmod` for the lift `ρ` — has a
`3`-adic Galois realization: a representation `τF` of `G_F` on a
stable lattice over a local ring `B` finite FREE over `ℤ_3`
(classically the integers of the completion `E_λ`, `λ | 3`), with the
same Hecke polynomials through a place `ψ₃` of `E` over `3`.

Literature: Carayol, *Sur les représentations ℓ-adiques associées aux
formes modulaires de Hilbert*, Ann. Sci. ÉNS 19 (1986) (construction
and local-global compatibility for `[F : ℚ]` odd or via
Jacquet–Langlands at a finite place); Taylor, *On Galois
representations associated to Hilbert modular forms*, Invent. Math.
98 (1989) (the remaining even-degree cases, by congruences); the
stable lattice exists because `G_F` is compact and `E_λ` is local
(standard: Serre, *Abelian ℓ-adic representations*, I §1). The
freeness of `B` over `ℤ_3` is the freeness of the integers of a
finite extension of `ℚ_3`.

SOUNDNESS AUDIT (both ways, 2026-07-24): (i) direct — for the
intended instantiation (`(E, heckeF)` the eigensystem of the Hilbert
newform attached to `ρ|_{G_F}` by `exists_heckePackage_of_seed`) this
is Carayol/Taylor verbatim; for an abstract eigensystem merely
satisfying `hmod` the abstract-quantification caveat applies (the
hypothesis that `heckeF` IS a newform eigensystem lives in this
citation), and (ii) collapse — the hypothesis set (an irreducible
hardly ramified mod-`ℓ` representation, `ℓ ≥ 5`) is classically
unsatisfiable (headline below), so the statement is classically true
for every package.

CIRCULARITY GUARD (inherited from pillar β, load-bearing): no
discharge through `Family.lean`, `Lift.lean`, or
`Modularity/Interface.lean`. -/
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
      ∀ w ∉ badF, (τF.charFrob w).map ιB = (heckeF w).map ψ₃ :=
  sorry

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

/-- **Brauer's induction theorem — trivial-character form** (sorry
node; FOUNDER leaf, pure finite group theory — the group-theoretic
engine of the `ℓ`-adic Brauer descent): for a finite group `G` the
trivial character is a `ℤ`-linear combination of characters induced
from one-dimensional characters of SOLVABLE subgroups. The data is
presented explicitly and self-containedly: subgroups `H i`,
one-dimensional characters of `H i` carried as functions
`φ i : G → ℂ` extended by zero off `H i` (the three conditions say
exactly that: `φ i` vanishes outside `H i`, sends `1` to `1`, and is
multiplicative on `H i` — its values on `H i` are then |G|-th roots of
unity, each element having finite order), and integers `c i`, such
that the Frobenius-formula combination
`Σᵢ cᵢ · |Hᵢ|⁻¹ · Σ_{x ∈ G} φᵢ(x⁻¹ g x)` — the `i`-th inner term is
the induced character `Ind_{Hᵢ}^G χᵢ` evaluated at `g` — is the
constant `1`.

Literature: Brauer's induction theorem — Serre, *Linear
Representations of Finite Groups*, §10.5, Theorems 18–19 (every
character of `G` is a `ℤ`-linear combination of characters induced
from one-dimensional characters of `p`-elementary subgroups; apply to
the trivial character); Isaacs, *Character Theory of Finite Groups*,
Theorem 8.4; Curtis–Reiner §15. A `p`-elementary group (cyclic ×
`p`-group) is nilpotent, hence solvable — solvability is the weaker
form recorded here because it is exactly what solvable base change
consumes downstream.

PIN AUDIT (2026-07-24, hard search): the mathlib pin has the induction
functor (`Representation.ind`, `Mathlib/RepresentationTheory/
Induced.lean` — a categorical adjunction, no character formula) and
basic character theory (`Mathlib/RepresentationTheory/Character.lean`:
orthogonality only), but NO induced-character formula, NO virtual
characters, NO Artin or Brauer induction in any form (`grep Brauer`
over `Mathlib/`: only Brauer GROUPS of fields). The leaf is therefore
stated self-containedly (no `FDRep`, no decidability or subtype
baggage — the extension-by-zero form makes the induced character an
unrestricted sum over `G`), in the exact shape its consumer
(`exists_heckeField_system_of_witness_of_pieces`) needs. It is
genuinely provable in-tree — finite character theory over `ℂ` — but is
a real project (elementary subgroups, algebraic integrality of
character values, the Brauer/Banaschewski counting argument), hence a
leaf.

SOUNDNESS AUDIT (2026-07-24): a true classical theorem with NO vacuity
route — this leaf carries no arithmetic hypotheses, so unlike the
arithmetic leaves of this module it must be (and is) directly true as
stated: Serre §10.5, Theorem 19, applied to `1_G`, with each
`p`-elementary subgroup relabelled solvable. Edge `G = 1`: take
`n = 1`, `H 0 = ⊤`, `φ 0 = 1`, `c 0 = 1`. -/
theorem brauer_induction_trivial_character (G : Type*) [Group G]
    [Fintype G] :
    ∃ (n : ℕ) (H : Fin n → Subgroup G) (φ : Fin n → G → ℂ)
      (c : Fin n → ℤ),
      (∀ i, IsSolvable (H i)) ∧
      (∀ i, ∀ g ∉ H i, φ i g = 0) ∧
      (∀ i, φ i 1 = 1) ∧
      (∀ i, ∀ a ∈ H i, ∀ b ∈ H i, φ i (a * b) = φ i a * φ i b) ∧
      (∀ g : G, ∑ i, (c i : ℂ) * (Nat.card (H i) : ℂ)⁻¹ *
        ∑ x : G, φ i (x⁻¹ * g * x) = 1) :=
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
`Modularity/Interface.lean`. -/
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
            w).map Wit.ιO = (P w).map Wit.ψℓ :=
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
`Modularity/Interface.lean`. -/
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
    ∃ (S₀ : Finset (HeightOneSpectrum (NumberField.RingOfIntegers ℚ)))
      (Pv : HeightOneSpectrum (NumberField.RingOfIntegers ℚ) →
        Polynomial Wit.E),
      ∀ (q : ℕ) (hq : q.Prime),
        hq.toHeightOneSpectrumRingOfIntegersRat ∉ S₀ →
        q ≠ 2 → q ≠ 3 → q ≠ ℓ →
        (ρ.charFrob hq.toHeightOneSpectrumRingOfIntegersRat).map Wit.ιO =
          (Pv hq.toHeightOneSpectrumRingOfIntegersRat).map Wit.ψℓ :=
  sorry

/-- **Brauer descent, `ℓ`-adic side — the Hecke-field polynomial
system over `ℚ`** (PROVEN 2026-07-24 as an assembly over the three
Brauer-descent leaves above; the depth now lives in
`brauer_induction_trivial_character`,
`exists_descended_heckeSystem_of_solvable` and
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
Brauer data and the chosen piece systems. Those three leaves are now
the residual sorries of this node; the circularity guard above binds
the two arithmetic ones (the Brauer leaf is pure group theory — no
guard needed, nothing arithmetic to route through). -/
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

/-- **Brauer descent, `3`-adic side — construction of the raw
realization** (sorry node — BLGGT §5.3, the Brauer-trick
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
    Nonempty (ThreeadicRealization ℓ O ρ Wit) :=
  sorry

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

/-- **Condition transfer, ramification — unramified outside `{2, 3}`**
(sorry node): the Brauer-descended `3`-adic member is unramified at
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

SOUNDNESS AUDIT (both ways, 2026-07-24): (i) direct — for the
realization produced by the construction leaf this is the strict
compatibility transfer above; for an abstract realization the
abstract-quantification caveat of pillar β applies, and (ii) collapse
— the hypothesis set is classically unsatisfiable (headline below),
so the statement is classically true for every package.

CIRCULARITY GUARD (inherited from pillar β, load-bearing): no
discharge through `Family.lean`, `Lift.lean`, or
`Modularity/Interface.lean`. -/
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
      Rlz.τ.IsUnramifiedAt hp.toHeightOneSpectrumRingOfIntegersRat :=
  sorry

/-- **Condition transfer, flatness at `3` — Fontaine–Laffaille**
(sorry node): the Brauer-descended `3`-adic member is flat at `3`.
Classically: the system has parallel weight `2` and conductor prime
to `3`, so its `3`-adic member is crystalline at `3` with
Hodge–Tate weights `{0, 1}` (Carayol/Taylor local-global
compatibility at `p = ℓ` for `p` prime to the level, via
Fontaine–Laffaille theory in weight `2` — equivalently Raynaud: a
lattice in a crystalline representation with weights in `{0, 1}` is
the generic fiber of a finite flat group scheme over `ℤ_3`, and every
finite quotient of the stable lattice prolongs); this is the
blueprint's "flat at 3".

Literature: Fontaine–Laffaille, *Construction de représentations
p-adiques*, Ann. Sci. ÉNS 15 (1982); Raynaud, *Schémas en groupes de
type (p, …, p)*, Bull. SMF 102 (1974); Carayol, Ann. Sci. ÉNS 19
(1986) and Taylor, Invent. Math. 98 (1989) (the weight-2 local shape
at primes over `p` prime to the level); BLGGT §5.5. FLT blueprint
ch. 4: "flat at 3".

SOUNDNESS AUDIT (both ways, 2026-07-24): (i) direct — for the
realization produced by the construction leaf this is
Fontaine–Laffaille/Raynaud as above; for an abstract realization the
abstract-quantification caveat of pillar β applies, and (ii) collapse
— the hypothesis set is classically unsatisfiable (headline below),
so the statement is classically true for every package.

CIRCULARITY GUARD (inherited from pillar β, load-bearing): no
discharge through `Family.lean`, `Lift.lean`, or
`Modularity/Interface.lean`. -/
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
        (Fact.out : Nat.Prime 3)) :=
  sorry

/-- **Condition transfer, tameness at `2` — constant Weil–Deligne
type** (sorry node): the Brauer-descended `3`-adic member is tame at
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

CIRCULARITY GUARD (inherited from pillar β, load-bearing): no
discharge through `Family.lean`, `Lift.lean`, or
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
        (∀ g' : Field.absoluteGaloisGroup ℚ_[2], δ g' * δ g' = 1) :=
  sorry

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
three (`brauer_induction_trivial_character`,
`exists_descended_heckeSystem_of_solvable`,
`exists_heckeField_system_of_witness_of_pieces`), and the realization
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
