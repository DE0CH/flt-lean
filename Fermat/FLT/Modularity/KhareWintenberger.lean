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
interface's CIRCULARITY GUARD forbids. The three sorried pillars below
are consequently FAMILY-FREE restatements, and their docstrings record,
pillar by pillar, which in-tree twin they mirror and which discharge
routes are sound:

* pillar α (`exists_hardlyRamified_lift_residual_of_five_le`) mirrors
  `Lift.lean`'s B6a and may eventually SHARE its proof by a bookkeeping
  refactor (moving the deformation development out of `Lift.lean`'s
  `Family.lean` import);
* pillar β (`exists_threeadic_compatible_member_of_five_le`) mirrors
  B6b + the 3-adic specialization, but its in-tree twin's proof
  (through `Family.lean`) is UNSOUND here — its only sound discharge is
  the potential-modularity construction. This pillar is where the
  genuine depth of the residual-modularity leaf now lives (2026-07-24:
  DISCHARGED as a proven assembly over the potential-modularity
  carrier `PotentialModularityWitness`; the depth now lives in its
  three sorried leaves — carrier inhabitation via Taylor 2002 +
  modularity lifting over totally real fields, the ℓ-adic Brauer
  descent of the Hecke eigensystem to `ℚ`, and the hardly ramified
  `3`-adic member via BLGGT §5 — see their docstrings);
* pillar γ (`not_isIrreducible_of_charFrob_eisenstein`) is the
  finite-coefficient-field transfer of the PROVEN
  `not_isIrreducible_of_charFrob_eq`, whose proof consumes only
  Family-free material from `Chebotarev.lean` — a mechanical
  generalization, no new mathematics.

The assembly `not_isIrreducible_of_isHardlyRamified_of_five_le` is
PROVEN below from the three pillars plus the PROVEN 3-adic machinery
(`IsHardlyRamified.exists_frobenius_triangular`, `Threeadic.lean` — the
trace form of the same classification is B6c,
`IsHardlyRamified.three_adic`).

(Import note, 2026-07-24: `Chebotarev.lean` — the home of pillar γ's
proof ingredients — is deliberately NOT imported: the assembly does not
need it, thanks to the triangular-Frobenius route through
`Threeadic.lean`; the agent proving pillar γ adds the import then.)
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
-- be imported) and the matrix-charpoly bridges
import Fermat.FLT.GaloisRepresentation.HardlyRamified.Threeadic
import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff

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

IN-TREE TWIN: `exists_hardlyRamifiedLift` (`Lift.lean`, stated over
`ZMod ℓ`), already decomposed there into deformation-theoretic leaves
(Mazur representability, Carayol subring descent, mod-`ℓ` finiteness,
minimal presentations). That module imports `Family.lean` and is
therefore un-importable here (cycle); its lifting development does not
mathematically depend on the family machinery, so a future bookkeeping
refactor splitting it into a Family-free module can discharge this
pillar by delegation (generalizing `ZMod ℓ` to the finite coefficient
field `k`, which its deformation theory already handles classically).
Until then the two statements are deliberately kept in sync.
CIRCULARITY GUARD: must not be proven through `Family.lean`,
`Lift.lean`, or `Modularity/Interface.lean`. -/
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
  sorry

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
through `Family.lean`, `Lift.lean`, or `Modularity/Interface.lean`. -/
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
    Nonempty (PotentialModularityWitness ℓ O ρ) :=
  sorry

/-- **Brauer descent, `ℓ`-adic side — the Hecke-field polynomial
system over `ℚ`** (sorry node): given a potential-modularity carrier
for the lift `ρ`, the Frobenius characteristic polynomials of `ρ` at
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
`Modularity/Interface.lean`. -/
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
          (Pv hq.toHeightOneSpectrumRingOfIntegersRat).map Wit.ψℓ :=
  sorry

/-- **Brauer descent, `3`-adic side — the hardly ramified `3`-adic
member over `ℚ`** (sorry node): given a potential-modularity carrier
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
            P.map Wit.ψ₃ :=
  sorry

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
BLGGT §5.5, Fontaine–Laffaille, strict compatibility), glued by
uniting the two exceptional sets and instantiating the `3`-adic
compatibility clause at the descended polynomials. Those three
leaves are now the residual sorries of this pillar; the circularity
guard above binds each of them. -/
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

/-- **Pillar γ — Chebotarev + Brauer–Nesbitt over a finite coefficient
field** (sorry node — mechanical transfer, no new mathematics): a
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
    ¬ ρbar.IsIrreducible :=
  sorry

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
