/-
GaloisRepresentation/HardlyRamified/HilbertModularity.lean — own work for
the Fermat project (not vendored from the FLT project).

# `R_F = T_F`: the Hilbert-modular route to the potential-modularity leaf

This module is the KW-free upstream home of the **`F`-level** modularity
input of pillar α: the deformation ring `R_F` of the restriction of a
hardly ramified representation to the absolute Galois group of a totally
real field `F`, the Hecke algebra `T_F` of Hilbert modular forms over `F`
with its `ℤ_ℓ`-module-finiteness, and the modularity lifting theorem
`R_F = T_F` over `F`.

## Why it exists, and why HERE

`Deformation.lean`'s
`exists_finiteIndex_isIntegral_charpolyCoeff_quotient_minimalPrime_of_isWeaklyUniversal_isTraceGenerated`
is the single genuinely deep arithmetic node of the hardly ramified
lifting core: at a prime `q` of the universal deformation ring `D.R`
minimal over `(ℓ)` it asks for a FINITE-INDEX subgroup `H ≤ G_ℚ` on which
the traces of the universal deformation are already integral over `ℤ_ℓ`.
Three successive audits of that leaf (recorded in its docstring, and NOT
repeated here) established:

* the leaf admits no weaker form in the vocabulary of that module;
* the route through `Modularity/Patching.lean` is **circular** — its
  `R = T` needs a modular `T` attached to `ρbar` over `ℚ`, which for a
  general irreducible hardly ramified `ρbar` at `ℓ ≥ 5` IS Serre's
  conjecture, i.e. the very statement pillar α proves;
* the ONLY non-circular route is **potential modularity**: Taylor's
  Moret–Bailly argument supplies a totally real `F` over which
  `ρbar|_{G_F}` is modular — never over `ℚ` — and then modularity lifting
  over totally real fields gives `R_F = T_F`, with `T_F` a Hecke algebra
  of Hilbert modular forms of fixed weight and level, hence a FINITE
  `ℤ_ℓ`-algebra. `H = G_F`, and `[F : ℚ] < ∞` is exactly
  `H.FiniteIndex`.

That audit also listed five missing items and observed that only the
interface of item 5 (potential modularity) exists anywhere, inside
`Modularity/KhareWintenberger.lean` — which imports `Deformation.lean`,
so nothing there is reachable from the leaf. This module is the KW-free
upstream module that route (ii) needs. It imports only
`HardlyRamified/Defs.lean`, `Deformations/RepresentationTheory/`
(which is UPSTREAM of `Defs.lean` — `Defs.lean` already imports
`GaloisRep.lean` from there) and mathlib, so `Deformation.lean` may
`public import` it without touching the circularity guard.

CIRCULARITY GUARD (inherited, load-bearing): nothing from `Family.lean`,
`Lift.lean`, `Modularity/*` or `Deformation.lean` may ever be imported
here. In particular the odd-prime dichotomy
`not_isIrreducible_of_isHardlyRamified_of_five_le` — itself proven over
pillar α — must never be used to discharge the leaves below vacuously.

## Architecture (top-down; the consumer is written first)

The consumer of everything below is
`exists_finiteIndex_isIntegral_charpolyCoeff_of_isHardlyRamified`, the
LAST declaration of this module: for a hardly ramified deformation `ρ` of
an irreducible hardly ramified `ρbar` at `ℓ ≥ 5`, the traces of `ρ` are
integral over `ℤ_ℓ` on a finite-index subgroup of `G_ℚ`. It is PROVEN
over the six items below and is what `Deformation.lean` consumes.

The chain, in the order the assembly uses it:

1. `galoisSubgroup F` — `G_F ≤ G_ℚ` as the range of the functorial map
   `Γ F → Γ ℚ`; `finiteIndex_galoisSubgroup` is item 1 of the audit's
   missing-machinery list (PROVEN 2026-07-26, over the general
   `finiteIndex_range_absoluteGaloisGroupMap`: the chosen embedding
   `Kᵃˡᵍ → Fᵃˡᵍ` is an isomorphism, so `G_F` lands on a subgroup
   containing the fixing subgroup of a finite intermediate field, which
   is open in the Krull topology of the COMPACT group `Γ K`).
2. `IsHilbertHardlyRamified` — the `F`-level local deformation condition,
   and `isHilbertHardlyRamified_map_of_isHardlyRamified`: the restriction
   of a hardly ramified representation satisfies it. PROVEN (2026-07-26)
   over ONE remaining local leaf,
   `map_mem_inertia_Z2bar_of_mem_localInertiaGroup` — the agreement of the
   `IntegralClosure 𝒪_v` and `Z2bar` spellings of local inertia at `2`.
   Its determinant and unramifiedness clauses are PROVEN glue; BOTH of the
   two sharper local halves it was cut over are now closed (2026-07-26):

   * the tame-at-`2` half `exists_padicTwoEmbedding_of_mem` is PROVEN over
     that single remaining leaf; and
   * the flatness half `isFlatAt_map_of_isFlatAt_under` is PROVEN through
     the base-change core
     `hasFlatProlongationAt_map_of_hasFlatProlongationAt_under`, over the
     general-field-extension points comparison `extPointsEquiv` of the
     `FlatBaseChange` section.
3. `HilbertDeformationDatum` / `IsWeaklyUniversal` — Mazur's category and
   its universal object over `F`, i.e. `R_F`;
   `exists_isWeaklyUniversal_hilbertDeformationDatum` is item 2. It was
   REFUTED and REPAIRED on 2026-07-26 (it needs the category to be
   NONEMPTY; see the faithfulness section on it and the proven refutation
   `rank_eq_two_of_hilbertDeformationDatum`), and is now PROVEN as an
   assembly over the arithmetic-free Schlessinger machine
   `exists_isWeaklyUniversal_hilbertDeformationDatum_of_clauses` together
   with the four deformation-condition clauses
   `isHilbertBaseChangeClause`, `isHilbertFibreProductClause`,
   `isHilbertFiniteFramesClause`, `isHilbertProLimitClause` and the
   Brauer–Nesbitt clause `isHilbertResidualRigidityClause` (PROVEN
   2026-07-26 over `BrauerNesbittConjugacy.lean`'s abstract dimension-`2`
   core `exists_linearEquiv_of_charpoly_eq`, under the added `[Finite k]`
   that core is proven with).

   `isHilbertFibreProductClause` is itself PROVEN (2026-07-26) over the two
   arithmetic residues `isHilbertFlatAt_of_fibreProduct` and
   `isHilbertTameAtTwo_of_fibreProduct`, and that repair added
   `hℓ5 : 5 ≤ ℓ` to it and to
   `exists_isWeaklyUniversal_hilbertDeformationDatum`: the tame-at-`2`
   residue is FALSE at `ℓ = 3`, by the `ℚ`-level counterexample recorded in
   `Deformation.lean`, which applies here verbatim at `F = ℚ`.

   The FIRST of those clauses is PROVEN (2026-07-26), over the single
   leaf `hasFlatProlongationAt_of_pi_surjection_of_numberField` — Raynaud
   closure over a VARIABLE number field — via the proven transfers
   `isHilbertTameAtTwo_baseChange`, `isFlatAt_baseChange_of_numberField`,
   `isHilbertHardlyRamified_conj` and
   `isHilbertHardlyRamified_baseChange`.

   `isHilbertFiniteFramesClause` (Schlessinger's H3) is no longer a leaf
   either: it was DECOMPOSED 2026-07-26 along the Hermite–Minkowski cut
   and is now PROVEN over the two bookkeeping lemmas
   `finite_setOf_framedGaloisRep_isUnramifiedAt` and
   `finite_setOf_subgroup_hilbertInertiaAt_le`, above the single
   ARITHMETIC leaf `finite_setOf_intermediateField_hilbertInertiaAt_le`
   (Hermite's theorem for `F`).

   `isHilbertProLimitClause` is PROVEN too (2026-07-26), over the single
   residual leaf `isHilbertTameAtTwo_of_forall_isOpen_quotient`: its
   determinant and unramifiedness clauses are `𝔪`-adic separation, its
   flatness clause is a re-indexing of the level data, and only the tame
   quotient at the places over `2` is a genuine limit statement.

   The machine itself was in turn PROVEN (2026-07-26) as the ASSEMBLY of a
   three-way cut mirroring `Deformation.lean`'s: the profinite
   CONSTRUCTION `exists_universalFrame_profinite_hilbert_of_clauses`
   (LEAF), the upstream FINITENESS criterion
   `ProfiniteLocalNoetherian.isNoetherianRing_isAdic_of_profinite_of_finite_ringHom`
   (PROVEN, Mazur's `Φ_ℓ`), and the LIMIT passage
   `HilbertDeformationDatum.isWeaklyUniversal_of_finiteFrames` (LEAF).
   That proof also carried a SECOND FAITHFULNESS REPAIR: the residual
   field `k` of both nodes now carries `[Finite k]`,
   `[DiscreteTopology k]` and `[Algebra ℤ_[ℓ] k]`, which the `ℚ`-level
   twin assumes throughout and which the consumer of this module already
   supplies. See the repair paragraph on the machine node.

4. `HilbertHeckeAlgebra` — `T_F`, carrying finiteness AND FREENESS of
   `T_F` over `ℤ_[ℓ]`, generation by Hecke operators, and the
   **Hecke-valued Galois representation** `ρT : G_F → GL₂(T_F)` reducing
   to `ρbar|_{G_F}` (the residual eigensystem is now the PROVEN lemma
   `HilbertHeckeAlgebra.residualT`, not a field). `PotentialHeckeDatum`
   bundles it with the totally real `F` that Moret–Bailly produces, and
   `nonempty_potentialHeckeDatum_of_five_le` is items 3 + 5 (LEAF).
   The last three of those components were added on 2026-07-26 after the
   structure was found — and machine-checked — to be inhabited by a
   residual junk witness, i.e. to record no modularity at all; see the
   VACUITY AUDIT in its docstring and in the leaf's. A SECOND repair the
   same day put the `ℓ`-power Teichmüller roots into `adjoin_heckeT` and
   added `πT_surjective`, so that `T_F` is the Hecke algebra over `W(k)`
   rather than over `ℤ_[ℓ]` and its residue field is `k`; without it the
   `R_F = T_F` leaf was FALSE. See the FAITHFULNESS AUDIT in its docstring.
5. `exists_heckeAlgebra_algEquiv_of_isWeaklyUniversal` — **`R_F = T_F`**,
   item 4. DECOMPOSED 2026-07-26 and now PROVEN over
   `exists_heckeDatum_isWeaklyUniversal_isTraceGenerated` ("the `F`-level
   universal ring IS a Hilbert Hecke algebra") plus the formal Carayol
   rigidity
   `HilbertDeformationDatum.isUniversal_of_isWeaklyUniversal_isTraceGenerated`
   and `HilbertDeformationDatum.exists_ringEquiv_of_isUniversal`, both
   PROVEN here. `exists_heckeDatum_isWeaklyUniversal_isTraceGenerated` was
   itself REFUTED, REPAIRED and DECOMPOSED on 2026-07-26 (second pass) into
   THREE leaves, following `Modularity/Patching.lean`'s `ℚ`-level cut:
   `exists_hilbertHeckeDatum_of_hilbertHeckeAlgebra` (the Hecke algebra of
   the matching level as an object of the deformation category — level
   lowering over totally real fields),
   `surjective_classifyingMap_hilbertHeckeDatum` (Carayol generation —
   PROVEN 2026-07-26 after a fifth faithfulness repair: the isomorphism `e`
   carried no link to `T.ρT`, so `exists_hilbertHeckeDatum_of_hilbertHeckeAlgebra`
   now produces it with a charpoly compatibility) and
   `injective_classifyingMap_hilbertHeckeDatum` (Taylor–Wiles patching).
   The refutation is recorded in the FAITHFULNESS AUDIT of
   `HilbertHeckeAlgebra` and in the leaf's own docstring: as stated it
   asserted an isomorphism between a ring with residue field `k` and one
   whose residue field the old `adjoin_heckeT` forced to be the trace field
   of `ρbar|_{G_F}`, so it was false whenever `k` properly contains that
   field. The repair is in `HilbertHeckeAlgebra` — Teichmüller roots into
   `adjoin_heckeT`, `πT_surjective` added — plus a Schlessinger-style
   nonemptiness hypothesis `𝒟₀` on the leaf, which its consumer discharges
   for free.
6. `exists_isWeaklyUniversal_isTraceGenerated_hilbertDeformationDatum` —
   Carayol trace descent at the `F` level. It exists because a
   FAITHFULNESS AUDIT (in the `R_F = T_F` section below) found
   `R_F = T_F` and its finiteness corollary FALSE as originally stated:
   `IsWeaklyUniversal` is an existence-only mapping property, which
   `𝒟₀.R⟦X⟧` satisfies without being module-finite over `ℤ_ℓ`. Trace
   generation is the missing hypothesis, and this node is what supplies
   it to the assembly. `Deformation.lean` had already made exactly this
   repair at the `ℚ` level, on the same day; this module was written
   without it.
   DECOMPOSED 2026-07-26 along the `ℚ`-level architecture and now PROVEN
   as composition glue over `exists_hilbertTraceDescent` (itself PROVEN)
   and the two arithmetic leaves of the Carayol package,
   `exists_isLocalRing_hilbertTraceSubring` (Lemme 1 — the trace subring
   is again a coefficient ring; the content is NOETHERIANITY) and
   `exists_framedGaloisRep_hilbertTraceSubring` (Théorème 1 — the
   conjugation of `𝒟.ρ` into `GL₂(R')`). The `ℚ` level's THIRD leaf, the
   Chebotarev density step, has no `F`-level counterpart: this module's
   `IsTraceGenerated` is stated at every `g : Γ F`, so the generating set
   already contains every trace. Two hypotheses were added to the node in
   the same step, `[Finite k]` and `hlk : (ℓ : k) = 0` — without them the
   descent is FALSE, because the residue field of the trace subring is
   then a proper subfield of `k`; both are discharged for free at the
   consumer. See the faithfulness note on the subsection.

Everything else here is PROVEN glue.

## What this development does NOT do (deliberately)

It does not restate the leaf. The assembly's conclusion — integrality of
the traces on `H` in `R` itself — is strictly STRONGER than the leaf's
mod-`q` form, and the leaf's docstring explicitly forbids *restating* the
leaf that way, because the weak form leaves a future prover free to find
a cheaper route. Proving the leaf from a stronger, separately stated
development is a different thing: the leaf's statement is untouched, and
the strength enters only where the literature genuinely produces it (the
image of `T_F` in `D.R` is a module-finite `ℤ_ℓ`-subalgebra, and that is
what `R_F = T_F` says). The leaf's own audit already records that, given
its PROVEN siblings, the mod-`q` form and the integral form coincide
anyway.

## References

Wiles, *Modular elliptic curves and Fermat's Last Theorem*, Ann. of Math.
141 (1995), §2 (the `R = T` machine); Taylor–Wiles, *Ring-theoretic
properties of certain Hecke algebras*, ibid.; Taylor, *Remarks on a
conjecture of Fontaine and Mazur*, J. Inst. Math. Jussieu 1 (2002) and
*On the meromorphic continuation of degree two L-functions*, Doc. Math.
Extra Vol. (2006) (potential modularity); Kisin, *Moduli of finite flat
group schemes, and modularity*, Ann. of Math. 170 (2009);
Barnet-Lamb–Gee–Geraghty–Taylor, *Potential automorphy and change of
weight*, §§1–2 (the `F`-level deformation ring); Diamond–Shurman, *A
First Course in Modular Forms*, ch. 5–8 (Hecke algebras);
Khare–Wintenberger, *Serre's modularity conjecture (I)*, Invent. Math.
178 (2009), §4.
-/
module

public import Fermat.FLT.GaloisRepresentation.HardlyRamified.Defs
public import Fermat.FLT.GaloisRepresentation.HardlyRamified.ProfiniteLocalNoetherian
public import Fermat.FLT.Deformations.RepresentationTheory.GaloisRepTransport
public import Mathlib.Topology.Algebra.Ring.Ideal
public import Mathlib.Topology.Compactness.Compact
-- the convolution-monoid bookkeeping of the flat-prolongation package
-- (`liftEquiv_convOne`/`liftEquiv_convMul`/`liftEquiv_comp`,
-- `vendored_one_eq_convOne`, `vendored_mul_eq_convMul`), reused by the
-- base-change points comparison `extPointsEquiv` below
public import Fermat.FLT.Deformations.RepresentationTheory.FlatProlongation
public import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.GroupTheory.Index
public import Mathlib.LinearAlgebra.Charpoly.Basic
-- `LinearMap.det_baseChange`, consumed by `det_framePushforward` below and by
-- the determinant clause of `isHilbertHardlyRamified_baseChange`
public import Mathlib.LinearAlgebra.Charpoly.BaseChange
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.RingTheory.Adjoin.Basic
public import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.Finiteness.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Pi
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.Topology.Algebra.Algebra
public import Mathlib.NumberTheory.Padics.HeightOneSpectrum
-- `Submodule.isCompact_of_fg`, `Submodule.eq_bot_of_le_smul_of_le_jacobson_bot`
-- and `PadicInt.compactSpace`: the closed-image half of
-- `surjective_classifyingMap_hilbertHeckeDatum` below
public import Mathlib.Topology.Algebra.Module.Compact
public import Mathlib.RingTheory.Nakayama
public import Mathlib.NumberTheory.Padics.ProperSpace
-- proof-only: the abstract dimension-`2` Brauer–Nesbitt core
-- `exists_linearEquiv_of_charpoly_eq`, which discharges
-- `isHilbertResidualRigidityClause` below. `BrauerNesbittConjugacy.lean` sits
-- in `GaloisRepresentation/` and imports only `GaloisRep.lean`, `BrauerNesbitt.lean`,
-- `Chebotarev.lean` and mathlib, so it is OUTSIDE the circularity guard
-- (nothing from `Family.lean`, `Lift.lean`, `Modularity/*` or `Deformation.lean`);
-- `Deformation.lean`, the consumer of this module, already imports it too.
import Fermat.FLT.GaloisRepresentation.BrauerNesbittConjugacy
-- `HenselianLocalRing`, for the Teichmüller-root existence lemma
-- `exists_mem_teichmullerRootSet_map_eq` in the Carayol trace-descent section.
import Mathlib.RingTheory.Henselian

@[expose] public section

open IsDedekindDomain Polynomial
open scoped NumberField

namespace GaloisRepresentation

local notation3 "Γ" K:max => Field.absoluteGaloisGroup K
local notation3 K:max "ᵃˡᵍ" => AlgebraicClosure K

universe u v

/-! Binders are written out on every declaration rather than collected in a
`variable` block: Lean's automatic variable inclusion looks at a structure's
PARAMETERS and not at its FIELDS, so a section variable used only inside a
field (here `ℓ`, which occurs in `Algebra ℤ_[ℓ] R`) is silently left
unbound and the field's instance search gets stuck on a metavariable. -/

/-- `Fin 2 → O` has rank `2`. (A local copy of `Deformation.lean`'s
`rank_finTwoFun`, which lives DOWNSTREAM of this module; the two are the
same one-line `simp`, and neither may be replaced by the other without
moving a declaration across the import edge.) -/
lemma rank_finTwoPi (O : Type*) [CommRing O] [Nontrivial O] :
    Module.rank O (Fin 2 → O) = 2 := by
  simp

/-! ### Item 1 — the Galois group of a number field as a subgroup of `G_ℚ` -/

/-- **`G_F` as a subgroup of `G_ℚ`**: the range of the functorial map
`Γ F → Γ ℚ` induced by `ℚ ↪ F` (`Field.absoluteGaloisGroup.map`, which
fixes an embedding `ℚᵃˡᵍ → Fᵃˡᵍ` and restricts along it).

Classically this map is INJECTIVE with image the fixing subgroup of `F`
inside `G_ℚ`, of index `[F : ℚ]`; only the index statement is needed
downstream, and it is `finiteIndex_galoisSubgroup` below.

This is the concrete `H` that the potential-modularity leaf of
`Deformation.lean` states abstractly as `H : Subgroup (Γ ℚ)`. -/
noncomputable def galoisSubgroup (F : Type u) [Field F] [NumberField F] :
    Subgroup (Γ ℚ) :=
  (Field.absoluteGaloisGroup.map (algebraMap ℚ F)).toMonoidHom.range

/-- Membership in `galoisSubgroup F` is exactly being the restriction of
an element of `Γ F` (PROVEN — `MonoidHom.mem_range` unfolded). It is the
step that turns a statement about `G_F` into a statement about `G_ℚ` in
the assembly below. -/
lemma exists_map_eq_of_mem_galoisSubgroup (F : Type u) [Field F] [NumberField F]
    {g : Γ ℚ} (hg : g ∈ galoisSubgroup F) :
    ∃ σ : Γ F, Field.absoluteGaloisGroup.map (algebraMap ℚ F) σ = g := by
  obtain ⟨σ, hσ⟩ := MonoidHom.mem_range.mp hg
  exact ⟨σ, hσ⟩

/-- **The range of `Γ F → Γ K` has finite index, for `F/K` finite**
(PROVEN; item 1 of the audit's missing-machinery list, in the general
form the ℚ-level statement below is an instance of).

The argument, in four steps, is the classical one and uses no counting:

1. The chosen embedding `ι := AlgebraicClosure.map (algebraMap K F)` of
   `Kᵃˡᵍ` into `Fᵃˡᵍ` is BIJECTIVE. It is injective as a map of fields;
   it is surjective because `Fᵃˡᵍ` is algebraic over `K`, hence integral
   over the image of the algebraically closed `Kᵃˡᵍ`, and an
   algebraically closed field admits no proper integral extension
   (`IsAlgClosed.ringHom_bijective_of_isIntegral`).
2. Transporting `F` back along `ι⁻¹` gives a `K`-algebra embedding
   `g : F →ₐ[K] Kᵃˡᵍ`, whose `fieldRange` is an intermediate field
   `E` of `Kᵃˡᵍ/K` with `E ≃ₐ[K] F`, hence `FiniteDimensional K E`.
3. `E.fixingSubgroup ≤ range`: an element `τ` of `Γ K` fixing `E`
   pointwise is transported by `ι` to a ring automorphism `ι τ ι⁻¹` of
   `Fᵃˡᵍ` which fixes `F` pointwise — i.e. an element of `Γ F` — and
   `Field.absoluteGaloisGroup.lift_map` plus injectivity of `ι` identify
   its image in `Γ K` with `τ`.
4. `E.fixingSubgroup` is OPEN in the Krull topology because `E/K` is
   finite (`IntermediateField.fixingSubgroup_isOpen`), and `Γ K` is
   COMPACT, so the quotient is discrete and compact, hence finite; a
   subgroup containing a finite-index subgroup has finite index.

Only the inclusion of step 3 is proven, not the reverse one: the
reverse inclusion (the range really IS `E.fixingSubgroup`, so the index
is exactly `[F : K]`) is true but is not needed by any consumer, and
`Subgroup.finiteIndex_of_le` goes the way that needs only one half.

Stated over a VARIABLE base field `K` and instantiated at `ℚ` below,
deliberately: at the literal `ℚ`, `Algebra ℚ (AlgebraicClosure F)` is
found as `DivisionRing.toRatAlgebra` rather than through the tower
`ℚ → F → Fᵃˡᵍ`, and `AlgebraicClosure.map_algebraMap` then fails to
rewrite against a goal that pretty-prints as exactly its pattern. -/
theorem finiteIndex_range_absoluteGaloisGroupMap (K : Type*) [Field K]
    (F : Type*) [Field F] [Algebra K F] [FiniteDimensional K F]
    [CompactSpace (Γ K)] :
    ((Field.absoluteGaloisGroup.map (algebraMap K F)).toMonoidHom.range).FiniteIndex := by
  classical
  -- STEP 1: the chosen embedding `Kᵃˡᵍ → Fᵃˡᵍ` is bijective.
  have key : ∀ j : AlgebraicClosure K →+* AlgebraicClosure F,
      (∀ y : K, j (algebraMap K (AlgebraicClosure K) y)
        = algebraMap K (AlgebraicClosure F) y) → Function.Bijective j := by
    intro j hj
    refine IsAlgClosed.ringHom_bijective_of_isIntegral j fun x => ?_
    refine ⟨(minpoly K x).map (algebraMap K (AlgebraicClosure K)),
      (minpoly.monic (Algebra.IsIntegral.isIntegral x)).map _, ?_⟩
    have hcomp : j.comp (algebraMap K (AlgebraicClosure K))
        = algebraMap K (AlgebraicClosure F) := RingHom.ext hj
    rw [Polynomial.eval₂_map, hcomp, ← Polynomial.aeval_def, minpoly.aeval]
  have hcommutes : ∀ y : K, AlgebraicClosure.map (algebraMap K F)
      (algebraMap K (AlgebraicClosure K) y) = algebraMap K (AlgebraicClosure F) y := fun y => by
    rw [AlgebraicClosure.map_algebraMap, ← IsScalarTower.algebraMap_apply]
  have hbij : Function.Bijective (AlgebraicClosure.map (algebraMap K F)) := key _ hcommutes
  let e : AlgebraicClosure K ≃+* AlgebraicClosure F := RingEquiv.ofBijective _ hbij
  have he : ∀ x, e x = AlgebraicClosure.map (algebraMap K F) x := fun _ => rfl
  -- STEP 2: `E ≤ Kᵃˡᵍ`, the copy of `F` inside `Kᵃˡᵍ` along `e⁻¹`.
  let g : F →ₐ[K] AlgebraicClosure K :=
    { (e.symm : AlgebraicClosure F ≃+* AlgebraicClosure K).toRingHom.comp
        (algebraMap F (AlgebraicClosure F)) with
      commutes' := fun y => by
        show e.symm (algebraMap F (AlgebraicClosure F) (algebraMap K F y)) = _
        rw [← IsScalarTower.algebraMap_apply, ← hcommutes y, ← he]
        exact e.symm_apply_apply _ }
  have hg : ∀ y : F, e (g y) = algebraMap F (AlgebraicClosure F) y := fun y =>
    e.apply_symm_apply _
  let E : IntermediateField K (AlgebraicClosure K) := g.fieldRange
  haveI : FiniteDimensional K E :=
    (show F ≃ₐ[K] E from AlgEquiv.ofInjectiveField g).toLinearEquiv.finiteDimensional
  -- STEP 3: `E.fixingSubgroup ≤ range`.
  have hle : E.fixingSubgroup ≤
      (Field.absoluteGaloisGroup.map (algebraMap K F)).toMonoidHom.range := by
    intro τ hτ
    have hτ' : ∀ x ∈ E, τ x = x := (IntermediateField.mem_fixingSubgroup_iff E τ).mp hτ
    have hfix : ∀ y : F, ((e.symm.trans τ.toRingEquiv).trans e)
        (algebraMap F (AlgebraicClosure F) y) = algebraMap F (AlgebraicClosure F) y := by
      intro y
      have hmem : g y ∈ E := (AlgHom.mem_fieldRange (f := g)).mpr ⟨y, rfl⟩
      have hsy : e.symm (algebraMap F (AlgebraicClosure F) y) = g y := by
        rw [← hg y, e.symm_apply_apply]
      show e (τ (e.symm (algebraMap F (AlgebraicClosure F) y))) = _
      rw [hsy, hτ' (g y) hmem, hg]
    refine ⟨AlgEquiv.ofRingEquiv (f := (e.symm.trans τ.toRingEquiv).trans e) hfix, ?_⟩
    refine AlgEquiv.ext fun x => hbij.injective ?_
    refine (Field.absoluteGaloisGroup.lift_map (algebraMap K F)
      (AlgEquiv.ofRingEquiv (f := (e.symm.trans τ.toRingEquiv).trans e) hfix) x).trans ?_
    show e (τ (e.symm (e x))) = e (τ x)
    rw [e.symm_apply_apply]
  -- STEP 4: an open subgroup of the compact group `Γ K` has finite index.
  haveI : Finite ((Γ K) ⧸ E.fixingSubgroup) :=
    Subgroup.quotient_finite_of_isOpen _ (IntermediateField.fixingSubgroup_isOpen E)
  haveI : (E.fixingSubgroup : Subgroup (Γ K)).FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  exact Subgroup.finiteIndex_of_le hle

/-- **`[G_ℚ : G_F] < ∞`** (PROVEN — item 1 of the audit's
missing-machinery list; the `ℚ`-level instance of
`finiteIndex_range_absoluteGaloisGroupMap`, whose docstring carries the
argument).

Formalization note: `Subgroup.FiniteIndex` only asks that the index be
nonzero, so the sharp value `[F : ℚ]` is deliberately NOT part of the
statement — no consumer here needs it, and proving it would additionally
need the reverse inclusion of step 3 there. -/
theorem finiteIndex_galoisSubgroup (F : Type u) [Field F] [NumberField F] :
    (galoisSubgroup F).FiniteIndex :=
  finiteIndex_range_absoluteGaloisGroupMap ℚ F

/-! ### Item 2a — the `F`-level local deformation condition -/

/-- **The hardly ramified condition over a totally real field `F`**: the
local conditions cut out of the `F`-level deformation problem, in the same
FOUR clauses as `IsHardlyRamified` over `ℚ` — cyclotomic determinant,
unramified away from the places over `2` and `ℓ`, flat at the places over
`ℓ`, and tame with a square-trivial unramified quotient character at the
places over `2`.

Two deliberate shape differences from the `ℚ`-level `IsHardlyRamified`:

* **The determinant clause is written through the RESTRICTION of the
  `ℚ`-adic cyclotomic character**, not through `cyclotomicCharacter Fᵃˡᵍ`.
  The two agree — the cyclotomic character of `F` is the restriction of
  that of `ℚ`, both being the action on `ℓ`-power roots of unity, which
  already live in `ℚᵃˡᵍ` — and writing it this way keeps the determinant
  clause of `isHilbertHardlyRamified_map_of_isHardlyRamified` PROVEN glue
  instead of a sixth leaf about compatibility of cyclotomic characters
  under base change.
* **The tame-at-`2` clause is stated PER PLACE over `2`, through
  `ρ.toLocal w` and `localInertiaGroup w`**, where the `ℚ`-level version
  hard-codes the single place `ℚ_[2]` and its bespoke inertia subgroup of
  `Z2bar`. That is forced: `F` has several places over `2`.

**WHY THE TAME-AT-`2` CLAUSE MAY NOT BE DROPPED** (this was got wrong once
while drafting this module, and the mistake is instructive). Omitting it
makes the condition weaker and the category larger, which makes
`IsWeaklyUniversal` a *stronger* hypothesis — that direction is safe. But
it also makes `R_F` the deformation ring of representations with
UNRESTRICTED ramification at the places over `2`, i.e. of unbounded level,
and such a ring is not module-finite over `ℤ_ℓ` and is not a Hecke algebra
of any fixed level. `R_F = T_F` would then be FALSE, and it is precisely
`Module.Finite ℤ_[ℓ] R_F` that this whole module exists to produce. The
minimality of the condition at `2` is load-bearing, exactly as it is over
`ℚ`, where it is what makes `moduleFinite_of_isUniversal` true. -/
structure IsHilbertHardlyRamified (ℓ : ℕ) [Fact ℓ.Prime]
    (F : Type u) [Field F] [NumberField F]
    {R : Type*} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    [IsLocalRing R] [Algebra ℤ_[ℓ] R]
    {M : Type*} [AddCommGroup M] [Module R M] [Module.Finite R M]
    [Module.Free R M] (hdim : Module.rank R M = 2)
    (ρ : GaloisRep F R M) : Prop where
  /-- The determinant is the restriction to `G_F` of the `ℓ`-adic
  cyclotomic character of `ℚ`. -/
  det : ∀ g : Γ F, ρ.det g = algebraMap ℤ_[ℓ] R
    (cyclotomicCharacter (ℚ ᵃˡᵍ) ℓ
      (Field.absoluteGaloisGroup.map (algebraMap ℚ F) g).toRingEquiv)
  /-- Unramified at every place not above `2` or `ℓ`. -/
  isUnramified : ∀ w : HeightOneSpectrum (𝓞 F),
    ((2 : ℕ) : 𝓞 F) ∉ w.asIdeal → ((ℓ : ℕ) : 𝓞 F) ∉ w.asIdeal →
    ρ.IsUnramifiedAt w
  /-- Flat at every place above `ℓ`. -/
  isFlat : ∀ w : HeightOneSpectrum (𝓞 F), ((ℓ : ℕ) : 𝓞 F) ∈ w.asIdeal →
    ρ.IsFlatAt w
  /-- At every place above `2` there is a `G_{F_w}`-stable rank-one
  quotient on which `ρ` acts by an unramified character of order dividing
  `2` — the minimality that keeps `R_F` of bounded level. -/
  isTameAtTwo : ∀ w : HeightOneSpectrum (𝓞 F), ((2 : ℕ) : 𝓞 F) ∈ w.asIdeal →
    ∃ (p : M →ₗ[R] R) (_ : Function.Surjective p)
      (δ : GaloisRep (w.adicCompletion F) R R),
      (∀ g : Γ (w.adicCompletion F), ∀ v : M, p (ρ.toLocal w g v) = δ g (p v)) ∧
      localInertiaGroup w ≤ δ.ker ∧
      ∀ g : Γ (w.adicCompletion F), δ g * δ g = 1

/-! #### Place bookkeeping over `ℚ`

`IsHardlyRamified` indexes its local conditions by RATIONAL PRIMES, through
`Nat.Prime.toHeightOneSpectrumRingOfIntegersRat`, while
`IsHilbertHardlyRamified` indexes them by places `w` of `F`. The three
lemmas below are the dictionary: every place of `ℚ` is the place of a prime
number, and `w` lies over the prime `p` exactly when `p ∈ w`. -/

set_option backward.isDefEq.respectTransparency false in
/-- **Every finite place of `ℚ` is the place of a prime number** (PROVEN):
the corresponding height-one prime of the PID `ℤ` is generated by a prime
integer, and `Rat.ringOfIntegersEquiv` transports that back to `𝓞 ℚ`.

(`Chebotarev.lean` carries the same statement as
`exists_prime_toHeightOneSpectrum`; it is re-proven here, in ten lines,
rather than imported, because that module is 13k lines and lies OUTSIDE
this module's deliberately minimal import surface.) -/
lemma exists_prime_eq_ratPlace (v : HeightOneSpectrum (𝓞 ℚ)) :
    ∃ (q : ℕ) (hq : q.Prime), v = hq.toHeightOneSpectrumRingOfIntegersRat := by
  set e : HeightOneSpectrum ℤ ≃ HeightOneSpectrum (𝓞 ℚ) :=
    Rat.ringOfIntegersEquiv.symm.heightOneSpectrum
  obtain ⟨w, rfl⟩ := e.surjective v
  set a : ℤ := Submodule.IsPrincipal.generator w.asIdeal
  have ha : Ideal.span {a} = w.asIdeal := Ideal.span_singleton_generator _
  have ha0 : a ≠ 0 := by
    intro h
    apply w.ne_bot
    rw [← ha, h]
    exact Ideal.span_singleton_eq_bot.mpr rfl
  have hsp : (Ideal.span {a} : Ideal ℤ).IsPrime := ha ▸ w.isPrime
  have haprime : Prime a := (Ideal.span_singleton_prime ha0).mp hsp
  refine ⟨a.natAbs, Int.prime_iff_natAbs_prime.mp haprime, ?_⟩
  show e w = e (Nat.Prime.toHeightOneSpectrumInt
    (Int.prime_iff_natAbs_prime.mp haprime))
  refine congrArg e ?_
  apply HeightOneSpectrum.ext
  show w.asIdeal = Ideal.span {((a.natAbs : ℕ) : ℤ)}
  rw [← ha, Ideal.span_singleton_eq_span_singleton]
  exact Int.associated_natAbs a

/-- **A place lying over `q` contains `q`** (PROVEN): `(w.under (𝓞 ℚ)).asIdeal`
is by definition the contraction of `w.asIdeal`, and the place of `q` is the
ideal `(q)` (`asIdeal_toHeightOneSpectrumRingOfIntegersRat`). -/
lemma natCast_mem_asIdeal_of_under_eq {F : Type u} [Field F] [NumberField F]
    (w : HeightOneSpectrum (𝓞 F)) {q : ℕ} (hq : q.Prime)
    (hqv : w.under (𝓞 ℚ) = hq.toHeightOneSpectrumRingOfIntegersRat) :
    ((q : ℕ) : 𝓞 F) ∈ w.asIdeal := by
  have h1 : ((q : ℕ) : 𝓞 ℚ) ∈ (w.under (𝓞 ℚ)).asIdeal := by
    rw [hqv, asIdeal_toHeightOneSpectrumRingOfIntegersRat]
    exact Ideal.mem_span_singleton_self _
  have h2 : algebraMap (𝓞 ℚ) (𝓞 F) ((q : ℕ) : 𝓞 ℚ) ∈ w.asIdeal := h1
  rwa [map_natCast] at h2

/-- **A place containing `p` lies over `p`** (PROVEN, the converse):
`w.under (𝓞 ℚ)` is the place of SOME prime `q`, and `p ∈ w` forces
`q ∣ p` in `ℤ`, hence `q = p` since both are prime. -/
lemma under_eq_of_natCast_mem {F : Type u} [Field F] [NumberField F]
    (w : HeightOneSpectrum (𝓞 F)) {p : ℕ} (hp : p.Prime)
    (hmem : ((p : ℕ) : 𝓞 F) ∈ w.asIdeal) :
    w.under (𝓞 ℚ) = hp.toHeightOneSpectrumRingOfIntegersRat := by
  obtain ⟨q, hq, hqv⟩ := exists_prime_eq_ratPlace (w.under (𝓞 ℚ))
  have h1 : ((p : ℕ) : 𝓞 ℚ) ∈ (w.under (𝓞 ℚ)).asIdeal := by
    show algebraMap (𝓞 ℚ) (𝓞 F) ((p : ℕ) : 𝓞 ℚ) ∈ w.asIdeal
    rwa [map_natCast]
  rw [hqv, Nat.Prime.mem_toHeightOneSpectrumRingOfIntegersRat_asIdeal,
    map_natCast] at h1
  have hqp : q = p := (Nat.prime_dvd_prime_iff_eq hq hp).mp (Int.ofNat_dvd.mp h1)
  subst hqp
  exact hqv

/-! #### The unramifiedness clause -/

/-- **Unramifiedness descends to every place over an unramified place**
(PROVEN): if `ρ` is unramified at the place `w.under (𝓞 K)` of `K` below
`w`, then its restriction to `G_L` is unramified at `w`.

This is the SHARP, place-by-place form of
`GaloisRep.exists_finset_isUnramifiedAt_map`
(`GaloisRepTransport.lean`), which only produces a cofinite conclusion
(`∃ T : Finset …, ∀ w ∉ T, …`) and therefore cannot discharge the
`∀ w` of `IsHilbertHardlyRamified.isUnramified`. The proof is the same:
the finite set there is exactly the set of places over the excluded set,
so nothing but packaging is lost by removing it.

THE ARGUMENT (all four ingredients are PROVEN in `CompletionTransport.lean`
and `GaloisRepTransport.lean`):

* `v := w.under (𝓞 K)` is by definition the contraction of `w`, so
  `HeightOneSpectrum.valuation_map_le_of_le_one` gives `w(x) ≤ v(x)` on the
  valuation ring of `v`, hence `K → L` extends to a continuous
  `φ : K_v →+* L_w` (`HeightOneSpectrum.adicCompletionMap`);
* `φ` is LOCAL (`adicCompletionMap_mem_integers`), so
  `Field.absoluteGaloisGroup.map_mem_localInertiaGroup` carries
  `localInertiaGroup w` into `localInertiaGroup v`;
* `Field.absoluteGaloisGroup.exists_conj_map_comp'` — twice, once for each
  of the two factorisations of `K → L_w` — supplies the two
  argument-independent conjugators whose ratio `μ` relates the two routes;
* the kernel of `ρ` is a subgroup, so the conjugation by `μ` is invisible
  to it. -/
theorem isUnramifiedAt_map_of_isUnramifiedAt_under
    {K : Type*} [Field K] [NumberField K] {L : Type*} [Field L] [NumberField L]
    [Algebra K L]
    {A : Type*} [CommRing A] [TopologicalSpace A]
    {M : Type*} [AddCommGroup M] [Module A M]
    (ρ : GaloisRep K A M) (w : HeightOneSpectrum (𝓞 L))
    (hv : ρ.IsUnramifiedAt (w.under (𝓞 K))) :
    (ρ.map (algebraMap K L)).IsUnramifiedAt w := by
  classical
  set v : HeightOneSpectrum (𝓞 K) := w.under (𝓞 K)
  have hcomm : ∀ a : 𝓞 K,
      (algebraMap K L) (algebraMap (𝓞 K) K a)
        = algebraMap (𝓞 L) L (algebraMap (𝓞 K) (𝓞 L) a) := by
    intro a
    rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
  have hmem : v.asIdeal ≤ Ideal.comap (algebraMap (𝓞 K) (𝓞 L)) w.asIdeal := le_rfl
  have hcompl : ∀ s : 𝓞 K, s ∉ v.asIdeal →
      algebraMap (𝓞 K) (𝓞 L) s ∉ w.asIdeal := fun _ hs => hs
  have hψ : UniformContinuous
      (WithVal.map (v.valuation K) (w.valuation L) (algebraMap K L)) :=
    WithVal.uniformContinuous_map_of_le _ _
      (HeightOneSpectrum.valuation_surjective K v) _
      (fun x hx => HeightOneSpectrum.valuation_map_le_of_le_one v w _ _
        hcomm hmem hcompl x hx)
  have hint : ∀ x ∈ v.adicCompletionIntegers K,
      HeightOneSpectrum.adicCompletionMap v w (algebraMap K L) hψ x
        ∈ w.adicCompletionIntegers L :=
    fun x hx => HeightOneSpectrum.adicCompletionMap_mem_integers v w _ hψ _ hcomm hx
  obtain ⟨τ, hτ⟩ := Field.absoluteGaloisGroup.exists_conj_map_comp'
    (algebraMap K (v.adicCompletion K))
    (HeightOneSpectrum.adicCompletionMap v w (algebraMap K L) hψ)
    ((algebraMap L (w.adicCompletion L)).comp (algebraMap K L))
    (RingHom.ext fun x =>
      HeightOneSpectrum.adicCompletionMap_coe v w (algebraMap K L) hψ x)
  obtain ⟨τ₀, hτ₀⟩ := Field.absoluteGaloisGroup.exists_conj_map_comp' (algebraMap K L)
    (algebraMap L (w.adicCompletion L))
    ((algebraMap L (w.adicCompletion L)).comp (algebraMap K L)) rfl
  refine ⟨fun ι hι => ?_⟩
  obtain ⟨κ, hκdef⟩ : ∃ κ : Γ (v.adicCompletion K), Field.absoluteGaloisGroup.map
      (HeightOneSpectrum.adicCompletionMap v w (algebraMap K L) hψ) ι = κ := ⟨_, rfl⟩
  have hκ : κ ∈ localInertiaGroup v := by
    rw [← hκdef]
    exact Field.absoluteGaloisGroup.map_mem_localInertiaGroup v w _ hint ι hι
  have hmain := hτ ι
  rw [hκdef] at hmain
  have hker : ρ (Field.absoluteGaloisGroup.map
      (algebraMap K (v.adicCompletion K)) κ) = 1 := by
    have h1 : ρ.toLocal v κ = 1 := hv.localInertiaGroup_le hκ
    rwa [GaloisRep.toLocal_apply] at h1
  obtain ⟨μ, hμ⟩ : ∃ μ : Γ K, τ₀⁻¹ * τ = μ := ⟨_, rfl⟩
  show (ρ.map (algebraMap K L)).toLocal w ι = 1
  have hX : Field.absoluteGaloisGroup.map (algebraMap K L)
      (Field.absoluteGaloisGroup.map (algebraMap L (w.adicCompletion L)) ι)
      = μ * Field.absoluteGaloisGroup.map
          (algebraMap K (v.adicCompletion K)) κ * μ⁻¹ := by
    have h1 := hτ₀ ι
    rw [hmain] at h1
    rw [← hμ, show τ₀⁻¹ * τ * Field.absoluteGaloisGroup.map
        (algebraMap K (v.adicCompletion K)) κ * (τ₀⁻¹ * τ)⁻¹
      = τ₀⁻¹ * (τ * Field.absoluteGaloisGroup.map
        (algebraMap K (v.adicCompletion K)) κ * τ⁻¹) * τ₀ from by group, h1]
    group
  rw [GaloisRep.toLocal_apply, GaloisRep.map_apply, hX, map_mul, map_mul, hker,
    mul_one, ← map_mul, mul_inv_cancel, map_one]

/-! #### The two remaining local leaves -/

/-! ##### The local embedding at `2`

The route mapped out by this leaf's previous owner is now EXECUTED, and
what remains is exactly the one identification that owner flagged as
"genuinely missing". Four things happen below:

1. `symm_primesEquiv_of_natCast_mem` — the place of `ℚ` containing the
   prime `p` IS `Rat.HeightOneSpectrum.primesEquiv.symm p`;
2. `exists_ringEquiv_padicTwo_adicCompletion` — hence mathlib's
   `Padic.adicCompletionEquiv` (which, being stated for a general Dedekind
   `R`, applies at `R := 𝓞 ℚ` with NO `ℤ ↔ 𝓞 ℚ` bridge) identifies `ℚ_[2]`
   with `v.adicCompletion ℚ` as a topological ring, carrying `ℤ_[2]` into
   `𝒪_v` (`PadicInt.adicCompletionIntegersEquiv`);
3. `conj_mem_inertia_Z2bar` — the `Z2bar` spelling of inertia is NORMAL in
   `Γ ℚ_[2]`, which is what absorbs the conjugation ambiguity of
   `Field.absoluteGaloisGroup.map`;
4. `map_mem_inertia_Z2bar_of_mem_localInertiaGroup` (LEAF) — the two
   spellings of local inertia at `2` agree across that identification.

`exists_padicTwoEmbedding_of_mem` is then PROVEN glue over 4.
-/

/-- **The place of `ℚ` containing a prime `p` is `primesEquiv.symm p`**
(PROVEN). `Rat.HeightOneSpectrum.natGenerator v` is the positive generator
of the ideal of `v` read in `ℤ`; `p ∈ v` makes it divide `p`, and it is
prime, so it IS `p`.

This is the bridge that lets mathlib's `Padic.adicCompletionEquiv` — whose
codomain is indexed by `primesEquiv.symm`, not by "the place containing
`p`" — be used at a place given arithmetically. -/
lemma symm_primesEquiv_of_natCast_mem (p : ℕ) (hp : p.Prime)
    (v : HeightOneSpectrum (𝓞 ℚ)) (hv : ((p : ℕ) : 𝓞 ℚ) ∈ v.asIdeal) :
    (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).symm ⟨p, hp⟩ = v := by
  have hgen : Rat.HeightOneSpectrum.natGenerator v = p := by
    have hdvd : Rat.HeightOneSpectrum.natGenerator v ∣ p := by
      rw [Rat.HeightOneSpectrum.natGenerator_dvd_iff]
      have h1 : Rat.IsIntegralClosure.intEquiv (𝓞 ℚ) ((p : ℕ) : 𝓞 ℚ) ∈
          Ideal.map (Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)) v.asIdeal :=
        Ideal.mem_map_of_mem _ hv
      rwa [map_natCast] at h1
    exact (Nat.prime_dvd_prime_iff_eq
      (Rat.HeightOneSpectrum.prime_natGenerator v) hp).mp hdvd
  rw [Equiv.symm_apply_eq]
  exact Subtype.ext hgen.symm

/-- **`ℚ_[2]` IS the completion of `ℚ` at a place containing `2`** (PROVEN),
as a topological ring, and the identification carries `ℤ_[2]` into `𝒪_v`.

The `letI` pinning `Algebra ℚ (v.adicCompletion ℚ)` is load-bearing: at the
CONCRETE base `ℚ` there are two instances that print identically —
`DivisionRing.toRatAlgebra`, which instance search returns, and
`HeightOneSpectrum.instAlgebraAdicCompletion`, which is baked into
mathlib's statement — and they are not definitionally equal, so without the
`letI` the projections out of `Padic.adicCompletionEquiv` do not even
elaborate.

The `ℚ`-linearity of the resulting `e` is NOT recorded here because it is
automatic: `Rat.subsingleton_ringHom` makes every ring hom out of `ℚ` the
same one, so any `ℚ_[2] →+* v.adicCompletion ℚ` is a `ℚ`-algebra map. -/
theorem exists_ringEquiv_padicTwo_adicCompletion (v : HeightOneSpectrum (𝓞 ℚ))
    (hv : ((2 : ℕ) : 𝓞 ℚ) ∈ v.asIdeal) :
    ∃ e : ℚ_[2] ≃+* v.adicCompletion ℚ,
      (∀ x : ℤ_[2], e (x : ℚ_[2]) ∈ v.adicCompletionIntegers ℚ) ∧
      Continuous e ∧ Continuous e.symm := by
  obtain rfl := symm_primesEquiv_of_natCast_mem 2 Nat.prime_two v hv
  letI : Algebra ℚ (HeightOneSpectrum.adicCompletion ℚ
      ((Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).symm ⟨2, Nat.prime_two⟩)) :=
    HeightOneSpectrum.instAlgebraAdicCompletion (𝓞 ℚ) ℚ _
  refine ⟨(Padic.adicCompletionEquiv (𝓞 ℚ) ⟨2, Nat.prime_two⟩).toAlgEquiv.toRingEquiv,
    fun x => ?_,
    (Padic.adicCompletionEquiv (𝓞 ℚ) ⟨2, Nat.prime_two⟩).continuous,
    (Padic.adicCompletionEquiv (𝓞 ℚ) ⟨2, Nat.prime_two⟩).symm.continuous⟩
  have h := PadicInt.coe_adicCompletionIntegersEquiv_apply (𝓞 ℚ) ⟨2, Nat.prime_two⟩ x
  exact h ▸ (PadicInt.adicCompletionIntegersEquiv (𝓞 ℚ) ⟨2, Nat.prime_two⟩ x).2

/-- **The valuation of `ℚ_[2]ᵃˡᵍ` is Galois-invariant** (PROVEN): it is the
spectral norm of `ℚ_[2]`, and `spectralNorm_eq_of_equiv` says a
`ℚ_[2]`-automorphism preserves it (the minimal polynomial is unchanged). -/
lemma valued_v_padicAlgCl_apply (σ : Γ ℚ_[2]) (z : ℚ_[2]ᵃˡᵍ) :
    Valued.v (σ z) = Valued.v z := by
  apply NNReal.coe_injective
  exact (spectralNorm_eq_of_equiv σ z).symm

/-- **The maximal ideal of `Z2bar` is Galois-stable** (PROVEN): membership is
`Valued.v < 1` (`Valuation.mem_maximalIdeal_iff`) and the valuation is
Galois-invariant. -/
lemma smul_mem_maximalIdeal_Z2bar (σ : Γ ℚ_[2]) {z : Z2bar}
    (hz : z ∈ IsLocalRing.maximalIdeal Z2bar) :
    σ • z ∈ IsLocalRing.maximalIdeal Z2bar := by
  rw [Valuation.mem_maximalIdeal_iff] at hz ⊢
  show Valued.v (σ (z : ℚ_[2]ᵃˡᵍ)) < 1
  rwa [valued_v_padicAlgCl_apply]

/-- **The `Γ ℚ_[2]`-action on `Z2bar` is additive** (PROVEN): the action of
`Defs.lean` is the restriction of a field automorphism, so it commutes with
subtraction on the nose. (The instance is only a `MulAction`, so `smul_sub`
does not apply.) -/
lemma smul_sub_Z2bar (σ : Γ ℚ_[2]) (a b : Z2bar) : σ • (a - b) = σ • a - σ • b := by
  apply Subtype.ext
  show σ ((a : ℚ_[2]ᵃˡᵍ) - b) = σ a - σ b
  exact map_sub σ _ _

/-- **The `Z2bar` spelling of inertia is NORMAL in `Γ ℚ_[2]`** (PROVEN), the
exact analogue of `Field.absoluteGaloisGroup.conj_mem_localInertiaGroup` for
the other spelling. This is what absorbs the conjugation ambiguity of
`Field.absoluteGaloisGroup.map` in the assembly below. -/
lemma conj_mem_inertia_Z2bar (σ : Γ ℚ_[2]) {ι : Γ ℚ_[2]}
    (hι : ι ∈ AddSubgroup.inertia
      ((IsLocalRing.maximalIdeal Z2bar).toAddSubgroup : AddSubgroup Z2bar) (Γ ℚ_[2])) :
    σ * ι * σ⁻¹ ∈ AddSubgroup.inertia
      ((IsLocalRing.maximalIdeal Z2bar).toAddSubgroup : AddSubgroup Z2bar) (Γ ℚ_[2]) := by
  intro z
  have key := smul_mem_maximalIdeal_Z2bar σ (hι (σ⁻¹ • z))
  rw [smul_sub_Z2bar, smul_smul, smul_smul, smul_inv_smul] at key
  exact key

/-- **The two spellings of local inertia at `2` agree** (LEAF — this is
precisely the identification that the previous owner of
`exists_padicTwoEmbedding_of_mem` flagged as "WHAT IS GENUINELY MISSING",
and it is now all that is missing: everything else on that route is PROVEN
above and below).

`localInertiaGroup v` (`AbsoluteGaloisGroup.lean`) is the inertia of
`IsLocalRing.maximalIdeal (IntegralClosure 𝒪_v ((v.adicCompletion ℚ)ᵃˡᵍ))`,
while `IsHardlyRamified.isTameAtTwo` (`Defs.lean`) uses the inertia of
`IsLocalRing.maximalIdeal Z2bar` with
`Z2bar = Valued.v.valuationSubring (ℚ_[2]ᵃˡᵍ)`. The claim is that the
topological isomorphism `e : ℚ_[2] ≅ ℚ_v` of the previous lemma carries the
one to the other.

THE ROUTE, in the vocabulary that exists here — it is the template of
`CompletionTransport.lean`'s `icMap` / `map_mem_localInertiaGroup`, run
with `Z2bar` in the source slot instead of an `IntegralClosure`:

* `Z2bar` IS the integral closure of `ℤ_[2]` in `ℚ_[2]ᵃˡᵍ`: membership in
  `Z2bar` is `spectralNorm ℚ_[2] (ℚ_[2]ᵃˡᵍ) z ≤ 1`, and
  `AbsoluteGaloisGroup.lean`'s `isIntegral_of_spectralNorm_le_one` turns
  that into `IsIntegral (Valued.v).integer z` — which needs a
  `Valued ℚ_[2] ℝ≥0` (`NormedField.toValued`) together with its `RankOne`,
  neither of which mathlib provides for `ℚ_[2]` (it provides both for
  `PadicAlgCl 2`);

  **A MEASURED WARNING ON THAT STEP, so the next owner does not lose the
  cycle this one lost.** Building those two instances is easy — `RankOne`
  copies `PadicAlgCl`'s (`hom' := MonoidWithZeroHom.ValueGroup₀.embedding`,
  `strictMono' := embedding_strictMono`, nontriviality witnessed by `2`,
  whose norm is `1/2` by `Padic.norm_p`) and both elaborate in seconds. The
  step that does NOT work is then applying
  `isIntegral_of_spectralNorm_le_one` at `K := ℚ_[2]`: that lemma is stated
  under `attribute [local instance] Valued.toNormedField`, so the
  `spectralNorm ℚ_[2] _` in ITS hypothesis is taken with respect to
  `Valued.toNormedField (NormedField.toValued)` — whose norm is
  `RankOne.hom (Valued.v.restrict x)` — while `Z2bar` and `PadicAlgCl`'s
  own `spectralNorm` are taken with respect to `Padic.instNormedField`.
  The two `NormedField ℚ_[2]` structures are propositionally but not
  definitionally equal, and unification between them **diverges**: the
  application times out at `whnf` even at `maxHeartbeats 2000000`, so it is
  not a resource-limit problem and a bump will not fix it. (This is the
  same class of trap as the two `Algebra ℚ (v.adicCompletion ℚ)` instances
  handled by the `letI` in `exists_ringEquiv_padicTwo_adicCompletion`,
  which is why that `letI` is there.)

  Two ways round it, neither attempted here. (a) Prove the roundtrip
  `Valued.v.norm = (‖·‖)` on `ℚ_[2]` — mathlib does exactly this for
  `ℂ_[p]` in `PadicComplex.norm_eq_norm'`, and
  `Valued.toNormedField.norm_le_one_iff` already gives the `≤ 1` half,
  which may be all that is needed since `spectralValue p ≤ 1` depends only
  on which coefficients have norm `≤ 1`. (b) Avoid `ℚ_[2]` on the
  integrality side altogether: apply `isIntegral_of_spectralNorm_le_one` at
  `K := v.adicCompletion ℚ`, where the adic `Valued` instance is the only
  one in play and no competing `NormedField` exists — for which one needs
  `e` to compare spectral norms, and mathlib's
  `Rat.HeightOneSpectrum.adicCompletion.padicEquiv_bijOn` (`e` carries
  `𝒪_v` BIJECTIVELY onto the norm-`≤ 1` subring of `ℚ_[2]`) is the
  quantitative input that direction wants;
* `he` says `e` carries `ℤ_[2]` into `𝒪_v`, so
  `IsIntegral.map_of_comp_eq` along `AlgebraicClosure.map e` turns that
  into `IsIntegral 𝒪_v (AlgebraicClosure.map e z)`, i.e. gives a ring hom
  `Z2bar →+* IntegralClosure 𝒪_v ((v.adicCompletion ℚ)ᵃˡᵍ)`, exactly as
  `isIntegral_algebraicClosureMap` / `icMap` do downstream of a map of
  completions;
* `Field.absoluteGaloisGroup.lift_map` makes that hom equivariant for
  `Field.absoluteGaloisGroup.map e` upstairs and `κ` downstairs, so `hκ`
  applies to the image;
* the reflection `mem_maximalIdeal_of_icMap` — a ring hom of LOCAL rings
  sends units to units, so a preimage of a non-unit is a non-unit — brings
  the conclusion back to `IsLocalRing.maximalIdeal Z2bar`.

FAITHFULNESS: the conclusion is an inertia-only containment about a VALUE
(`e`, pinned by `he` and the two continuity clauses), never an existence of
a coordinate and never a `Γ`-wide rationality claim, so it is on the true
side of this development's `𝒪ᵥ` descent rule. `_hcont` / `_hcont'` are
underscored only because the route above does not consume them — they are
kept because without SOME pinning of `e` beyond `he` the statement would
quantify over arbitrary abstract embeddings, and the automatic continuity
that would justify that is itself a theorem nobody here has. -/
theorem map_mem_inertia_Z2bar_of_mem_localInertiaGroup
    (v : HeightOneSpectrum (𝓞 ℚ)) (e : ℚ_[2] ≃+* v.adicCompletion ℚ)
    (_he : ∀ x : ℤ_[2], e (x : ℚ_[2]) ∈ v.adicCompletionIntegers ℚ)
    (_hcont : Continuous e) (_hcont' : Continuous e.symm)
    {κ : Γ (v.adicCompletion ℚ)} (_hκ : κ ∈ localInertiaGroup v) :
    Field.absoluteGaloisGroup.map e.toRingHom κ ∈
      AddSubgroup.inertia
        ((IsLocalRing.maximalIdeal Z2bar).toAddSubgroup : AddSubgroup Z2bar) (Γ ℚ_[2]) :=
  sorry

/-- **The local embedding `ℚ_2 ↪ F_w` at a place over `2`, and inertia**
(PROVEN, 2026-07-26, over the single leaf
`map_mem_inertia_Z2bar_of_mem_localInertiaGroup` above).

`F_w` is complete and contains `ℚ`, and `w | 2`, so the `w`-adic topology
restricts to the `2`-adic topology on `ℚ` and the inclusion `ℚ → F_w`
extends by continuity to the completion `ℚ_[2]`. The resulting `φ` is a
LOCAL homomorphism of complete discretely valued fields, so the induced
map `Γ F_w → Γ ℚ_[2]` carries inertia into inertia.

WHY BOTH HALVES ARE ONE STATEMENT: the inertia conclusion is about the
SPECIFIC `φ` produced by the first half. An arbitrary abstract `φ` over `ℚ`
would also do — every field embedding of `ℚ_[2]` into a complete field over
`ℚ` is automatically continuous — but that automatic continuity is itself a
theorem nobody here has, so bundling is the honest form.

THE PROOF, now executed:

* `exists_ringEquiv_padicTwo_adicCompletion` (above) identifies `ℚ_[2]`
  with `v.adicCompletion ℚ` for `v = w.under (𝓞 ℚ)`, which contains `2`
  because `w` does;
* `HeightOneSpectrum.adicCompletionMap v w (algebraMap ℚ F) _`
  (`CompletionTransport.lean`) gives `v.adicCompletion ℚ →+* w.adicCompletion F`
  and `φ` is its composite with that identification. The `comp` clause is
  `RingHom.ext_rat`: `w.adicCompletion F` is a ring and every ring hom out
  of `ℚ` into it is the same one, so the clause holds for ANY `φ`;
* `adicCompletionMap_mem_integers` makes the completion map LOCAL, so
  `Field.absoluteGaloisGroup.map_mem_localInertiaGroup` carries
  `localInertiaGroup w` into `localInertiaGroup v`; the leaf then crosses
  from `localInertiaGroup v` to the `Z2bar` spelling;
* `Field.absoluteGaloisGroup.exists_conj_map_comp'` supplies the single
  argument-independent conjugator relating `map (φ₀ ∘ e)` to
  `map e ∘ map φ₀`, and `conj_mem_inertia_Z2bar` (normality) absorbs it.

FAITHFULNESS: this asks only for inertia-only containments and for a VALUE
(the map `φ`) determined by continuity, never for `Γ`-wide rationality; it
is on the true side of the `𝒪ᵥ` descent rule. -/
theorem exists_padicTwoEmbedding_of_mem
    (F : Type u) [Field F] [NumberField F] (w : HeightOneSpectrum (𝓞 F))
    (hw : ((2 : ℕ) : 𝓞 F) ∈ w.asIdeal) :
    ∃ φ : ℚ_[2] →+* w.adicCompletion F,
      φ.comp (algebraMap ℚ ℚ_[2]) =
        (algebraMap F (w.adicCompletion F)).comp (algebraMap ℚ F) ∧
      ∀ ι ∈ localInertiaGroup w,
        Field.absoluteGaloisGroup.map φ ι ∈
          AddSubgroup.inertia
            ((IsLocalRing.maximalIdeal Z2bar).toAddSubgroup : AddSubgroup Z2bar)
            (Γ ℚ_[2]) := by
  classical
  set v : HeightOneSpectrum (𝓞 ℚ) := w.under (𝓞 ℚ) with hvdef
  have hv2 : ((2 : ℕ) : 𝓞 ℚ) ∈ v.asIdeal := by
    show algebraMap (𝓞 ℚ) (𝓞 F) ((2 : ℕ) : 𝓞 ℚ) ∈ w.asIdeal
    rwa [map_natCast]
  obtain ⟨e, heint, hecont, hecont'⟩ := exists_ringEquiv_padicTwo_adicCompletion v hv2
  have hcomm : ∀ a : 𝓞 ℚ,
      (algebraMap ℚ F) (algebraMap (𝓞 ℚ) ℚ a)
        = algebraMap (𝓞 F) F (algebraMap (𝓞 ℚ) (𝓞 F) a) := by
    intro a
    rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
  have hmem : v.asIdeal ≤ Ideal.comap (algebraMap (𝓞 ℚ) (𝓞 F)) w.asIdeal := le_rfl
  have hcompl : ∀ s : 𝓞 ℚ, s ∉ v.asIdeal →
      algebraMap (𝓞 ℚ) (𝓞 F) s ∉ w.asIdeal := fun _ hs => hs
  have hψ : UniformContinuous
      (WithVal.map (v.valuation ℚ) (w.valuation F) (algebraMap ℚ F)) :=
    WithVal.uniformContinuous_map_of_le _ _
      (HeightOneSpectrum.valuation_surjective ℚ v) _
      (fun x hx => HeightOneSpectrum.valuation_map_le_of_le_one v w _ _
        hcomm hmem hcompl x hx)
  have hint : ∀ x ∈ v.adicCompletionIntegers ℚ,
      HeightOneSpectrum.adicCompletionMap v w (algebraMap ℚ F) hψ x
        ∈ w.adicCompletionIntegers F :=
    fun x hx => HeightOneSpectrum.adicCompletionMap_mem_integers v w _ hψ _ hcomm hx
  refine ⟨(HeightOneSpectrum.adicCompletionMap v w (algebraMap ℚ F) hψ).comp e.toRingHom,
    RingHom.ext_rat _ _, fun ι hι => ?_⟩
  obtain ⟨τ, hτ⟩ := Field.absoluteGaloisGroup.exists_conj_map_comp'
    e.toRingHom (HeightOneSpectrum.adicCompletionMap v w (algebraMap ℚ F) hψ)
    ((HeightOneSpectrum.adicCompletionMap v w (algebraMap ℚ F) hψ).comp e.toRingHom) rfl
  rw [hτ ι]
  exact conj_mem_inertia_Z2bar τ
    (map_mem_inertia_Z2bar_of_mem_localInertiaGroup v e heint hecont hecont'
      (Field.absoluteGaloisGroup.map_mem_localInertiaGroup v w _ hint ι hι))

universe u₁ u₂

/-! #### The points comparison over a general field extension

`FlatProlongation.lean` proves the four-layer points comparison
`dvrPointsEquiv` for the pair `(K, K_v)` of a number field and one of its
completions, and that is the wrong pair for base change: what is needed
below is the pair `(K_v, L_w)` of two COMPLETIONS. The five declarations of
this section are that development at a general field extension `F ⊆ E`;
they are the only pieces of the `dvrPointsEquiv` package whose statements
mention a number field, and everything else (`liftEquiv_convOne`,
`liftEquiv_convMul`, `liftEquiv_comp`, `vendored_one_eq_convOne`,
`vendored_mul_eq_convMul`) is imported from there unchanged.

The section uses a `variable` block, which the file otherwise avoids: the
reason for avoiding it (a structure's FIELDS do not trigger automatic
variable inclusion) does not apply here, since nothing in this section is a
structure. -/

section FlatBaseChange

open _root_.TensorProduct _root_.WithConv

variable {F E : Type*} [Field F] [Field E] [Algebra F E]

/-- **Every element of `Eᵃˡᵍ` integral over `F` lies in the image of the
chosen embedding `Fᵃˡᵍ → Eᵃˡᵍ`** (PROVEN): the minimal polynomial of `z`
over `F` already splits over `Fᵃˡᵍ`, and the roots of the pushed-forward
polynomial are exactly the images of the roots upstairs.

(The `(K, K_v)` instance of this is `FlatProlongation.lean`'s
`mem_range_algebraicClosureMap_of_isIntegral`; the argument is pure field
theory and is repeated here at the generality the base change needs.) -/
theorem mem_range_algebraicClosureMapExt_of_isIntegral (z : AlgebraicClosure E)
    (hz : IsIntegral F z) :
    z ∈ Set.range (AlgebraicClosure.map (algebraMap F E)) := by
  classical
  have hμ0 : minpoly F z ≠ 0 := minpoly.ne_zero hz
  have hsplit : ((minpoly F z).map (algebraMap F (AlgebraicClosure F))).Splits :=
    IsAlgClosed.splits ((minpoly F z).map (algebraMap F (AlgebraicClosure F)))
  have hfactor : (minpoly F z).map (algebraMap F (AlgebraicClosure E)) =
      ((minpoly F z).map (algebraMap F (AlgebraicClosure F))).map
        (AlgebraicClosure.map (algebraMap F E)) := by
    rw [Polynomial.map_map]
    congr 1
    refine RingHom.ext fun x => ?_
    show algebraMap F (AlgebraicClosure E) x =
      AlgebraicClosure.map (algebraMap F E) (algebraMap F (AlgebraicClosure F) x)
    rw [AlgebraicClosure.map_algebraMap, ← IsScalarTower.algebraMap_apply]
  have hroot : z ∈ ((minpoly F z).map (algebraMap F (AlgebraicClosure E))).roots := by
    rw [Polynomial.mem_roots
      (Polynomial.map_ne_zero_iff (algebraMap F _).injective |>.mpr hμ0)]
    rw [Polynomial.IsRoot, Polynomial.eval_map, ← Polynomial.aeval_def]
    exact minpoly.aeval F z
  rw [hfactor, Polynomial.Splits.roots_map hsplit, Multiset.mem_map] at hroot
  obtain ⟨r, _, hr⟩ := hroot
  exact ⟨r, hr⟩

variable (F E) in
/-- The chosen embedding `Fᵃˡᵍ → Eᵃˡᵍ`, packaged as an `F`-algebra hom. -/
noncomputable def algebraicClosureMapExtAlgHom :
    AlgebraicClosure F →ₐ[F] AlgebraicClosure E where
  toRingHom := AlgebraicClosure.map (algebraMap F E)
  commutes' := fun x => by
    show AlgebraicClosure.map (algebraMap F E) (algebraMap F (AlgebraicClosure F) x) = _
    rw [AlgebraicClosure.map_algebraMap (algebraMap F E) x]
    exact (IsScalarTower.algebraMap_apply F E (AlgebraicClosure E) x).symm

/-- **The points of a FINITE `F`-algebra do not see the extension** (PROVEN):
for `B` finite over `F`, postcomposition with `Fᵃˡᵍ → Eᵃˡᵍ` is a bijection
from the `Fᵃˡᵍ`-points of `B` to its `Eᵃˡᵍ`-points, because every
`Eᵃˡᵍ`-point has algebraic image and hence factors through the copy of
`Fᵃˡᵍ` inside `Eᵃˡᵍ`. -/
noncomputable def algHomEquivExtOfFinite (B : Type*) [CommRing B] [Algebra F B]
    [Module.Finite F B] :
    (B →ₐ[F] AlgebraicClosure E) ≃ (B →ₐ[F] AlgebraicClosure F) where
  toFun φ := (AlgEquiv.ofInjective (algebraicClosureMapExtAlgHom F E)
      (algebraicClosureMapExtAlgHom F E).toRingHom.injective).symm.toAlgHom.comp
    (φ.codRestrict (algebraicClosureMapExtAlgHom F E).range (fun b => by
      obtain ⟨r, hr⟩ := mem_range_algebraicClosureMapExt_of_isIntegral (φ b)
        ((Algebra.IsIntegral.isIntegral (R := F) b).map φ)
      exact ⟨r, hr⟩))
  invFun ψ := (algebraicClosureMapExtAlgHom F E).comp ψ
  left_inv φ := by
    refine AlgHom.ext fun b => ?_
    exact congrArg Subtype.val
      ((AlgEquiv.ofInjective (algebraicClosureMapExtAlgHom F E)
        (algebraicClosureMapExtAlgHom F E).toRingHom.injective).apply_symm_apply
        (φ.codRestrict (algebraicClosureMapExtAlgHom F E).range (fun b => by
          obtain ⟨r, hr⟩ := mem_range_algebraicClosureMapExt_of_isIntegral (φ b)
            ((Algebra.IsIntegral.isIntegral (R := F) b).map φ)
          exact ⟨r, hr⟩) b))
  right_inv ψ := by
    refine AlgHom.ext fun b => ?_
    apply (AlgEquiv.ofInjective (algebraicClosureMapExtAlgHom F E)
      (algebraicClosureMapExtAlgHom F E).toRingHom.injective).injective
    refine ((AlgEquiv.ofInjective (algebraicClosureMapExtAlgHom F E)
      (algebraicClosureMapExtAlgHom F E).toRingHom.injective).apply_symm_apply _).trans ?_
    apply Subtype.ext
    rfl

/-- The inverse of `algHomEquivExtOfFinite` is postcomposition with the
embedding of algebraic closures. -/
theorem algHomEquivExtOfFinite_symm_apply {B : Type*} [CommRing B] [Algebra F B]
    [Module.Finite F B] (ψ : B →ₐ[F] AlgebraicClosure F) :
    (algHomEquivExtOfFinite (E := E) B).symm ψ =
      (algebraicClosureMapExtAlgHom F E).comp ψ :=
  rfl

section ExtConv

variable {B : Type*} [CommRing B] [Bialgebra F B] [Module.Finite F B]

/-- `algHomEquivExtOfFinite` preserves the convolution unit. -/
theorem algHomEquivExtOfFinite_convOne :
    algHomEquivExtOfFinite (E := E) B
      ((1 : WithConv (B →ₐ[F] AlgebraicClosure E)).ofConv) =
      (1 : WithConv (B →ₐ[F] AlgebraicClosure F)).ofConv := by
  apply (algHomEquivExtOfFinite (E := E) B).symm.injective
  rw [Equiv.symm_apply_apply, algHomEquivExtOfFinite_symm_apply]
  refine AlgHom.ext fun b => ?_
  rw [AlgHom.comp_apply, AlgHom.convOne_apply, AlgHom.convOne_apply, AlgHom.commutes]

/-- `algHomEquivExtOfFinite` preserves the convolution product. -/
theorem algHomEquivExtOfFinite_convMul
    (ψ₁ ψ₂ : WithConv (B →ₐ[F] AlgebraicClosure E)) :
    algHomEquivExtOfFinite (E := E) B ((ψ₁ * ψ₂).ofConv) =
      (toConv (algHomEquivExtOfFinite (E := E) B ψ₁.ofConv) *
        toConv (algHomEquivExtOfFinite (E := E) B ψ₂.ofConv)).ofConv := by
  apply (algHomEquivExtOfFinite (E := E) B).symm.injective
  rw [Equiv.symm_apply_apply, algHomEquivExtOfFinite_symm_apply,
    AlgHom.comp_convMul_distrib,
    ← algHomEquivExtOfFinite_symm_apply (E := E)
      (algHomEquivExtOfFinite (E := E) B ψ₁.ofConv),
    ← algHomEquivExtOfFinite_symm_apply (E := E)
      (algHomEquivExtOfFinite (E := E) B ψ₂.ofConv),
    Equiv.symm_apply_apply, Equiv.symm_apply_apply]

/-- `algHomEquivExtOfFinite` intertwines postcomposition by `σ ∈ Γ E` with
postcomposition by its restriction in `Γ F`. -/
theorem algHomEquivExtOfFinite_comp (σ : Γ E) (ψ : B →ₐ[F] AlgebraicClosure E) :
    algHomEquivExtOfFinite (E := E) B ((σ.toAlgHom.restrictScalars F).comp ψ) =
      (Field.absoluteGaloisGroup.map (algebraMap F E) σ).toAlgHom.comp
        (algHomEquivExtOfFinite (E := E) B ψ) := by
  apply (algHomEquivExtOfFinite (E := E) B).symm.injective
  rw [Equiv.symm_apply_apply, algHomEquivExtOfFinite_symm_apply]
  have h2 : (algebraicClosureMapExtAlgHom F E).comp
      (algHomEquivExtOfFinite (E := E) B ψ) = ψ := by
    rw [← algHomEquivExtOfFinite_symm_apply, Equiv.symm_apply_apply]
  refine AlgHom.ext fun b => ?_
  refine Eq.symm ?_
  calc ((algebraicClosureMapExtAlgHom F E).comp
        ((Field.absoluteGaloisGroup.map (algebraMap F E) σ).toAlgHom.comp
          (algHomEquivExtOfFinite (E := E) B ψ))) b
      = σ (AlgebraicClosure.map (algebraMap F E)
          ((algHomEquivExtOfFinite (E := E) B ψ) b)) :=
        Field.absoluteGaloisGroup.lift_map _ σ _
    _ = σ (ψ b) := congrArg σ congr($(h2) b)
    _ = ((σ.toAlgHom.restrictScalars F).comp ψ) b := rfl

end ExtConv

section ExtCore

variable (R : Type*) [CommRing R] [Algebra R F] [Algebra R E] [IsScalarTower R F E]
variable (O : Type*) [CommRing O] [Algebra R O] [Algebra O E] [IsScalarTower R O E]
variable (H : Type*) [CommRing H] [HopfAlgebra R H] [Module.Finite R H]

/-- **The four-layer points comparison**, over a general integral package
`R → O → E` with generic fibre `R → F`: the `Eᵃˡᵍ`-points of the generic
fibre of the base-changed Hopf algebra `O ⊗[R] H` are the `Fᵃˡᵍ`-points of
`F ⊗[R] H`. (`AlgHom.liftEquiv` three times, then
`algHomEquivExtOfFinite`; the exact analogue of `dvrPointsEquiv`.) -/
noncomputable def extPointsEquiv :
    ((E ⊗[O] (O ⊗[R] H)) →ₐ[E] AlgebraicClosure E) ≃
      ((F ⊗[R] H) →ₐ[F] AlgebraicClosure F) :=
  (AlgHom.liftEquiv O E (O ⊗[R] H) (AlgebraicClosure E)).symm.trans
    ((AlgHom.liftEquiv R O H (AlgebraicClosure E)).symm.trans
      ((AlgHom.liftEquiv R F H (AlgebraicClosure E)).trans
        (algHomEquivExtOfFinite (E := E) (F ⊗[R] H))))

/-- The points comparison sends the convolution unit to the convolution
unit. -/
theorem extPointsEquiv_one :
    extPointsEquiv (F := F) R O H
        (1 : (E ⊗[O] (O ⊗[R] H)) →ₐ[E] AlgebraicClosure E) =
      (1 : WithConv ((F ⊗[R] H) →ₐ[F] AlgebraicClosure F)).ofConv := by
  show algHomEquivExtOfFinite (E := E) (F ⊗[R] H)
    ((AlgHom.liftEquiv R F H (AlgebraicClosure E))
      ((AlgHom.liftEquiv R O H (AlgebraicClosure E)).symm
        ((AlgHom.liftEquiv O E (O ⊗[R] H) (AlgebraicClosure E)).symm 1))) = _
  rw [vendored_one_eq_convOne, liftEquiv_symm_convOne, liftEquiv_symm_convOne,
    liftEquiv_convOne, algHomEquivExtOfFinite_convOne]

/-- The points comparison sends the convolution product to the convolution
product. -/
theorem extPointsEquiv_mul (φ ψ : (E ⊗[O] (O ⊗[R] H)) →ₐ[E] AlgebraicClosure E) :
    extPointsEquiv (F := F) R O H (φ * ψ) =
      (toConv (extPointsEquiv (F := F) R O H φ) *
        toConv (extPointsEquiv (F := F) R O H ψ)).ofConv := by
  show algHomEquivExtOfFinite (E := E) (F ⊗[R] H)
    ((AlgHom.liftEquiv R F H (AlgebraicClosure E))
      ((AlgHom.liftEquiv R O H (AlgebraicClosure E)).symm
        ((AlgHom.liftEquiv O E (O ⊗[R] H) (AlgebraicClosure E)).symm (φ * ψ)))) = _
  rw [vendored_mul_eq_convMul, liftEquiv_symm_convMul, liftEquiv_symm_convMul,
    liftEquiv_convMul, algHomEquivExtOfFinite_convMul]
  rfl

/-- The points comparison intertwines the postcomposition action of `Γ E`
with the postcomposition action of its restriction in `Γ F`. -/
theorem extPointsEquiv_smul (σ : Γ E)
    (φ : (E ⊗[O] (O ⊗[R] H)) →ₐ[E] AlgebraicClosure E) :
    extPointsEquiv (F := F) R O H (σ • φ) =
      (Field.absoluteGaloisGroup.map (algebraMap F E) σ).toAlgHom.comp
        (extPointsEquiv (F := F) R O H φ) := by
  have h₀ : σ • φ = (σ.toAlgHom : AlgebraicClosure E →ₐ[E] AlgebraicClosure E).comp φ :=
    AlgHom.ext fun _ => rfl
  show algHomEquivExtOfFinite (E := E) (F ⊗[R] H)
    ((AlgHom.liftEquiv R F H (AlgebraicClosure E))
      ((AlgHom.liftEquiv R O H (AlgebraicClosure E)).symm
        ((AlgHom.liftEquiv O E (O ⊗[R] H) (AlgebraicClosure E)).symm (σ • φ)))) = _
  rw [h₀, liftEquiv_symm_comp, liftEquiv_symm_comp]
  have hrs : ((σ.toAlgHom.restrictScalars O).restrictScalars R :
      AlgebraicClosure E →ₐ[R] AlgebraicClosure E) =
      ((σ.toAlgHom.restrictScalars F).restrictScalars R) := rfl
  rw [hrs, liftEquiv_comp, algHomEquivExtOfFinite_comp]
  rfl

end ExtCore

/-- **Base change of a SINGLE finite flat prolongation along `𝒪_v → 𝒪_w`**
(PROVEN, 2026-07-26 — the geometric core of the flatness half of item 1/2
of the audit's list; split off from `isFlatAt_map_of_isFlatAt_under`, which
is PROVEN over it).

`ρ.HasFlatProlongationAt v` says that the `Γ K_v`-set underlying `M` is the
set of `K_vᵃˡᵍ`-points of the generic fibre of a finite flat `𝒪_v`-Hopf
algebra `G`. This leaf is the base-change of that ONE package along the
local map `𝒪_v → 𝒪_w`; the quantifier over open ideals which distinguishes
`IsFlatAt` from `HasFlatProlongationAt` has already been discharged by the
consumer below, so nothing here is about the coefficient ring.

THE PROOF, in the vocabulary of `CompletionTransport.lean` and
`FlatProlongation.lean` (it is a second copy of the `dvrPointsEquiv`
development, at a different pair of rings — that copy is the
`extPointsEquiv` section above):

* `HeightOneSpectrum.adicCompletionMap v w (algebraMap K L) hψ : K_v →+* L_w`
  exists (the very map `isUnramifiedAt_map_of_isUnramifiedAt_under` builds,
  from `valuation_map_le_of_le_one` + `WithVal.uniformContinuous_map_of_le`),
  it is LOCAL (`adicCompletionMap_mem_integers`), and
  `Field.absoluteGaloisGroup.intMap` restricts it to `𝒪_v →+* 𝒪_w`. That is
  the `Algebra 𝒪_v 𝒪_w` used below, together with the induced
  `Algebra 𝒪_v L_w`, `Algebra K_v L_w` and the two scalar towers;
* the witness upstairs is `G' := 𝒪_w ⊗[𝒪_v] G`. `CommRing`, `HopfAlgebra 𝒪_w`
  (mathlib's `TensorProduct` Hopf instance, `B := 𝒪_w`, `A := G`),
  `Module.Flat 𝒪_w` and `Module.Finite 𝒪_w` are all instances;
* étaleness of the generic fibre is `Algebra.Etale.baseChange` transported
  across
  `L_w ⊗[𝒪_w] (𝒪_w ⊗[𝒪_v] G) ≃ₐ L_w ⊗[𝒪_v] G ≃ₐ L_w ⊗[K_v] (K_v ⊗[𝒪_v] G)`
  (`Algebra.TensorProduct.cancelBaseChange`, twice);
* the points comparison is `extPointsEquiv 𝒪_v 𝒪_w G` above:
  `((L_w ⊗[𝒪_w] G') →ₐ[L_w] L_wᵃˡᵍ) ≃ ((K_v ⊗[𝒪_v] G) →ₐ[K_v] K_vᵃˡᵍ)`,
  by `AlgHom.liftEquiv` three times and then the finite-algebra points
  bijection `algHomEquivExtOfFinite` (every `L_wᵃˡᵍ`-point of a FINITE
  `K_v`-algebra has algebraic image, hence lands in the copy of `K_vᵃˡᵍ`
  inside `L_wᵃˡᵍ`); `liftEquiv_convOne`/`liftEquiv_convMul`/`liftEquiv_comp`
  carry the convolution-monoid bookkeeping through the `liftEquiv` layers;
* the equivariance is where the CONJUGATOR enters, exactly as in the
  tame-at-`2` clause of `isHilbertHardlyRamified_map_of_isHardlyRamified`:
  the two routes `Γ L_w → Γ K`, one through `Γ L` and one through `Γ K_v`,
  differ by one argument-independent `μ ∈ Γ K`
  (`Field.absoluteGaloisGroup.exists_conj_map_comp'`, twice), and the fix is
  to conjugate the COMPARISON MAP rather than the character: replacing the
  bijection `f` of the package downstairs by `ρ μ ∘ f` turns
  `f (ψ σ • φ) = ρ (ψ σ) (f φ)` into
  `(ρ μ ∘ f) (σ • φ) = ρ (μ * ψ σ * μ⁻¹) ((ρ μ ∘ f) φ)`, which is the
  `Γ L_w`-equivariance the package upstairs asks for, on the nose.

FORMALIZATION NOTE ON THE UNIVERSES (why `L : Type (max u₁ u₂)` rather than
`Type*`). `GaloisRep.HasFlatProlongationAt` quantifies its Hopf-algebra
witness over `Type uK`, the universe of the BASE FIELD. So the conclusion
demands `G' : Type uL` while the hypothesis supplies `G : Type uK`, and the
base change `𝒪_w ⊗[𝒪_v] G` lives in `Type (max uK uL)`. Writing
`L : Type (max u₁ u₂)` for `K : Type u₁` is exactly the constraint
`uK ≤ uL`, under which that is `Type uL`. This is a formalization artifact,
not a mathematical hypothesis: `G` is finite flat over the DVR `𝒪_v`, hence
free of finite rank, so `𝒪_w ⊗[𝒪_v] G` is always `Small.{uL}` and the
unrestricted statement would follow by transporting the Hopf structure
along a `Shrink` equivalence — machinery mathlib does not have. Every
consumer in this development instantiates at `K = ℚ : Type 0`, where the
constraint is vacuous.

FAITHFULNESS: a statement about the EXISTENCE of a prolongation upstairs
given one downstairs, produced by base change — not a descent of existence
from `𝒪^nr`, so the `𝒪ᵥ` rule does not bite. -/
theorem hasFlatProlongationAt_map_of_hasFlatProlongationAt_under
    {K : Type u₁} [Field K] [NumberField K]
    {L : Type (max u₁ u₂)} [Field L] [NumberField L] [Algebra K L]
    {A : Type*} [CommRing A] [TopologicalSpace A]
    {M : Type*} [AddCommGroup M] [Module A M]
    (ρ : GaloisRep K A M) (w : HeightOneSpectrum (𝓞 L))
    (h : ρ.HasFlatProlongationAt (w.under (𝓞 K))) :
    (ρ.map (algebraMap K L)).HasFlatProlongationAt w := by
  classical
  set v : HeightOneSpectrum (𝓞 K) := w.under (𝓞 K)
  have hcomm : ∀ a : 𝓞 K,
      (algebraMap K L) (algebraMap (𝓞 K) K a)
        = algebraMap (𝓞 L) L (algebraMap (𝓞 K) (𝓞 L) a) := fun a => by
    rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
  have hmem : v.asIdeal ≤ Ideal.comap (algebraMap (𝓞 K) (𝓞 L)) w.asIdeal := le_rfl
  have hcompl : ∀ s : 𝓞 K, s ∉ v.asIdeal →
      algebraMap (𝓞 K) (𝓞 L) s ∉ w.asIdeal := fun _ hs => hs
  have hψ : UniformContinuous
      (WithVal.map (v.valuation K) (w.valuation L) (algebraMap K L)) :=
    WithVal.uniformContinuous_map_of_le _ _
      (HeightOneSpectrum.valuation_surjective K v) _
      (fun x hx => HeightOneSpectrum.valuation_map_le_of_le_one v w _ _
        hcomm hmem hcompl x hx)
  have hint : ∀ x ∈ v.adicCompletionIntegers K,
      HeightOneSpectrum.adicCompletionMap v w (algebraMap K L) hψ x
        ∈ w.adicCompletionIntegers L :=
    fun x hx => HeightOneSpectrum.adicCompletionMap_mem_integers v w _ hψ _ hcomm hx
  -- `𝒪_v → 𝒪_w`, `K_v → L_w` and the two scalar towers between them
  letI : Algebra ↥(v.adicCompletionIntegers K) ↥(w.adicCompletionIntegers L) :=
    (Field.absoluteGaloisGroup.intMap v w
      (HeightOneSpectrum.adicCompletionMap v w (algebraMap K L) hψ) hint).toAlgebra
  letI : Algebra (v.adicCompletion K) (w.adicCompletion L) :=
    (HeightOneSpectrum.adicCompletionMap v w (algebraMap K L) hψ).toAlgebra
  letI : Algebra ↥(v.adicCompletionIntegers K) (w.adicCompletion L) :=
    ((algebraMap ↥(w.adicCompletionIntegers L) (w.adicCompletion L)).comp
      (Field.absoluteGaloisGroup.intMap v w
        (HeightOneSpectrum.adicCompletionMap v w (algebraMap K L) hψ) hint)).toAlgebra
  haveI : IsScalarTower ↥(v.adicCompletionIntegers K) ↥(w.adicCompletionIntegers L)
      (w.adicCompletion L) := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower ↥(v.adicCompletionIntegers K) (v.adicCompletion K)
      (w.adicCompletion L) := IsScalarTower.of_algebraMap_eq fun _ => rfl
  -- the two routes `Γ L_w → Γ K` differ by the single conjugator `μ`
  obtain ⟨τ, hτ⟩ := Field.absoluteGaloisGroup.exists_conj_map_comp'
    (algebraMap K (v.adicCompletion K))
    (algebraMap (v.adicCompletion K) (w.adicCompletion L))
    ((algebraMap L (w.adicCompletion L)).comp (algebraMap K L))
    (RingHom.ext fun x =>
      HeightOneSpectrum.adicCompletionMap_coe v w (algebraMap K L) hψ x)
  obtain ⟨τ₀, hτ₀⟩ := Field.absoluteGaloisGroup.exists_conj_map_comp' (algebraMap K L)
    (algebraMap L (w.adicCompletion L))
    ((algebraMap L (w.adicCompletion L)).comp (algebraMap K L)) rfl
  obtain ⟨μ, hμ⟩ : ∃ μ : Γ K, τ₀⁻¹ * τ = μ := ⟨_, rfl⟩
  have hX : ∀ σ : Γ (w.adicCompletion L),
      Field.absoluteGaloisGroup.map (algebraMap K L)
          (Field.absoluteGaloisGroup.map (algebraMap L (w.adicCompletion L)) σ)
        = μ * Field.absoluteGaloisGroup.map (algebraMap K (v.adicCompletion K))
            (Field.absoluteGaloisGroup.map
              (algebraMap (v.adicCompletion K) (w.adicCompletion L)) σ) * μ⁻¹ := by
    intro σ
    have h1 := hτ₀ σ
    rw [hτ σ] at h1
    rw [← hμ, show τ₀⁻¹ * τ * Field.absoluteGaloisGroup.map
          (algebraMap K (v.adicCompletion K))
          (Field.absoluteGaloisGroup.map
            (algebraMap (v.adicCompletion K) (w.adicCompletion L)) σ) * (τ₀⁻¹ * τ)⁻¹
        = τ₀⁻¹ * (τ * Field.absoluteGaloisGroup.map (algebraMap K (v.adicCompletion K))
            (Field.absoluteGaloisGroup.map
              (algebraMap (v.adicCompletion K) (w.adicCompletion L)) σ) * τ⁻¹) * τ₀
        from by group, h1]
    group
  have hinv : ∀ x : M, (ρ μ⁻¹) ((ρ μ) x) = x := by
    intro x
    show (ρ μ⁻¹ * ρ μ) x = x
    rw [← map_mul, inv_mul_cancel, map_one]
    rfl
  have hinv' : ∀ x : M, (ρ μ) ((ρ μ⁻¹) x) = x := by
    intro x
    show (ρ μ * ρ μ⁻¹) x = x
    rw [← map_mul, mul_inv_cancel, map_one]
    rfl
  have hρμ : Function.Bijective ⇑(ρ μ) :=
    ⟨fun a b hab => by rw [← hinv a, ← hinv b, hab], fun y => ⟨ρ μ⁻¹ y, hinv' y⟩⟩
  obtain ⟨G, hCR, hHopf, hFlat, hFin, hEt, f, hbij⟩ := h
  letI := hCR
  letI := hHopf
  letI := hFlat
  letI := hFin
  letI := hEt
  refine ⟨↥(w.adicCompletionIntegers L) ⊗[↥(v.adicCompletionIntegers K)] G,
    (inferInstance : CommRing
      (↥(w.adicCompletionIntegers L) ⊗[↥(v.adicCompletionIntegers K)] G)),
    (inferInstance : HopfAlgebra ↥(w.adicCompletionIntegers L)
      (↥(w.adicCompletionIntegers L) ⊗[↥(v.adicCompletionIntegers K)] G)),
    (inferInstance : Module.Flat ↥(w.adicCompletionIntegers L)
      (↥(w.adicCompletionIntegers L) ⊗[↥(v.adicCompletionIntegers K)] G)),
    (inferInstance : Module.Finite ↥(w.adicCompletionIntegers L)
      (↥(w.adicCompletionIntegers L) ⊗[↥(v.adicCompletionIntegers K)] G)),
    Algebra.Etale.of_equiv
      ((Algebra.TensorProduct.cancelBaseChange ↥(v.adicCompletionIntegers K)
          (v.adicCompletion K) (w.adicCompletion L) (w.adicCompletion L) G).trans
        (Algebra.TensorProduct.cancelBaseChange ↥(v.adicCompletionIntegers K)
          ↥(w.adicCompletionIntegers L) (w.adicCompletion L) (w.adicCompletion L) G).symm),
    { toFun := fun Φ => ρ μ (f (Additive.ofMul
        (extPointsEquiv (F := v.adicCompletion K) ↥(v.adicCompletionIntegers K)
          ↥(w.adicCompletionIntegers L) G Φ.toMul)))
      map_smul' := fun σ Φ => by
        show ρ μ (f (Additive.ofMul (extPointsEquiv (F := v.adicCompletion K)
            ↥(v.adicCompletionIntegers K) ↥(w.adicCompletionIntegers L) G
            (Additive.toMul (σ • Φ)))))
          = ((ρ.map (algebraMap K L)).toLocal w) σ
              (ρ μ (f (Additive.ofMul (extPointsEquiv (F := v.adicCompletion K)
                ↥(v.adicCompletionIntegers K) ↥(w.adicCompletionIntegers L) G Φ.toMul))))
        have hΦ : Additive.toMul (σ • Φ) = σ • Φ.toMul := rfl
        rw [hΦ, extPointsEquiv_smul]
        have hact : ∀ (g : Γ (v.adicCompletion K))
            (χ : (v.adicCompletion K ⊗[↥(v.adicCompletionIntegers K)] G)
              →ₐ[v.adicCompletion K] AlgebraicClosure (v.adicCompletion K)),
            f (Additive.ofMul (g.toAlgHom.comp χ))
              = ρ (Field.absoluteGaloisGroup.map
                  (algebraMap K (v.adicCompletion K)) g) (f (Additive.ofMul χ)) := by
          intro g χ
          exact map_smul f g (Additive.ofMul χ)
        have key : ∀ (g : Γ K) (y : M), ρ μ (ρ g y) = ρ (μ * g * μ⁻¹) (ρ μ y) := by
          intro g y
          show (ρ μ * ρ g) y = (ρ (μ * g * μ⁻¹) * ρ μ) y
          rw [← map_mul, ← map_mul]
          congr 2
          group
        have hgoal : ((ρ.map (algebraMap K L)).toLocal w) σ
            = ρ (μ * Field.absoluteGaloisGroup.map (algebraMap K (v.adicCompletion K))
                (Field.absoluteGaloisGroup.map
                  (algebraMap (v.adicCompletion K) (w.adicCompletion L)) σ) * μ⁻¹) := by
          rw [← hX σ]
          rfl
        rw [hact, hgoal]
        exact key _ _
      map_zero' := by
        show ρ μ (f (Additive.ofMul (extPointsEquiv (F := v.adicCompletion K)
          (E := w.adicCompletion L)
          ↥(v.adicCompletionIntegers K) ↥(w.adicCompletionIntegers L) G
          (Additive.toMul 0)))) = 0
        rw [toMul_zero, extPointsEquiv_one, ← vendored_one_eq_convOne, ofMul_one,
          map_zero]
        exact LinearMap.map_zero _
      map_add' := fun Φ Ψ => by
        have hmul : extPointsEquiv (F := v.adicCompletion K)
              (E := w.adicCompletion L) ↥(v.adicCompletionIntegers K)
              ↥(w.adicCompletionIntegers L) G (Additive.toMul (Φ + Ψ))
            = extPointsEquiv (F := v.adicCompletion K) (E := w.adicCompletion L)
                ↥(v.adicCompletionIntegers K) ↥(w.adicCompletionIntegers L) G Φ.toMul
              * extPointsEquiv (F := v.adicCompletion K) (E := w.adicCompletion L)
                ↥(v.adicCompletionIntegers K) ↥(w.adicCompletionIntegers L) G Ψ.toMul :=
          (extPointsEquiv_mul (F := v.adicCompletion K) (E := w.adicCompletion L)
            ↥(v.adicCompletionIntegers K) ↥(w.adicCompletionIntegers L) G
            (Additive.toMul Φ) (Additive.toMul Ψ)).trans
            (vendored_mul_eq_convMul _ _).symm
        have h1 : f (Additive.ofMul
              (extPointsEquiv (F := v.adicCompletion K) (E := w.adicCompletion L)
                  ↥(v.adicCompletionIntegers K) ↥(w.adicCompletionIntegers L) G Φ.toMul
                * extPointsEquiv (F := v.adicCompletion K) (E := w.adicCompletion L)
                  ↥(v.adicCompletionIntegers K) ↥(w.adicCompletionIntegers L) G Ψ.toMul))
            = f (Additive.ofMul (extPointsEquiv (F := v.adicCompletion K)
                (E := w.adicCompletion L) ↥(v.adicCompletionIntegers K)
                ↥(w.adicCompletionIntegers L) G Φ.toMul))
              + f (Additive.ofMul (extPointsEquiv (F := v.adicCompletion K)
                (E := w.adicCompletion L) ↥(v.adicCompletionIntegers K)
                ↥(w.adicCompletionIntegers L) G Ψ.toMul)) :=
          map_add f (Additive.ofMul _) (Additive.ofMul _)
        show ρ μ (f (Additive.ofMul (extPointsEquiv (F := v.adicCompletion K)
            (E := w.adicCompletion L) ↥(v.adicCompletionIntegers K)
            ↥(w.adicCompletionIntegers L) G (Additive.toMul (Φ + Ψ))))) = _
        exact (congrArg (fun x => (ρ μ) (f (Additive.ofMul x))) hmul).trans
          ((congrArg (⇑(ρ μ)) h1).trans (LinearMap.map_add (ρ μ) _ _)) }, ?_⟩
  exact hρμ.comp (hbij.comp (Additive.ofMul.bijective.comp
    ((extPointsEquiv (F := v.adicCompletion K) ↥(v.adicCompletionIntegers K)
      ↥(w.adicCompletionIntegers L) G).bijective.comp Additive.toMul.bijective)))

end FlatBaseChange

/-- **Flatness descends to every place over a flat place** (PROVEN,
2026-07-26, over `hasFlatProlongationAt_map_of_hasFlatProlongationAt_under`).

`GaloisRep.IsFlatAt v` asks that for every open ideal `I` of the coefficient
ring the representation on `M/IM` be the geometric points of a finite flat
group scheme over `𝒪_v` (`GaloisRep.HasFlatProlongationAt`). Two things
separate that from the leaf above, and both are discharged here:

* the quantifier over open ideals — the same `I` works upstairs and
  downstairs, so it is transported unchanged;
* the commutation `(ρ.map f).baseChange B = (ρ.baseChange B).map f`, which
  holds definitionally: `map` precomposes with `Field.absoluteGaloisGroup.map
  f` and `baseChange` postcomposes with `Module.End.baseChangeHom`, and the
  two act on opposite sides of `ρ`.

For the universe restriction on `L`, see the leaf's FORMALIZATION NOTE. -/
theorem isFlatAt_map_of_isFlatAt_under
    {K : Type u₁} [Field K] [NumberField K]
    {L : Type (max u₁ u₂)} [Field L] [NumberField L] [Algebra K L]
    {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsLocalRing A]
    {M : Type*} [AddCommGroup M] [Module A M] [Module.Finite A M] [Module.Free A M]
    (ρ : GaloisRep K A M) (w : HeightOneSpectrum (𝓞 L))
    (h : ρ.IsFlatAt (w.under (𝓞 K))) :
    (ρ.map (algebraMap K L)).IsFlatAt w := by
  refine ⟨fun I hI => ?_⟩
  have heq : (ρ.map (algebraMap K L)).baseChange (A ⧸ I)
      = (ρ.baseChange (A ⧸ I)).map (algebraMap K L) := GaloisRep.ext fun _ => rfl
  rw [heq]
  exact hasFlatProlongationAt_map_of_hasFlatProlongationAt_under
    (ρ.baseChange (A ⧸ I)) w (h.cond I hI)

/-- **Restriction of a hardly ramified representation is hardly ramified
over `F`** (PROVEN, 2026-07-26, over the two local leaves above).

The four clauses are four compatibilities of restriction along
`G_F ≤ G_ℚ`. Two of them are now PROVEN glue and two are reduced to
sharply stated local leaves:

* *determinant* (PROVEN): `GaloisRep.map` is precomposition with
  `Field.absoluteGaloisGroup.map` and `GaloisRep.det` is postcomposition
  with `LinearMap.det`, so the two commute — and because the `F`-level
  determinant clause was deliberately written through the RESTRICTION of
  the `ℚ`-adic cyclotomic character, this clause is three rewrites;
* *unramifiedness* (PROVEN): a place `w` of `F` with `2 ∉ w` and `ℓ ∉ w`
  lies over a rational prime `p ∉ {2, ℓ}` (`exists_prime_eq_ratPlace`,
  `natCast_mem_asIdeal_of_under_eq`), and inertia at `w` maps into inertia
  at `p` (`isUnramifiedAt_map_of_isUnramifiedAt_under`);
* *flatness* (PROVEN, through `isFlatAt_map_of_isFlatAt_under`): a place
  `w | ℓ` lies over `ℓ` (`under_eq_of_natCast_mem`), and flat prolongations
  base-change along `𝒪_ℓ → 𝒪_w`;
* *tameness at `2`* (over `exists_padicTwoEmbedding_of_mem`): PROVEN glue
  from the local embedding `φ : ℚ_[2] →+* F_w`, see below.

**THE TAME-AT-`2` CLAUSE GENUINELY TRANSPORTS, AND THE CONJUGATOR IS THE
WHOLE POINT.** The clause may not be dropped (the structure's docstring
records why: without it `R_F` has unbounded level at the places over `2`
and `R_F = T_F` is FALSE), so it had to be transported rather than papered
over. The obstacle is that `GaloisRep.map` is functorial only UP TO
CONJUGATION — the two routes `G_{F_w} → G_ℚ`, one through `G_F` and one
through `G_{ℚ_2}`, differ by a single argument-independent `μ ∈ G_ℚ`
(`Field.absoluteGaloisGroup.exists_conj_map_comp'`, twice) — and the
intertwining `π ∘ ρ(·) = δ(·) · π` is NOT conjugation invariant.

The fix is to conjugate the QUOTIENT rather than the character: the
`F`-level quotient is `p := π ∘ ρ(μ⁻¹)`, still surjective because `ρ(μ)`
inverts `ρ(μ⁻¹)`, and then

  `p (ρ(μ ψ(g) μ⁻¹) x) = π (ρ(ψ(g) μ⁻¹) x) = δ₀(ψ(g)) (p x)`

on the nose, with `δ := δ₀ ∘ (Γ F_w → Γ ℚ_2)`. The remaining two
conditions are exactly the shape the discriminating rule of this
development calls FAITHFUL: `δ` is unramified because inertia at `w` maps
into inertia at `2` — an inertia-only containment, supplied by
`exists_padicTwoEmbedding_of_mem` — and `δ² = 1` is an IDENTITY, hence
stable under any precomposition. Neither asks for an element of `Γ` or for
`Γ`-wide rationality.

FAITHFULNESS AUDIT of the statement as a whole: TRUE AS STATED, for an
ARBITRARY number field `F` — nothing here needs `F` totally real, Galois,
or unramified anywhere. Ramification of `F/ℚ` only SHRINKS the inertia
groups (inertia at `w` maps into, not onto, inertia at `p`), which is the
direction that preserves all four clauses. -/
theorem isHilbertHardlyRamified_map_of_isHardlyRamified
    (ℓ : ℕ) [Fact ℓ.Prime] {hℓOdd : Odd ℓ}
    (F : Type u) [Field F] [NumberField F]
    {R : Type u} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    [IsLocalRing R] [Algebra ℤ_[ℓ] R]
    (ρ : FramedGaloisRep ℚ R (Fin 2))
    (hρ : IsHardlyRamified hℓOdd (rank_finTwoPi R) ρ) :
    IsHilbertHardlyRamified ℓ F (rank_finTwoPi R) (ρ.map (algebraMap ℚ F)) where
  det g := by
    rw [GaloisRep.det_apply, GaloisRep.map_apply, ← GaloisRep.det_apply]
    exact hρ.det _
  isUnramified w hw2 hwl := by
    obtain ⟨q, hq, hqv⟩ := exists_prime_eq_ratPlace (w.under (𝓞 ℚ))
    have hqmem := natCast_mem_asIdeal_of_under_eq w hq hqv
    have hq2 : q ≠ 2 := by rintro rfl; exact hw2 hqmem
    have hql : q ≠ ℓ := by rintro rfl; exact hwl hqmem
    have hun := hρ.isUnramified q hq ⟨hq2, hql⟩
    rw [← hqv] at hun
    exact isUnramifiedAt_map_of_isUnramifiedAt_under ρ w hun
  isFlat w hw := by
    have hfl := hρ.isFlat
    rw [← under_eq_of_natCast_mem w (Fact.out : ℓ.Prime) hw] at hfl
    exact isFlatAt_map_of_isFlatAt_under ρ w hfl
  isTameAtTwo w hw := by
    obtain ⟨φ, hφcomp, hφine⟩ := exists_padicTwoEmbedding_of_mem F w hw
    obtain ⟨π, hπ, δ₀, hδ₀⟩ := hρ.isTameAtTwo
    -- the two routes `Γ F_w → Γ ℚ` differ by the single conjugator `μ`
    obtain ⟨τ, hτ⟩ := Field.absoluteGaloisGroup.exists_conj_map_comp'
      (algebraMap ℚ ℚ_[2]) φ
      ((algebraMap F (w.adicCompletion F)).comp (algebraMap ℚ F)) hφcomp
    obtain ⟨τ₀, hτ₀⟩ := Field.absoluteGaloisGroup.exists_conj_map_comp'
      (algebraMap ℚ F) (algebraMap F (w.adicCompletion F))
      ((algebraMap F (w.adicCompletion F)).comp (algebraMap ℚ F)) rfl
    obtain ⟨μ, hμ⟩ : ∃ μ : Γ ℚ, τ₀⁻¹ * τ = μ := ⟨_, rfl⟩
    have hinv : ∀ x : Fin 2 → R, (ρ μ⁻¹) ((ρ μ) x) = x := by
      intro x
      show (ρ μ⁻¹ * ρ μ) x = x
      rw [← map_mul, inv_mul_cancel, map_one]
      rfl
    refine ⟨π ∘ₗ (ρ μ⁻¹), ?_, δ₀.map φ, ?_, ?_, ?_⟩
    · intro r
      obtain ⟨x, hx⟩ := hπ r
      exact ⟨(ρ μ) x, by simpa [hinv x] using hx⟩
    · intro g x
      have hX : Field.absoluteGaloisGroup.map (algebraMap ℚ F)
          (Field.absoluteGaloisGroup.map (algebraMap F (w.adicCompletion F)) g)
          = μ * Field.absoluteGaloisGroup.map (algebraMap ℚ ℚ_[2])
              (Field.absoluteGaloisGroup.map φ g) * μ⁻¹ := by
        have h1 := hτ₀ g
        rw [hτ g] at h1
        rw [← hμ, show τ₀⁻¹ * τ * Field.absoluteGaloisGroup.map (algebraMap ℚ ℚ_[2])
              (Field.absoluteGaloisGroup.map φ g) * (τ₀⁻¹ * τ)⁻¹
            = τ₀⁻¹ * (τ * Field.absoluteGaloisGroup.map (algebraMap ℚ ℚ_[2])
              (Field.absoluteGaloisGroup.map φ g) * τ⁻¹) * τ₀ from by group, h1]
        group
      have hstep : ((ρ.map (algebraMap ℚ F)).toLocal w) g
          = ρ (μ * Field.absoluteGaloisGroup.map (algebraMap ℚ ℚ_[2])
              (Field.absoluteGaloisGroup.map φ g) * μ⁻¹) := by
        rw [GaloisRep.toLocal_apply, GaloisRep.map_apply, hX]
      show π ((ρ μ⁻¹) (((ρ.map (algebraMap ℚ F)).toLocal w) g x)) = _
      rw [hstep]
      show π ((ρ μ⁻¹ * ρ (μ * Field.absoluteGaloisGroup.map (algebraMap ℚ ℚ_[2])
        (Field.absoluteGaloisGroup.map φ g) * μ⁻¹)) x) = _
      rw [← map_mul, show μ⁻¹ * (μ * Field.absoluteGaloisGroup.map (algebraMap ℚ ℚ_[2])
          (Field.absoluteGaloisGroup.map φ g) * μ⁻¹)
        = Field.absoluteGaloisGroup.map (algebraMap ℚ ℚ_[2])
          (Field.absoluteGaloisGroup.map φ g) * μ⁻¹ from by group, map_mul]
      exact (hδ₀ (Field.absoluteGaloisGroup.map φ g) ((ρ μ⁻¹) x)).1
    · intro ι hι
      show (δ₀.map φ) ι = 1
      rw [GaloisRep.map_apply]
      exact (hδ₀ 1 0).2.1 (hφine ι hι)
    · intro g
      rw [GaloisRep.map_apply]
      exact (hδ₀ 1 0).2.2 _

/-! ### Item 2b — the `F`-level deformation ring `R_F` -/

/-- **Mazur's deformation category over `F`**: an object is a complete
Noetherian local topological `ℤ_ℓ`-algebra `R` together with a framed
`F`-level hardly ramified representation reducing to `ρbar|_{G_F}`.

This is the `F`-analogue of `HardlyRamifiedDeformation`
(`Deformation.lean`), with two shape changes, both forced by what the
consumer needs:

* the base field of the representation is `F`, and the residual datum is
  the RESTRICTION `ρbar|_{G_F} = ρbar.map (algebraMap ℚ F)`;
* the residual compatibility `resid` is stated at EVERY group element,
  not only at Frobenius elements at good primes. Over `ℚ` the two are
  equivalent (Chebotarev density plus Brauer–Nesbitt, which is
  `Deformation.lean`'s PROVEN `exists_conj_of_charFrob_eq`); stating the
  strong form here means the classifying map produced by
  `IsWeaklyUniversal` below carries charpoly information at every
  `g ∈ G_F`, which is exactly what the leaf's `∀ g ∈ H` conclusion
  needs. -/
structure HilbertDeformationDatum (ℓ : ℕ) [Fact ℓ.Prime]
    (F : Type u) [Field F] [NumberField F]
    {k : Type u} [Field k] [TopologicalSpace k]
    {V : Type v} [AddCommGroup V] [Module k V] [Module.Finite k V]
    [Module.Free k V]
    (ρbar : GaloisRep ℚ k V) where
  /-- The coefficient ring of the `F`-level deformation. -/
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
  /-- The deformation of `ρbar|_{G_F}`, framed by the standard basis. -/
  ρ : FramedGaloisRep F R (Fin 2)
  /-- The deformation satisfies the `F`-level local conditions. -/
  isHilbertHardlyRamified : IsHilbertHardlyRamified ℓ F (rank_finTwoPi R) ρ
  /-- The reduction map onto the residual coefficient field. -/
  π : R →+* k
  /-- `k` IS the residue field of `R`. -/
  π_surjective : Function.Surjective π
  /-- The deformation reduces to `ρbar|_{G_F}`, at every group element. -/
  resid : ∀ g : Γ F, ((ρ g).charpoly).map π =
    ((ρbar.map (algebraMap ℚ F)) g).charpoly

attribute [instance] HilbertDeformationDatum.commRing
  HilbertDeformationDatum.topologicalSpace
  HilbertDeformationDatum.isTopologicalRing
  HilbertDeformationDatum.isLocalRing
  HilbertDeformationDatum.algebra
  HilbertDeformationDatum.isNoetherianRing

/-- **Weak universality of an `F`-level deformation datum**: every datum
receives a `ℤ_ℓ`-algebra homomorphism from `𝒟` compatible with the
reductions and with the characteristic polynomials at every element of
`G_F`.

Only the EXISTENCE half is asked for, as in `Deformation.lean`'s
`HardlyRamifiedDeformation.IsWeaklyUniversal`: the uniqueness half is not
needed by the assembly below, which uses the classifying map and never
compares two of them. -/
def HilbertDeformationDatum.IsWeaklyUniversal {ℓ : ℕ} [Fact ℓ.Prime]
    {F : Type u} [Field F] [NumberField F]
    {k : Type u} [Field k] [TopologicalSpace k]
    {V : Type v} [AddCommGroup V] [Module k V] [Module.Finite k V]
    [Module.Free k V]
    {ρbar : GaloisRep ℚ k V} (𝒟 : HilbertDeformationDatum ℓ F ρbar) : Prop :=
  ∀ 𝒟' : HilbertDeformationDatum ℓ F ρbar,
    ∃ f : 𝒟.R →+* 𝒟'.R,
      f.comp (algebraMap ℤ_[ℓ] 𝒟.R) = algebraMap ℤ_[ℓ] 𝒟'.R ∧
      𝒟'.π.comp f = 𝒟.π ∧
      ∀ g : Γ F, ((𝒟.ρ g).charpoly).map f = (𝒟'.ρ g).charpoly

/-! #### The FAITHFULNESS REPAIR of `exists_isWeaklyUniversal_hilbertDeformationDatum`

**The statement this module was created with was FALSE, and it is refuted
mechanically by `rank_eq_two_of_hilbertDeformationDatum` just below**
(2026-07-26). It read

```
theorem exists_isWeaklyUniversal_hilbertDeformationDatum
    (ℓ : ℕ) [Fact ℓ.Prime] (F : Type u) [Field F] [NumberField F]
    {k : Type u} [Field k] [TopologicalSpace k]
    {V : Type v} [AddCommGroup V] [Module k V] [Module.Finite k V]
    [Module.Free k V] {ρbar : GaloisRep ℚ k V}
    (hirrF : (ρbar.map (algebraMap ℚ F)).IsIrreducible) :
    ∃ 𝒟 : HilbertDeformationDatum ℓ F ρbar, 𝒟.IsWeaklyUniversal
```

— with NO constraint tying `V` to the `Fin 2` of `HilbertDeformationDatum.ρ`,
and no hypothesis making the deformation category nonempty. An existential
over a category is false as soon as the category is EMPTY, and it is empty
here for two independent reasons:

* **Dimension.** `HilbertDeformationDatum.resid` asks that the charpoly of
  `𝒟.ρ g`, an endomorphism of `Fin 2 → 𝒟.R`, reduce to the charpoly of
  `ρbar|_{G_F} g`, an endomorphism of `V`. Both are monic and `𝒟.π` lands in
  a field, so `Monic.natDegree_map` forces `finrank k V = 2`. That is proven
  below. A `1`-dimensional `ρbar` — say the trivial character on `V = k` — is
  `IsIrreducible` (`IsSimpleOrder (Subrepresentation ρbar)` holds: the only
  subrepresentations of a line are `⊥ ≠ ⊤`) and satisfies `hirrF` for `F = ℚ`,
  so it meets every hypothesis of the old statement while
  `HilbertDeformationDatum ℓ ℚ ρbar` is EMPTY. That is an explicit
  counterexample.
* **Arithmetic.** Even at `finrank k V = 2` the category is empty unless
  `ρbar|_{G_F}` itself satisfies the `F`-level local conditions — `resid`
  forces `det ρbar|_{G_F}` to be the reduction of the cyclotomic character,
  and forces the whole residual eigensystem to be hardly ramified over `F`.
  For a `ρbar` ramified outside `2ℓ` no `𝒟` exists at all.

**THE REPAIR: the category is required to be nonempty, by a hypothesis
`𝒟₀ : HilbertDeformationDatum ℓ F ρbar`.** This is not a weakening dressed
up as a fix; it is the shape every representability theorem has. Mazur's
theorem produces the universal object of a deformation problem whose
residual object is GIVEN — Schlessinger's `F(k)` is a single point, not the
empty set — and here `𝒟₀` is exactly that input: it pins `finrank k V = 2`
(proven below) and it exhibits a hardly ramified `F`-level deformation of
`ρbar|_{G_F}` to reduce, so its residual frame is the ρbar-frame the machine
deforms. Nothing is lost downstream: the consumer
`exists_finiteIndex_isIntegral_charpolyCoeff_of_isHardlyRamified` at the
bottom of this module BUILDS such a datum out of its own `ρ` (that is the
`𝒟'` of its proof), so the hypothesis is discharged there for free — the
only change to the assembly is that `𝒟'` is now constructed BEFORE `R_F`
is asked for rather than after. `Deformation.lean`'s consumer of that
assembly is untouched, signature and all.

VACUITY AUDIT: the repaired statement is NOT vacuous. `𝒟₀` makes the
hypothesis-set satisfiable (the consumer satisfies it), and the conclusion
is not satisfiable by `𝒟₀` itself — weak universality is a genuine
condition on the produced `𝒟`, which is why the machine leaf below still
carries the whole Schlessinger argument. Every hypothesis of the repaired
statement is used: `𝒟₀` in the machine leaf and in the rank lemma,
`hirrF` in the residual-rigidity clause. -/

/-- **Nonemptiness of the `F`-level deformation category forces
`Module.rank k V = 2`** (PROVEN — the mechanical half of the faithfulness
repair recorded above).

The proof is the degree count of `HilbertDeformationDatum.resid` at
`g = 1`: the left-hand charpoly is that of an endomorphism of
`Fin 2 → 𝒟.R`, hence monic of degree `2`, and monic polynomials keep their
degree under a ring map into a nontrivial ring (`𝒟.π` lands in the field
`k`); the right-hand charpoly is that of an endomorphism of `V`, of degree
`finrank k V`.

Consumed by the assembly below, which feeds it to the residual-rigidity
clause; it is also the refutation of the module's original statement of
`exists_isWeaklyUniversal_hilbertDeformationDatum`, since a `1`-dimensional
irreducible `ρbar` satisfies that statement's hypotheses and this lemma
shows it can have no datum at all. -/
theorem rank_eq_two_of_hilbertDeformationDatum {ℓ : ℕ} [Fact ℓ.Prime]
    {F : Type u} [Field F] [NumberField F]
    {k : Type u} [Field k] [TopologicalSpace k]
    {V : Type v} [AddCommGroup V] [Module k V] [Module.Finite k V]
    [Module.Free k V] {ρbar : GaloisRep ℚ k V}
    (𝒟 : HilbertDeformationDatum ℓ F ρbar) :
    Module.rank k V = 2 := by
  have hres := 𝒟.resid 1
  have hL : (((𝒟.ρ 1).charpoly).map 𝒟.π).natDegree = 2 := by
    rw [(LinearMap.charpoly_monic (𝒟.ρ 1)).natDegree_map 𝒟.π,
      LinearMap.charpoly_natDegree, Module.finrank_pi]
    simp
  rw [hres, LinearMap.charpoly_natDegree] at hL
  rw [← Module.finrank_eq_rank, hL]
  norm_num

open scoped TensorProduct in
/-- **Pushforward of an `F`-framed representation along a continuous ring
homomorphism**: base change along `ψ.toAlgebra`, followed by the standard
identification `A ⊗_B (Fin 2 → B) ≅ (Fin 2 → A)` — concretely, "apply `ψ`
to the matrix entries".

This is `Deformation.lean`'s `pushforwardFrame` with the base field `ℚ`
replaced by an arbitrary number field; the two are the same definition and
neither may be replaced by the other without moving a declaration across
the import edge (the same situation as `rank_finTwoPi` above). The name
differs because `Deformation.lean` `public import`s this module into the
same namespace.

Bundled as a definition rather than written inline because the base change
needs an `Algebra B A` and a `ContinuousSMul B A` in scope, so the inline
form drags a `letI` block into every statement that mentions it. -/
noncomputable def framePushforward {F : Type u} [Field F] [NumberField F]
    {B : Type u} [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
    {A : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    (ψ : B →+* A) (hψ : Continuous ψ) (ρ : FramedGaloisRep F B (Fin 2)) :
    FramedGaloisRep F A (Fin 2) :=
  letI : Algebra B A := ψ.toAlgebra
  letI : ContinuousSMul B A := continuousSMul_of_algebraMap B A
    (by rw [RingHom.algebraMap_toAlgebra]; exact hψ)
  (ρ.baseChange A).conj (TensorProduct.piScalarRight B A A (Fin 2))

/-! #### Bookkeeping for `framePushforward`

The two lemmas below are the `F`-level copies of `Deformation.lean`'s
`pushforwardFrame_apply_map` and `det_pushforwardFrame` — same statements
and same proofs with the base field `ℚ` replaced by `F`, and, like
`rank_finTwoPi` and `framePushforward` themselves, neither may be replaced
by the other without moving a declaration across the import edge. Together
they say that `framePushforward ψ` really is "apply `ψ` to the matrix
entries": it acts entrywise on vectors already in the image of `ψ`, and its
determinant is `ψ` of the determinant. That is exactly what a fibre-product
argument needs, because it turns a statement over `B` into a pair of
statements about VALUES in `A₁` and `A₂`, and values descend along the
injection `b ↦ (p₁ b, p₂ b)`.

**IF YOU ARE ANOTHER CLAUSE OWNER AND NEED THESE, USE THEM — DO NOT ADD A
SECOND COPY.** `Deformation.lean` records what that costs: two concurrent
owners each landed a byte-identical `det_pushforwardFrame`, git merged the
disjoint regions cleanly, every source scan saw a clean file, and the
module then failed to elaborate at all with "has already been declared",
producing no `.olean` and silently blocking every downstream module. -/

open scoped TensorProduct in
/-- **`framePushforward` computed on the image of a `B`-vector** (PROVEN;
the `F`-level copy of `Deformation.lean`'s `pushforwardFrame_apply_map`).

`(1 : A) ⊗ₜ v` is a preimage of `ψ ∘ v` under
`TensorProduct.piScalarRight`, so `LinearEquiv.conj_apply_apply` moves the
conjugation out of the way and `GaloisRep.baseChange_tmul` finishes;
nothing has to be said about `piScalarRight.symm` on a general element,
which is a sum.

This is the handle that lets a fibre-product argument compare `ρ g` with
`1` ENTRYWISE, which is the shape the injectivity of `b ↦ (p₁ b, p₂ b)`
can act on. -/
lemma framePushforward_apply_map {F : Type u} [Field F] [NumberField F]
    {B : Type u} [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
    {A : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    (ψ : B →+* A) (hψ : Continuous ψ) (ρ : FramedGaloisRep F B (Fin 2))
    (g : Γ F) (v : Fin 2 → B) (i : Fin 2) :
    framePushforward ψ hψ ρ g (fun j => ψ (v j)) i = ψ (ρ g v i) := by
  letI : Algebra B A := ψ.toAlgebra
  letI : ContinuousSMul B A := continuousSMul_of_algebraMap B A
    (by rw [RingHom.algebraMap_toAlgebra]; exact hψ)
  have hsmul : ∀ (b : B) (a : A), b • a = ψ b * a := fun _ _ => rfl
  have h1 : (fun j => ψ (v j)) =
      (TensorProduct.piScalarRight B A A (Fin 2)) ((1 : A) ⊗ₜ[B] v) := by
    funext j
    rw [TensorProduct.piScalarRight_apply, TensorProduct.piScalarRightHom_tmul]
    simp [hsmul]
  show (((ρ.baseChange A).conj (TensorProduct.piScalarRight B A A (Fin 2))) g)
      (fun j => ψ (v j)) i = _
  rw [h1, GaloisRep.conj_apply, LinearEquiv.conj_apply_apply,
    LinearEquiv.symm_apply_apply, GaloisRep.baseChange_tmul,
    TensorProduct.piScalarRight_apply, TensorProduct.piScalarRightHom_tmul]
  simp [hsmul]

open scoped TensorProduct in
/-- **`det` commutes with `framePushforward`** (PROVEN; the `F`-level copy
of `Deformation.lean`'s `det_pushforwardFrame`).

`LinearMap.det_conj` absorbs the framing identification and
`LinearMap.det_baseChange` turns the base-changed determinant into
`algebraMap B A` of the original, which is `ψ` by
`RingHom.algebraMap_toAlgebra`. This is the direction that lets a
determinant identity be REFLECTED BACK from the two projections to `B`,
and equally lets the determinant clause of `isHilbertProLimitClause` be
reflected back from the levels to `R`. -/
lemma det_framePushforward {F : Type u} [Field F] [NumberField F]
    {B : Type u} [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
    {A : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    (ψ : B →+* A) (hψ : Continuous ψ) (ρ : FramedGaloisRep F B (Fin 2))
    (g : Γ F) :
    (framePushforward ψ hψ ρ).det g = ψ (ρ.det g) := by
  letI : Algebra B A := ψ.toAlgebra
  letI : ContinuousSMul B A := continuousSMul_of_algebraMap B A
    (by rw [RingHom.algebraMap_toAlgebra]; exact hψ)
  show LinearMap.det
    ((((ρ.baseChange A).conj (TensorProduct.piScalarRight B A A (Fin 2))) g)) = _
  rw [GaloisRep.conj_apply, LinearEquiv.conj_apply, LinearMap.comp_assoc,
    LinearMap.det_conj]
  show LinearMap.det (LinearMap.baseChange A (ρ g)) = _
  rw [LinearMap.det_baseChange, RingHom.algebraMap_toAlgebra]
  rfl

/-! #### The two arithmetic residues of Schlessinger's H1/H2 over `F`

`isHilbertFibreProductClause` below is PROVEN over exactly these two
leaves; the determinant and unramifiedness clauses are formal and are
discharged there. The split is `Deformation.lean`'s, one for one: over `ℚ`
the same two residues are `isFlatAt_of_fibreProduct` and
`isTameAtTwo_of_fibreProduct`, and everything else in
`isHardlyRamified_of_fibreProduct` is bookkeeping.

They are stated HERE rather than immediately above their consumer only to
keep this file's concurrently-edited regions apart; nothing in them depends
on the clause definitions below. -/

/-- **Flatness at a place over `ℓ` glues along a fibre product** (LEAF;
Ramakrishna and Raynaud — the first arithmetic residue of Schlessinger's
H1/H2 over `F`, and the `F`-level twin of `Deformation.lean`'s
`isFlatAt_of_fibreProduct`).

`B` is the fibre product `A₁ ×_{A₀} A₂` of finite local `ℤ_ℓ`-algebras
along a SURJECTION `f₂`, presented by its universal property rather than as
a construction: `hcart` says every compatible pair comes from `B`, and
`hemb` says `B` carries the induced topology and injects, so `B` really is
the fibre product AS A TOPOLOGICAL RING.

WHY IT IS NOT FORMAL, and where each hypothesis is spent.
`GaloisRep.IsFlatAt w` quantifies over the OPEN IDEALS `I` of the
coefficient ring and asks that `ρ ⊗ (B ⧸ I)` be the geometric points of a
finite flat group scheme over `𝒪_{F_w}`. The open ideals of `B` are NOT in
general pullbacks of open ideals of `A₁` and `A₂`, so `h₁` and `h₂` cannot
simply be evaluated at the ideal one is handed: one first has to shrink `I`
to an open ideal that IS a pullback, which is where finiteness of the rings
and `hemb` enter (over `ℚ` this is exactly what
`exists_isOpen_ideal_subset_of_finite` was cut out of
`isFlatAt_of_fibreProduct` to do). The gluing of the two prolongations is
then Raynaud's: over the complete DVR `𝒪_{F_w}` a finite flat group scheme
with the given generic fibre is determined by its geometric points, and a
fibre product of two such along a common quotient — this is where the
surjectivity `hf₂` is used, so that the quotient really is common — is
again finite and flat.

`hw : ℓ ∈ w` is what makes the clause meaningful: at a place not over `ℓ`
the flatness clause of `IsHilbertHardlyRamified` is not asserted at all.

FAITHFULNESS: the statement asks for the EXISTENCE of a prolongation over
`𝒪_{F_w}` produced from two given ones, not for a descent of existence from
`𝒪^nr`, so the `𝒪ᵥ` descent rule does not bite. Nothing here needs `F`
totally real or `F/ℚ` Galois.

References: Raynaud, *Schémas en groupes de type `(p,…,p)`*, Bull. SMF 102
(1974); Ramakrishna, Compositio 87 (1994), §1; Conrad–Diamond–Taylor, JAMS
12 (1999), §2. -/
theorem isHilbertFlatAt_of_fibreProduct (ℓ : ℕ) [Fact ℓ.Prime]
    (F : Type u) [Field F] [NumberField F]
    {A₀ : Type u} [CommRing A₀] [TopologicalSpace A₀] [IsTopologicalRing A₀]
    [IsLocalRing A₀] [Algebra ℤ_[ℓ] A₀] [Finite A₀]
    {A₁ : Type u} [CommRing A₁] [TopologicalSpace A₁] [IsTopologicalRing A₁]
    [IsLocalRing A₁] [Algebra ℤ_[ℓ] A₁] [Finite A₁]
    {A₂ : Type u} [CommRing A₂] [TopologicalSpace A₂] [IsTopologicalRing A₂]
    [IsLocalRing A₂] [Algebra ℤ_[ℓ] A₂] [Finite A₂]
    {B : Type u} [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
    [IsLocalRing B] [Algebra ℤ_[ℓ] B] [Finite B]
    (f₁ : A₁ →+* A₀) (f₂ : A₂ →+* A₀) (hf₂ : Function.Surjective f₂)
    (p₁ : B →+* A₁) (p₂ : B →+* A₂) (hp₁ : Continuous p₁) (hp₂ : Continuous p₂)
    (hcomm : f₁.comp p₁ = f₂.comp p₂)
    (hemb : Topology.IsEmbedding fun b : B => (p₁ b, p₂ b))
    (hcart : ∀ (a₁ : A₁) (a₂ : A₂), f₁ a₁ = f₂ a₂ → ∃ b : B, p₁ b = a₁ ∧ p₂ b = a₂)
    {ρ : FramedGaloisRep F B (Fin 2)}
    (w : HeightOneSpectrum (𝓞 F)) (hw : ((ℓ : ℕ) : 𝓞 F) ∈ w.asIdeal)
    (h₁ : (framePushforward p₁ hp₁ ρ).IsFlatAt w)
    (h₂ : (framePushforward p₂ hp₂ ρ).IsFlatAt w) :
    ρ.IsFlatAt w :=
  sorry

/-- **The tame quadratic quotient at a place over `2` glues along a fibre
product** (LEAF; Conrad–Diamond–Taylor — the second arithmetic residue of
Schlessinger's H1/H2 over `F`, and the `F`-level twin of
`Deformation.lean`'s `isTameAtTwo_of_fibreProduct`).

**THIS STATEMENT CARRIES `hℓ5 : 5 ≤ ℓ`, AND MUST — see the faithfulness
note on `isHilbertFibreProductClause` below.** The `ℓ = 3` case is not
merely open: the `ℚ`-level twin's `ℓ = 3` case was REFUTED on 2026-07-26
with an explicit counterexample, recorded in full in the block comment
above `isTameAtTwo_of_fibreProduct` in `Deformation.lean`, and that
counterexample is a counterexample HERE TOO at `F = ℚ`, because
`IsHilbertHardlyRamified ℓ ℚ` is the `ℚ`-level condition place by place.
Do not drop `hℓ5`, and do not restate this leaf without it.

WHY IT IS NOT FORMAL. The tame clause is an EXISTENTIAL — SOME surjection
`p` and SOME unramified quadratic `δ`. So `h₁` and `h₂` hand you a line
over `A₁` and a line over `A₂` with no compatibility whatever over `A₀`,
while a line over the fibre product is exactly a compatible PAIR of lines.
Everything turns on a uniqueness statement forcing the two given choices to
agree over `A₀`, and that uniqueness is what `hdet` and `hℓ5` buy:

* `χ_ℓ` is unramified on `G_{F_w}` with `χ_ℓ(Frob_w) = 2^{f(w|2)}`, because
  `ℓ` is odd, so the residual representation restricted to `G_{F_w}` is
  never scalar and its two Jordan–Hölder characters `χ̄δ̄` and `δ̄` differ by
  `χ̄|_{G_w}`;
* those two characters can COINCIDE as candidates for the clause only when
  `χ̄²|_{G_w} = 1`, i.e. when `2^{2f} ≡ 1 mod ℓ`; at `ℓ = 3` that holds for
  every `w | 2` and every `F`, which is exactly the degeneracy the `ℚ`-level
  counterexample exploits, and at `ℓ ≥ 5` the argument of the `ℚ`-level
  proof — the two surjections are unimodular rows that are left
  eigenvectors of `ρ(Frob_w)`, and `det − d₁d₂` is a unit — forces them
  proportional over `A₀`, after which `hf₂` rescales one of them and
  `hcart` glues them entrywise.

FAITHFULNESS: as over `ℚ`, the two nontrivial conditions on the glued `δ`
are an inertia-only containment and an IDENTITY of values, both on the true
side of the `𝒪ᵥ` descent rule; no element of `Γ` and no `Γ`-wide
rationality is demanded.

References: Conrad–Diamond–Taylor, JAMS 12 (1999), §2; Mazur, *Deforming
Galois representations*, MSRI Publ. 16 (1989), §§18–23; Schlessinger,
Trans. AMS 130 (1968), Thm. 2.11. -/
theorem isHilbertTameAtTwo_of_fibreProduct (ℓ : ℕ) [Fact ℓ.Prime] (hℓ5 : 5 ≤ ℓ)
    (F : Type u) [Field F] [NumberField F]
    {A₀ : Type u} [CommRing A₀] [TopologicalSpace A₀] [IsTopologicalRing A₀]
    [IsLocalRing A₀] [Algebra ℤ_[ℓ] A₀] [Finite A₀]
    {A₁ : Type u} [CommRing A₁] [TopologicalSpace A₁] [IsTopologicalRing A₁]
    [IsLocalRing A₁] [Algebra ℤ_[ℓ] A₁] [Finite A₁]
    {A₂ : Type u} [CommRing A₂] [TopologicalSpace A₂] [IsTopologicalRing A₂]
    [IsLocalRing A₂] [Algebra ℤ_[ℓ] A₂] [Finite A₂]
    {B : Type u} [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
    [IsLocalRing B] [Algebra ℤ_[ℓ] B] [Finite B]
    (f₁ : A₁ →+* A₀) (f₂ : A₂ →+* A₀) (hf₂ : Function.Surjective f₂)
    (p₁ : B →+* A₁) (p₂ : B →+* A₂) (hp₁ : Continuous p₁) (hp₂ : Continuous p₂)
    (hcomm : f₁.comp p₁ = f₂.comp p₂)
    (hemb : Topology.IsEmbedding fun b : B => (p₁ b, p₂ b))
    (hcart : ∀ (a₁ : A₁) (a₂ : A₂), f₁ a₁ = f₂ a₂ → ∃ b : B, p₁ b = a₁ ∧ p₂ b = a₂)
    {ρ : FramedGaloisRep F B (Fin 2)}
    (hdet : ∀ g : Γ F, ρ.det g = algebraMap ℤ_[ℓ] B
      (cyclotomicCharacter (ℚ ᵃˡᵍ) ℓ
        (Field.absoluteGaloisGroup.map (algebraMap ℚ F) g).toRingEquiv))
    (w : HeightOneSpectrum (𝓞 F)) (hw : ((2 : ℕ) : 𝓞 F) ∈ w.asIdeal)
    (h₁ : ∃ (p : (Fin 2 → A₁) →ₗ[A₁] A₁) (_ : Function.Surjective p)
      (δ : GaloisRep (w.adicCompletion F) A₁ A₁),
      (∀ g : Γ (w.adicCompletion F), ∀ v : Fin 2 → A₁,
        p ((framePushforward p₁ hp₁ ρ).toLocal w g v) = δ g (p v)) ∧
      localInertiaGroup w ≤ δ.ker ∧
      ∀ g : Γ (w.adicCompletion F), δ g * δ g = 1)
    (h₂ : ∃ (p : (Fin 2 → A₂) →ₗ[A₂] A₂) (_ : Function.Surjective p)
      (δ : GaloisRep (w.adicCompletion F) A₂ A₂),
      (∀ g : Γ (w.adicCompletion F), ∀ v : Fin 2 → A₂,
        p ((framePushforward p₂ hp₂ ρ).toLocal w g v) = δ g (p v)) ∧
      localInertiaGroup w ≤ δ.ker ∧
      ∀ g : Γ (w.adicCompletion F), δ g * δ g = 1) :
    ∃ (p : (Fin 2 → B) →ₗ[B] B) (_ : Function.Surjective p)
      (δ : GaloisRep (w.adicCompletion F) B B),
      (∀ g : Γ (w.adicCompletion F), ∀ v : Fin 2 → B,
        p (ρ.toLocal w g v) = δ g (p v)) ∧
      localInertiaGroup w ≤ δ.ker ∧
      ∀ g : Γ (w.adicCompletion F), δ g * δ g = 1 :=
  sorry

/-! #### The four deformation-condition clauses over `F`, and residual rigidity

The cut of `exists_isWeaklyUniversal_hilbertDeformationDatum` below follows
`Deformation.lean`'s cut of
`exists_isStrictlyUniversalOnFrames_of_deformationCondition` one for one:
the Schlessinger machine is separated from the ARITHMETIC of the local
conditions, which enters it only through the four clauses that say
`IsHilbertHardlyRamified` is a deformation condition in Mazur's sense —
functoriality, gluing along fibre products, finiteness at every finite
level, and detection on the finite levels — plus the residual rigidity that
identifies an object's residual frame with `ρbar|_{G_F}`.

Each clause is written ONCE, as a `Prop`-valued definition, so that the
machine leaf can take it as a hypothesis and the assembly can discharge
that hypothesis by naming the corresponding leaf, with no binder
bookkeeping in between. This is deliberate: the `ℚ`-level twin spells the
same five statements out twice, and the duplicated binder lists are what
conflicted on five consecutive integrations there. -/

/-- **Functoriality clause** (`hbase` of the `ℚ`-level twin): the `F`-level
hardly ramified condition is stable under pushforward along a continuous
`ℤ_ℓ`-algebra map into a FINITE local ring. -/
def IsHilbertBaseChangeClause (ℓ : ℕ) [Fact ℓ.Prime]
    (F : Type u) [Field F] [NumberField F] : Prop :=
  ∀ {B : Type u} [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
    [IsLocalRing B] [Algebra ℤ_[ℓ] B]
    {A : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [IsLocalRing A] [Finite A] [Algebra ℤ_[ℓ] A]
    (ψ : B →+* A) (hψ : Continuous ψ),
    ψ.comp (algebraMap ℤ_[ℓ] B) = algebraMap ℤ_[ℓ] A →
    ∀ {ρ : FramedGaloisRep F B (Fin 2)},
    IsHilbertHardlyRamified ℓ F (rank_finTwoPi B) ρ →
    IsHilbertHardlyRamified ℓ F (rank_finTwoPi A) (framePushforward ψ hψ ρ)

/-- **Fibre-product clause** (`hglue` of the `ℚ`-level twin; Schlessinger's
H1 and H2): a framed representation over a fibre product of finite local
rings is hardly ramified over `F` as soon as both of its projections
are. -/
def IsHilbertFibreProductClause (ℓ : ℕ) [Fact ℓ.Prime]
    (F : Type u) [Field F] [NumberField F] : Prop :=
  ∀ {A₀ : Type u} [CommRing A₀] [TopologicalSpace A₀]
    [IsTopologicalRing A₀] [IsLocalRing A₀] [Algebra ℤ_[ℓ] A₀] [Finite A₀]
    {A₁ : Type u} [CommRing A₁] [TopologicalSpace A₁] [IsTopologicalRing A₁]
    [IsLocalRing A₁] [Algebra ℤ_[ℓ] A₁] [Finite A₁]
    {A₂ : Type u} [CommRing A₂] [TopologicalSpace A₂] [IsTopologicalRing A₂]
    [IsLocalRing A₂] [Algebra ℤ_[ℓ] A₂] [Finite A₂]
    {B : Type u} [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
    [IsLocalRing B] [Algebra ℤ_[ℓ] B] [Finite B]
    (f₁ : A₁ →+* A₀) (f₂ : A₂ →+* A₀), Function.Surjective f₂ →
    ∀ (p₁ : B →+* A₁) (p₂ : B →+* A₂) (hp₁ : Continuous p₁)
      (hp₂ : Continuous p₂),
    p₁.comp (algebraMap ℤ_[ℓ] B) = algebraMap ℤ_[ℓ] A₁ →
    p₂.comp (algebraMap ℤ_[ℓ] B) = algebraMap ℤ_[ℓ] A₂ →
    f₁.comp p₁ = f₂.comp p₂ →
    Topology.IsEmbedding (fun b : B => (p₁ b, p₂ b)) →
    (∀ (a₁ : A₁) (a₂ : A₂), f₁ a₁ = f₂ a₂ → ∃ b : B, p₁ b = a₁ ∧ p₂ b = a₂) →
    ∀ {ρ : FramedGaloisRep F B (Fin 2)},
    IsHilbertHardlyRamified ℓ F (rank_finTwoPi A₁) (framePushforward p₁ hp₁ ρ) →
    IsHilbertHardlyRamified ℓ F (rank_finTwoPi A₂) (framePushforward p₂ hp₂ ρ) →
    IsHilbertHardlyRamified ℓ F (rank_finTwoPi B) ρ

/-- **Finiteness clause** (`hfin` of the `ℚ`-level twin; Schlessinger's H3):
over a finite discrete local `ℤ_ℓ`-algebra there are only finitely many
`F`-level hardly ramified frames. Classically this is the finiteness of the
set of extensions of bounded ramification, i.e. Hermite–Minkowski for `F`
together with the finiteness of the set of places of `F` above `2ℓ`. -/
def IsHilbertFiniteFramesClause (ℓ : ℕ) [Fact ℓ.Prime]
    (F : Type u) [Field F] [NumberField F] : Prop :=
  ∀ (A : Type u) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [IsLocalRing A] [Algebra ℤ_[ℓ] A] [Finite A] [DiscreteTopology A],
    {ρ : FramedGaloisRep F A (Fin 2) |
      IsHilbertHardlyRamified ℓ F (rank_finTwoPi A) ρ}.Finite

/-- **Pro-limit clause** (`hlim` of the `ℚ`-level twin): the `F`-level
hardly ramified condition is DETECTED on the finite levels of a complete
Noetherian local coefficient ring. This is what upgrades the compatible
system of Artinian truncations produced by the Schlessinger machine to a
representation over the limit ring itself. -/
def IsHilbertProLimitClause (ℓ : ℕ) [Fact ℓ.Prime]
    (F : Type u) [Field F] [NumberField F] : Prop :=
  ∀ {R : Type u} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    [IsLocalRing R] [Algebra ℤ_[ℓ] R] [IsNoetherianRing R],
    IsAdic (IsLocalRing.maximalIdeal R) →
    IsAdicComplete (IsLocalRing.maximalIdeal R) R →
    ∀ {ρ : FramedGaloisRep F R (Fin 2)},
    (∀ (I : Ideal R), IsOpen (I : Set R) → ∀ [IsLocalRing (R ⧸ I)]
      (hmk : Continuous (Ideal.Quotient.mk I)),
      IsHilbertHardlyRamified ℓ F (rank_finTwoPi (R ⧸ I))
        (framePushforward (Ideal.Quotient.mk I) hmk ρ)) →
    IsHilbertHardlyRamified ℓ F (rank_finTwoPi R) ρ

/-- **Residual rigidity clause over `F`** (Brauer–Nesbitt): a framed
representation of `G_F` over `k` whose characteristic polynomials agree with
those of the IRREDUCIBLE `ρbar|_{G_F}` at EVERY group element is conjugate
to it.

This is the `F`-level analogue of `Deformation.lean`'s PROVEN
`exists_conj_of_charFrob_eq`, and it is strictly EASIER: the `ℚ`-level
statement is given the charpolys only at Frobenius elements at good primes
and must run Chebotarev density first, whereas here `HilbertDeformationDatum.resid`
already supplies them at every `g ∈ G_F`, so only Brauer–Nesbitt itself is
needed (equal characteristic polynomials ⟹ isomorphic semisimplifications;
the semisimplification of `ρbar|_{G_F}` is itself, being irreducible; a
`2`-dimensional representation whose semisimplification is irreducible is
irreducible, hence equal to it).

It is what lets the machine leaf classify an ARBITRARY object of the
category: `HilbertDeformationDatum` pins the residual frame only up to
charpolys, so an object's residual frame must first be conjugated onto the
frame the universal object deforms — and conjugation is invisible to the
conclusion of `IsWeaklyUniversal`, which speaks only of charpolys. -/
def IsHilbertResidualRigidityClause (F : Type u) [Field F] [NumberField F]
    {k : Type u} [Field k] [TopologicalSpace k]
    {V : Type v} [AddCommGroup V] [Module k V] [Module.Finite k V]
    [Module.Free k V] (ρbar : GaloisRep ℚ k V) : Prop :=
  Module.rank k V = 2 →
  (ρbar.map (algebraMap ℚ F)).IsIrreducible →
  ∀ τ : FramedGaloisRep F k (Fin 2),
    (∀ g : Γ F, (τ g).charpoly = ((ρbar.map (algebraMap ℚ F)) g).charpoly) →
    ∃ e : (Fin 2 → k) ≃ₗ[k] V, τ.conj e = ρbar.map (algebraMap ℚ F)

/-! #### The functoriality clause, and the base-field hoist it needed

`isHilbertBaseChangeClause` is now PROVEN (2026-07-26), over the single
leaf `hasFlatProlongationAt_of_pi_surjection_of_numberField` below. The
cut is `Deformation.lean`'s `ℚ`-level cut of
`isHardlyRamified_pushforwardFrame`, one for one:

* `isHilbertTameAtTwo_baseChange` — the tame quadratic quotient at a place
  over `2` base-changes (PROVEN, the `ℚ`-level `isTameAtTwo_baseChange`
  transcribed with `toLocal w` in place of `map (algebraMap ℚ ℚ_[2])`);
* `isFlatAt_baseChange_of_numberField` — the flatness transfer, PROVEN
  over the Raynaud leaf by the same explicit equivariant surjection out
  of a finite power;
* `isHilbertHardlyRamified_conj` and `isHilbertHardlyRamified_baseChange`
  — conjugation invariance and base change of the whole four-clause
  condition (PROVEN);
* `isHilbertBaseChangeClause` — the composite, since
  `framePushforward = conj ∘ baseChange` by definition.

The observation that made this cheap: `GaloisRep.HasFlatProlongationAt`,
`GaloisRep.IsFlatAt`, `GaloisRep.toLocal` and the base-change instance for
`GaloisRep.IsUnramifiedAt` are ALREADY stated over a variable number field
in `Deformations/RepresentationTheory/GaloisRep.lean`. The `ℚ` in
`Deformation.lean`'s versions of these transfers is incidental — it comes
from the place being written as
`Nat.Prime.toHeightOneSpectrumRingOfIntegersRat`, not from anything in the
argument. So only ONE statement in the chain is genuinely `ℚ`-bound, and
it is the Raynaud closure. -/

/-- **Raynaud closure for flat prolongations over a VARIABLE number field,
in surjection-from-a-finite-power form** (LEAF, new 2026-07-26): if the
local space of `ρ₁` at a place `w` of `K` is the geometric-point group of a
finite flat group scheme over `𝒪_w`, then so is every `Γ K_w`-equivariant
additive QUOTIENT of a finite POWER of it.

Mathematically this is the statement that the essential image of the
generic-fibre functor (finite flat group schemes over the DVR `𝒪_w`) ⟶
(finite `Γ K_w`-modules) is closed under finite products and under
equivariant quotients: products are represented by the tensor product of
the Hopf algebras, and quotients come from the schematic-closure
construction — an equivariant surjection of point groups is induced by a
surjection of the finite étale generic-fibre Hopf algebras, and the image
of a Hopf order under a surjective bialgebra map is again a Hopf order.
The EXISTENCE direction used here needs no `e < ℓ − 1` bound; Raynaud's
bound enters only for UNIQUENESS of the prolongation, which is not
asserted.

**WHY THIS IS OPEN HERE WHEN IT IS PROVEN AT `K = ℚ`, AND EXACTLY WHAT
CLOSES IT.** At `K = ℚ` this is `Deformation.lean`'s PROVEN
`hasFlatProlongationAt_of_pi_surjection`, which lives DOWNSTREAM of this
module and so is unreachable from here. That proof is four lines: it
passes to the representation-free carrier
`GaloisRepresentation.Modularity.IsFlatPointsGroupAt` and applies
`IsFlatPointsGroupAt.pi` and `IsFlatPointsGroupAt.of_surjective`, both
PROVEN, in `Deformations/RepresentationTheory/FlatPointsGroup.lean`.

That whole file — 1950 sorry-free lines — mentions `ℚ` exactly EIGHT
times, all of them inside `variable (v : HeightOneSpectrum (𝓞 ℚ))` and the
four `local notation`s `Kᵥ`/`𝒪ᵥ`/`Γᵥ`/`Ωᵥ` derived from it, plus one
`CharZero (adicCompletion ℚ v)` instance step. Nothing in its mathematics
is about `ℚ`: every argument is about the local field `K_w` and the DVR
`𝒪_w`. So the honest way to close THIS leaf is to hoist that `variable`
line to a general `(K : Type u) [Field K] [NumberField K]`, after which the
`ℚ` statement becomes an instance of the general one and BOTH leaves close
together — a strictly copy-count-reducing change.

It was not done in this task because it is a cross-cutting edit to a file
with several concurrent owners, and because consuming
`FlatPointsGroup.lean` from here would pull
`KnownIn1980s/EllipticCurves/Flat.lean` (the Gelfand-duality machinery,
itself over the division-polynomial cone) into this module's deliberately
minimal import surface — which is what lets `Deformation.lean`
`public import` this module without touching the circularity guard. The
right sequencing is: hoist `FlatPointsGroup.lean` first, then decide where
the shared statement lives.

FAITHFULNESS: the hypotheses are exactly those of the `ℚ`-level theorem
with `ℚ` replaced by `K`, and the conclusion asks only for EXISTENCE of a
prolongation upstairs produced by a product-then-quotient construction —
not for a descent of existence from `𝒪^nr`, so the `𝒪ᵥ` discriminating
rule does not bite.

References: Raynaud, *Schémas en groupes de type `(p,…,p)`*, Bull. SMF 102
(1974), §3; Tate–Oort, *A classification of group schemes of order p*,
Ann. Sci. ÉNS 3 (1970). -/
theorem hasFlatProlongationAt_of_pi_surjection_of_numberField
    {K : Type u} [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K))
    {A₁ : Type*} [CommRing A₁] [TopologicalSpace A₁]
    {M₁ : Type*} [AddCommGroup M₁] [Module A₁ M₁]
    {A₂ : Type*} [CommRing A₂] [TopologicalSpace A₂]
    {M₂ : Type*} [AddCommGroup M₂] [Module A₂ M₂]
    {ρ₁ : GaloisRep K A₁ M₁} {ρ₂ : GaloisRep K A₂ M₂} (n : ℕ)
    (h : ρ₁.HasFlatProlongationAt w)
    (π : (Fin n → (ρ₁.toLocal w).Space) →+ (ρ₂.toLocal w).Space)
    (hsurj : Function.Surjective π)
    (hequiv : ∀ (g : Γ (w.adicCompletion K))
        (x : Fin n → (ρ₁.toLocal w).Space), π (g • x) = g • π x) :
    ρ₂.HasFlatProlongationAt w :=
  sorry

set_option backward.isDefEq.respectTransparency false in
open scoped TensorProduct in
/-- **Flatness at a place transfers along an arbitrary base change to a
FINITE coefficient algebra, over a VARIABLE number field** (PROVEN
2026-07-26 over the Raynaud leaf above; the `K = ℚ` case is
`Deformation.lean`'s `isFlatAt_baseChange`, whose proof this is verbatim
with the place left variable).

Route. Let `I` be an open ideal of `B` and put `J := (algebraMap R B)⁻¹ I`,
an open ideal of `R` because the structure map is continuous
(`ContinuousSMul R B`, whence `continuous_algebraMap`). `hflat` supplies a
finite flat prolongation of `(R ⧸ J) ⊗_R M`, and what remains is that the
prolongation survives the COEFFICIENT EXTENSION `R ⧸ J → B ⧸ I` of finite
rings. That is done as an explicit equivariant SURJECTION rather than a
second tensor cancellation, which is what keeps the cut shallow: `B ⧸ I` is
finite, so enumerating it as `b₀, …, b_{n−1}` gives an additive surjection
`(Fin n → (R ⧸ J) ⊗_R M) ↠ (B ⧸ I) ⊗_R M`, `(xᵢ) ↦ Σᵢ bᵢ • ι(xᵢ)`, where
`ι` is `id ⊗ (R ⧸ J → B ⧸ I)`; surjectivity holds already on the generators
`c ⊗ m = b_{e(c)} • (1 ⊗ m)`, and `Γ K_w`-equivariance holds because the
Galois action lives on the `M`-factor while both `bᵢ • −` and `ι` act on the
coefficient factor. Composing with the inverse of
`TensorProduct.AlgebraTensorModule.cancelBaseChange` — which identifies
`(B ⧸ I) ⊗_B (B ⊗_R M)`, the space the goal actually names, with
`(B ⧸ I) ⊗_R M` — this is exactly the Raynaud leaf's hypothesis. The route
needs NO `(R ⧸ J)`-algebra structure on `B ⧸ I`, and in particular neither
`IsScalarTower R (R ⧸ J) (B ⧸ I)` nor `ContinuousSMul (R ⧸ J) (B ⧸ I)`,
neither of which is available as an instance.

`[Finite B]` is part of the statement and not a convenience: a finite flat
`𝒪_w`-algebra has only finitely many geometric points, so
`HasFlatProlongationAt` forces the space to be finite, and the unrestricted
form is FALSE (see the `ℚ`-level docstring for the counterexample). Every
consumer lives in the Artinian category, so the restriction costs nothing.

References: Ramakrishna, *On a variation of Mazur's deformation functor*,
Compositio 87 (1994), §1; Conrad–Diamond–Taylor, JAMS 12 (1999), §2. -/
theorem isFlatAt_baseChange_of_numberField
    {K : Type u} [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K))
    {R : Type*} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    [IsLocalRing R]
    {M : Type*} [AddCommGroup M] [Module R M] [Module.Finite R M]
    [Module.Free R M]
    (B : Type*) [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
    [IsLocalRing B] [Finite B] [Algebra R B] [ContinuousSMul R B]
    {ρ : GaloisRep K R M} (hflat : ρ.IsFlatAt w) :
    (ρ.baseChange B).IsFlatAt w := by
  classical
  constructor
  intro I hI
  -- the contracted open ideal of `R`
  set J : Ideal R := I.comap (algebraMap R B)
  have hJopen : IsOpen (J : Set R) := hI.preimage (continuous_algebraMap R B)
  have hflatJ : (ρ.baseChange (R ⧸ J)).HasFlatProlongationAt w :=
    hflat.cond J hJopen
  -- an enumeration of the finite ring `B ⧸ I`
  haveI : Finite (B ⧸ I) := Finite.of_surjective _ Ideal.Quotient.mk_surjective
  obtain ⟨n, ⟨enum⟩⟩ := Finite.exists_equiv_fin (B ⧸ I)
  -- the coefficient map `R ⧸ J → B ⧸ I`, `R`-linearly
  let cmap : (R ⧸ J) →ₗ[R] (B ⧸ I) :=
    Submodule.liftQ J (Algebra.linearMap R (B ⧸ I)) (by
      intro r hr
      show algebraMap R (B ⧸ I) r = 0
      rw [IsScalarTower.algebraMap_apply R B (B ⧸ I)]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr hr)
  have hcmap : ∀ r : R, cmap (Ideal.Quotient.mk J r) = algebraMap R (B ⧸ I) r :=
    fun _ => rfl
  let ι : ((R ⧸ J) ⊗[R] M) →ₗ[R] ((B ⧸ I) ⊗[R] M) := LinearMap.rTensor M cmap
  let can := TensorProduct.AlgebraTensorModule.cancelBaseChange R B (B ⧸ I) (B ⧸ I) M
  -- the equivariant surjection out of a finite power of `(R ⧸ J) ⊗ M`
  let π₀ : (Fin n → ((R ⧸ J) ⊗[R] M)) →+ ((B ⧸ I) ⊗[R] M) :=
    { toFun := fun x => ∑ i, (enum.symm i) • ι (x i)
      map_zero' := by simp
      map_add' := fun x y => by simp [smul_add, Finset.sum_add_distrib] }
  let π : (Fin n → ((ρ.baseChange (R ⧸ J)).toLocal w).Space) →+
      (((ρ.baseChange B).baseChange (B ⧸ I)).toLocal w).Space :=
    (can.symm.toAddEquiv.toAddMonoidHom).comp π₀
  refine hasFlatProlongationAt_of_pi_surjection_of_numberField w n hflatJ π ?_ ?_
  · -- surjectivity: already on the generators `c ⊗ m = b_{e c} • (1 ⊗ m)`
    have hsurj0 : Function.Surjective π₀ := by
      intro z
      induction z using TensorProduct.induction_on with
      | zero => exact ⟨0, map_zero _⟩
      | tmul c m =>
        refine ⟨(Pi.single (enum c) ((1 : R ⧸ J) ⊗ₜ[R] m) :
          Fin n → ((R ⧸ J) ⊗[R] M)), ?_⟩
        show ∑ i, (enum.symm i) • ι ((Pi.single (enum c) ((1 : R ⧸ J) ⊗ₜ[R] m) :
          Fin n → ((R ⧸ J) ⊗[R] M)) i) = c ⊗ₜ[R] m
        rw [Finset.sum_eq_single_of_mem (enum c) (Finset.mem_univ _)]
        · rw [Pi.single_eq_same]
          show (enum.symm (enum c)) • (cmap 1 ⊗ₜ[R] m) = c ⊗ₜ[R] m
          rw [Equiv.symm_apply_apply,
            show cmap 1 = 1 from (hcmap 1).trans (map_one _)]
          rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
        · intro i _ hne
          rw [Pi.single_eq_of_ne hne]
          simp
      | add a b ha hb =>
        obtain ⟨u, hu⟩ := ha
        obtain ⟨t, ht⟩ := hb
        exact ⟨u + t, by rw [map_add, hu, ht]⟩
    exact can.symm.surjective.comp hsurj0
  · -- `Γ K_w`-equivariance: the action is on the `M`-factor throughout
    intro g x
    have key : ∀ (i : Fin n) (y : (R ⧸ J) ⊗[R] M),
        can.symm ((enum.symm i) • ι (((ρ.baseChange (R ⧸ J)).toLocal w) g y))
          = (((ρ.baseChange B).baseChange (B ⧸ I)).toLocal w) g
              (can.symm ((enum.symm i) • ι y)) := by
      intro i y
      induction y using TensorProduct.induction_on with
      | zero => simp
      | add a b ha hb => simp only [map_add, smul_add, ha, hb]
      | tmul a m => rfl
    show can.symm (∑ i, (enum.symm i) • ι (((ρ.baseChange (R ⧸ J)).toLocal w) g (x i)))
        = (((ρ.baseChange B).baseChange (B ⧸ I)).toLocal w) g
            (can.symm (∑ i, (enum.symm i) • ι (x i)))
    rw [map_sum, map_sum, map_sum]
    exact Finset.sum_congr rfl fun i _ => key i (x i)

set_option backward.isDefEq.respectTransparency false in
open scoped TensorProduct in
/-- **Tameness at a place over `2` transfers along base change** (PROVEN
2026-07-26): the rank-one tame quadratic quotient `(p, δ)` of `ρ` at `w`
base-changes to `(rid ∘ (p ⊗ 1), (δ ⊗ 1)ᵉ)` for `ρ ⊗ B`.

This is `Deformation.lean`'s `isTameAtTwo_baseChange` with the local
representation spelled `ρ.toLocal w` — the restriction along
`Γ F_w → Γ F` — instead of `ρ.map (algebraMap ℚ ℚ_[2])`, and with the
inertia subgroup spelled `localInertiaGroup w` instead of the bespoke
`Z2bar` one. Nothing else changes: the equivariance is checked on simple
tensors, the kernel of a character only GROWS under base change followed by
conjugation, and `δ² = 1` is an identity transported through a monoid
homomorphism. -/
lemma isHilbertTameAtTwo_baseChange {F : Type u} [Field F] [NumberField F]
    {R : Type*} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    {M : Type*} [AddCommGroup M] [Module R M] [Module.Finite R M]
    [Module.Free R M]
    (B : Type*) [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
    [Algebra R B] [ContinuousSMul R B]
    (w : HeightOneSpectrum (𝓞 F)) {ρ : GaloisRep F R M}
    (htame : ∃ (p : M →ₗ[R] R) (_ : Function.Surjective p)
      (δ : GaloisRep (w.adicCompletion F) R R),
      (∀ g : Γ (w.adicCompletion F), ∀ x : M, p (ρ.toLocal w g x) = δ g (p x)) ∧
      localInertiaGroup w ≤ δ.ker ∧
      ∀ g : Γ (w.adicCompletion F), δ g * δ g = 1) :
    ∃ (p : (B ⊗[R] M) →ₗ[B] B) (_ : Function.Surjective p)
      (δ : GaloisRep (w.adicCompletion F) B B),
      (∀ g : Γ (w.adicCompletion F), ∀ x : B ⊗[R] M,
        p ((ρ.baseChange B).toLocal w g x) = δ g (p x)) ∧
      localInertiaGroup w ≤ δ.ker ∧
      ∀ g : Γ (w.adicCompletion F), δ g * δ g = 1 := by
  obtain ⟨p, hpsurj, δ, h⟩ := htame
  -- the canonical identification `B ⊗[R] R ≃ₗ[B] B`
  let e : (B ⊗[R] R) ≃ₗ[B] B := TensorProduct.AlgebraTensorModule.rid R B B
  refine ⟨e.toLinearMap ∘ₗ LinearMap.baseChange B p, ?_,
    (δ.baseChange B).conj e, ?_, ?_, ?_⟩
  · -- surjectivity: hit `c` with `c ⊗ v₀` for a preimage `v₀` of `1`
    intro c
    obtain ⟨v₀, hv₀⟩ := hpsurj 1
    refine ⟨c ⊗ₜ v₀, ?_⟩
    simp [e, LinearMap.baseChange_tmul, hv₀,
      TensorProduct.AlgebraTensorModule.rid_tmul]
  · -- equivariance, by linearity on simple tensors
    intro g y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul c x =>
      have h1 := h.1 g x
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
      rw [show ((ρ.baseChange B).toLocal w) g (c ⊗ₜ x) =
        c ⊗ₜ ((ρ.toLocal w) g x) from rfl,
        LinearMap.baseChange_tmul, h1,
        GaloisRep.conj_apply, LinearMap.baseChange_tmul]
      rw [LinearEquiv.conj_apply, LinearMap.comp_apply, LinearMap.comp_apply,
        LinearEquiv.coe_coe, LinearEquiv.coe_coe,
        TensorProduct.AlgebraTensorModule.rid_symm_apply,
        show ((δ.baseChange B) g : Module.End B (B ⊗[R] R)) =
          LinearMap.baseChange B (δ g) from rfl,
        LinearMap.baseChange_tmul,
        TensorProduct.AlgebraTensorModule.rid_tmul]
      rw [show (δ g) (p x) = p x • (δ g) 1 from by
        conv_lhs => rw [show (p x : R) = p x • (1 : R) from by
          rw [smul_eq_mul, mul_one]]
        rw [map_smul]]
      simp [e, TensorProduct.AlgebraTensorModule.rid_tmul, smul_smul,
        mul_comm]
    | add x y hx hy =>
      simp only [map_add, hx, hy]
  · -- unramifiedness: the kernel only grows under base change + conj
    intro σ hσ
    have hδσ : δ σ = 1 := h.2.1 hσ
    show (δ.baseChange B).conj e σ = 1
    rw [GaloisRep.conj_apply]
    rw [show (δ.baseChange B) σ = LinearMap.baseChange B (δ σ) from rfl, hδσ]
    refine LinearMap.ext fun c => ?_
    simp
  · -- the quadratic condition transfers through the monoid hom
    intro g'
    have hsq : δ g' * δ g' = 1 := h.2.2 g'
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
/-- **The `F`-level condition is invariant under an isomorphism of the
representation space** (PROVEN 2026-07-26; the `F`-analogue of
`Deformation.lean`'s `isHardlyRamified_conj`).

The determinant is conjugation-invariant, the kernels of the local
representations only grow, flatness transports through
`HasFlatProlongationAt.of_equiv` along the base-changed isomorphism at
EVERY place `w ∣ ℓ`, and the tame quadratic quotient at every `w ∣ 2` is
composed with the inverse isomorphism. -/
lemma isHilbertHardlyRamified_conj (ℓ : ℕ) [Fact ℓ.Prime]
    (F : Type u) [Field F] [NumberField F]
    {R : Type*} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    [IsLocalRing R] [Algebra ℤ_[ℓ] R]
    {M : Type*} [AddCommGroup M] [Module R M] [Module.Finite R M]
    [Module.Free R M]
    {N : Type*} [AddCommGroup N] [Module R N] [Module.Finite R N]
    [Module.Free R N]
    {hdimM : Module.rank R M = 2} (hdimN : Module.rank R N = 2)
    {ρ : GaloisRep F R M} (h : IsHilbertHardlyRamified ℓ F hdimM ρ)
    (e : M ≃ₗ[R] N) :
    IsHilbertHardlyRamified ℓ F hdimN (ρ.conj e) := by
  constructor
  · -- determinant: conjugation-invariant
    intro g
    rw [GaloisRep.det_apply, GaloisRep.conj_apply, LinearEquiv.conj_apply,
      LinearMap.comp_assoc, LinearMap.det_conj]
    exact h.det g
  · -- unramifiedness: the kernel of the local representation only grows
    intro w hw2 hwl
    have hun := h.isUnramified w hw2 hwl
    refine ⟨le_trans hun.localInertiaGroup_le ?_⟩
    intro σ hσ
    have h1 : ρ.toLocal w σ = 1 := hσ
    show (ρ.conj e).toLocal w σ = 1
    rw [GaloisRep.toLocal_apply, GaloisRep.conj_apply,
      ← GaloisRep.toLocal_apply, h1]
    refine LinearMap.ext fun x => ?_
    simp
  · -- flatness: transport along the base-changed equivariant isomorphism
    intro w hw
    constructor
    intro I hI
    refine ((h.isFlat w hw).cond I hI).of_equiv _
      (LinearEquiv.baseChange R (R ⧸ I) M N e).toAddEquiv ?_
    intro g x
    show (LinearEquiv.baseChange R (R ⧸ I) M N e)
        (((ρ.baseChange (R ⧸ I)).toLocal w g) x) =
      (((ρ.conj e).baseChange (R ⧸ I)).toLocal w g)
        ((LinearEquiv.baseChange R (R ⧸ I) M N e) x)
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add a b ha hb => simp only [map_add, ha, hb]
    | tmul c m =>
      simp only [GaloisRep.toLocal_apply, GaloisRep.baseChange_tmul,
        LinearEquiv.baseChange_tmul, GaloisRep.conj_apply,
        LinearEquiv.conj_apply_apply, LinearEquiv.symm_apply_apply]
  · -- tameness at `2`: compose the quotient with the inverse isomorphism
    intro w hw
    obtain ⟨p, hpsurj, δ, hδ⟩ := h.isTameAtTwo w hw
    refine ⟨p.comp (e.symm : N →ₗ[R] M), ?_, δ, ?_, hδ.2.1, hδ.2.2⟩
    · intro r
      obtain ⟨m, hm⟩ := hpsurj r
      exact ⟨e m, by simp [hm]⟩
    · intro g x
      have h1 := hδ.1 g (e.symm x)
      show p (e.symm ((ρ.conj e).toLocal w g x)) = δ g (p (e.symm x))
      rw [GaloisRep.toLocal_apply, GaloisRep.conj_apply,
        LinearEquiv.conj_apply_apply, LinearEquiv.symm_apply_apply,
        ← GaloisRep.toLocal_apply, h1]

set_option backward.isDefEq.respectTransparency false in
open scoped TensorProduct in
/-- **The `F`-level condition transfers along an arbitrary base change to a
FINITE coefficient algebra** (PROVEN 2026-07-26 over the single Raynaud
leaf; the `F`-analogue of `Deformation.lean`'s
`isHardlyRamified_baseChange`).

Same four clauses, same proofs: the determinant maps along the structure
morphism (`LinearMap.det_baseChange`, then `IsScalarTower` for the
`ℤ_ℓ`-compatibility, which is what the cyclotomic condition is stated
against), unramifiedness at every `w ∤ 2ℓ` passes to any base change by the
existing instance on `GaloisRep.IsUnramifiedAt`, flatness at every `w ∣ ℓ`
is `isFlatAt_baseChange_of_numberField`, and tameness at every `w ∣ 2` is
`isHilbertTameAtTwo_baseChange`. -/
lemma isHilbertHardlyRamified_baseChange (ℓ : ℕ) [Fact ℓ.Prime]
    (F : Type u) [Field F] [NumberField F]
    {R : Type*} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    [IsLocalRing R] [Algebra ℤ_[ℓ] R]
    {M : Type*} [AddCommGroup M] [Module R M] [Module.Finite R M]
    [Module.Free R M] {hdimM : Module.rank R M = 2}
    (B : Type*) [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
    [IsLocalRing B] [Finite B] [Algebra ℤ_[ℓ] B] [Algebra R B]
    [ContinuousSMul R B] [IsScalarTower ℤ_[ℓ] R B]
    (hdimB : Module.rank B (B ⊗[R] M) = 2)
    {ρ : GaloisRep F R M} (h : IsHilbertHardlyRamified ℓ F hdimM ρ) :
    IsHilbertHardlyRamified ℓ F hdimB (ρ.baseChange B) := by
  constructor
  · -- the determinant maps along the structure morphism
    intro g
    have hdet : (ρ.baseChange B).det g = algebraMap R B (ρ.det g) := by
      show LinearMap.det ((ρ.baseChange B) g) = _
      rw [show ((ρ.baseChange B) g : Module.End B (B ⊗[R] M)) =
        LinearMap.baseChange B (ρ g) from rfl, LinearMap.det_baseChange]
      rfl
    rw [hdet, h.det g, ← IsScalarTower.algebraMap_apply]
  · -- unramifiedness passes to the base change (existing instance)
    intro w hw2 hwl
    letI : ρ.IsUnramifiedAt w := h.isUnramified w hw2 hwl
    infer_instance
  · -- flatness at every `w ∣ ℓ`
    intro w hw
    exact isFlatAt_baseChange_of_numberField w B (h.isFlat w hw)
  · -- tameness at every `w ∣ 2`
    intro w hw
    exact isHilbertTameAtTwo_baseChange B w (h.isTameAtTwo w hw)

open scoped TensorProduct in
/-- **Functoriality of the `F`-level condition** (PROVEN 2026-07-26 over the
single leaf `hasFlatProlongationAt_of_pi_surjection_of_numberField`).

`framePushforward ψ hψ ρ` is by definition `(ρ.baseChange A).conj
(TensorProduct.piScalarRight B A A (Fin 2))`, so this is
`isHilbertHardlyRamified_baseChange` followed by
`isHilbertHardlyRamified_conj`, exactly the two-step pattern of the
`ℚ`-level `isHardlyRamified_pushforwardFrame`. The hypothesis `halg` —
that `ψ` is a `ℤ_ℓ`-algebra map — is what manufactures the
`IsScalarTower ℤ_[ℓ] B A` instance the determinant clause is stated
against, and `[Finite A]` is what the flatness clause needs (a finite flat
group scheme has only finitely many geometric points).

It is Schlessinger's functoriality clause: the `F`-level framed hardly
ramified lifts form a FUNCTOR on the Artinian category. -/
theorem isHilbertBaseChangeClause (ℓ : ℕ) [Fact ℓ.Prime]
    (F : Type u) [Field F] [NumberField F] :
    IsHilbertBaseChangeClause ℓ F := by
  intro B _ _ _ _ _ A _ _ _ _ _ _ ψ hψ halg ρ hρ
  letI : Algebra B A := ψ.toAlgebra
  letI : ContinuousSMul B A := continuousSMul_of_algebraMap B A
    (by rw [RingHom.algebraMap_toAlgebra]; exact hψ)
  letI : IsScalarTower ℤ_[ℓ] B A := IsScalarTower.of_algebraMap_eq' (by
    rw [RingHom.algebraMap_toAlgebra]
    exact halg.symm)
  have hrank : Module.rank A (A ⊗[B] (Fin 2 → B)) = 2 := by
    rw [Module.rank_baseChange, rank_finTwoPi]
    simp
  exact isHilbertHardlyRamified_conj ℓ F (rank_finTwoPi A)
    (isHilbertHardlyRamified_baseChange ℓ F A hrank hρ)
    (TensorProduct.piScalarRight B A A (Fin 2))

/-- **Gluing along fibre products** (Schlessinger's H1 and H2; PROVEN
2026-07-26 over the two arithmetic leaves `isHilbertFlatAt_of_fibreProduct`
and `isHilbertTameAtTwo_of_fibreProduct` stated above — the determinant and
unramifiedness clauses are formal and are proven here).

Over `ℚ` this is `Deformation.lean`'s `isHardlyRamified_of_fibreProduct`,
and the cut here is that theorem's, one leaf for one leaf.

**FAITHFULNESS REPAIR, 2026-07-26: THIS THEOREM NOW CARRIES
`hℓ5 : 5 ≤ ℓ`, WHICH IT DID NOT WHEN IT WAS FIRST STATED.** The previous
version's docstring asserted that "only the flatness clause at `w ∣ ℓ`
needs an argument" and that the order-`2` clause is "an equation that holds
iff it holds in both components". **Both halves of that are wrong**, and
the second is wrong in the dangerous direction:

* the tame clause is not an equation but an EXISTENTIAL — some rank-one
  quotient, some unramified quadratic character — so `h₁` and `h₂` supply
  two lines with no compatibility over `A₀`, and gluing them needs a
  uniqueness argument, not a componentwise reading;
* that uniqueness argument is FALSE at `ℓ = 3`. The `ℚ`-level twin's
  `ℓ = 3` case was refuted on 2026-07-26 with an explicit counterexample
  over `K = ℚ(∛2, μ₃)` — `A₀ = 𝔽₃`, `A₁ = 𝔽₃[ε₁]`, `A₂ = 𝔽₃[ε₂]`,
  `B = 𝔽₃[ε₁,ε₂]/(ε₁,ε₂)²` and
  `ρ(g) = !![1, ε₂c'(g); ε₁c(g), χ(g)]` for `c` the Kummer cocycle of `2`
  and `c' = χc` — verified exhaustively over the 27-element ring `B`, and
  recorded in the block comment above `isTameAtTwo_of_fibreProduct` in
  `Deformation.lean`. That configuration is a counterexample to the
  `F`-level statement TOO, at `F = ℚ`: `IsHilbertHardlyRamified ℓ ℚ` is the
  `ℚ`-level condition read place by place, and `ℚ` is a number field, so
  nothing in `IsHilbertFibreProductClause ℓ F` excludes it.
* the degeneracy is uniform in `F`, not special to `ℚ`: at a place `w ∣ 2`
  of residue degree `f` one has `χ̄(Frob_w) = 2^f`, and the two candidate
  lines both satisfy the clause exactly when `2^{2f} ≡ 1 mod ℓ`, which at
  `ℓ = 3` holds for every `f`.

The repair is the `ℚ`-level one and is deliberately made in the THEOREM
rather than in the `Prop`-valued definition `IsHilbertFibreProductClause`:
the definition is left untouched (so the machine leaf
`exists_isWeaklyUniversal_hilbertDeformationDatum_of_clauses`, which takes
it as a hypothesis, is unchanged), and `5 ≤ ℓ` is threaded down from the
consumer `exists_finiteIndex_isIntegral_charpolyCoeff_of_isHardlyRamified`,
which already carries it, through
`exists_isWeaklyUniversal_hilbertDeformationDatum`. `IsHilbertHardlyRamified`
itself is unchanged.

WHAT IS PROVEN HERE. `hemb` gives the injectivity of `b ↦ (p₁ b, p₂ b)`,
and both formal clauses are statements about VALUES, which is exactly what
descends along an injection:

* *determinant*: `det` commutes with `framePushforward`
  (`det_framePushforward`), so the identity `ρ.det g = χ_ℓ(g)` may be
  checked after applying `p₁` and `p₂`, where it is `h₁.det`/`h₂.det`
  transported by the `ℤ_ℓ`-compatibilities `halg₁`/`halg₂`;
* *unramifiedness*: by `framePushforward_apply_map` an endomorphism of
  `Fin 2 → B` whose two projections are the identity is the identity, entry
  by entry, so inertia at `w` is killed by `ρ` as soon as it is killed by
  both projections.

The determinant identity is proven before the case split because the tame
leaf consumes it as `hdet` — it is the uniqueness input that makes the
gluing of the two lines possible at all.

References: Schlessinger, *Functors of Artin rings*, Trans. AMS 130 (1968),
Thm. 2.11 (H1, H2); Mazur, *Deforming Galois representations*, MSRI Publ.
16 (1989), §§18–23; Ramakrishna, Compositio 87 (1994), §1;
Conrad–Diamond–Taylor, JAMS 12 (1999), §2. -/
theorem isHilbertFibreProductClause (ℓ : ℕ) [Fact ℓ.Prime] (hℓ5 : 5 ≤ ℓ)
    (F : Type u) [Field F] [NumberField F] :
    IsHilbertFibreProductClause ℓ F := by
  intro A₀ _ _ _ _ _ _ A₁ _ _ _ _ _ _ A₂ _ _ _ _ _ _ B _ _ _ _ _ _
    f₁ f₂ hf₂ p₁ p₂ hp₁ hp₂ halg₁ halg₂ hcomm hemb hcart ρ h₁ h₂
  -- An element of `B` is determined by its two projections: this is the
  -- only consequence of `hemb` the two formal clauses need.
  have hinj : ∀ b b' : B, p₁ b = p₁ b' → p₂ b = p₂ b' → b = b' := by
    intro b b' hb₁ hb₂
    exact hemb.injective (by simp only [Prod.mk.injEq]; exact ⟨hb₁, hb₂⟩)
  -- The determinant identity, reflected back from the two projections.
  -- Used twice: as the `det` clause, and as `hdet` for the tame leaf.
  have hdet : ∀ g : Γ F, ρ.det g = algebraMap ℤ_[ℓ] B
      (cyclotomicCharacter (ℚ ᵃˡᵍ) ℓ
        (Field.absoluteGaloisGroup.map (algebraMap ℚ F) g).toRingEquiv) := by
    intro g
    refine hinj _ _ ?_ ?_
    · have hcompat : p₁ (algebraMap ℤ_[ℓ] B
          (cyclotomicCharacter (ℚ ᵃˡᵍ) ℓ
            (Field.absoluteGaloisGroup.map (algebraMap ℚ F) g).toRingEquiv)) =
          algebraMap ℤ_[ℓ] A₁
            (cyclotomicCharacter (ℚ ᵃˡᵍ) ℓ
              (Field.absoluteGaloisGroup.map (algebraMap ℚ F) g).toRingEquiv) := by
        rw [← halg₁]; rfl
      rw [← det_framePushforward p₁ hp₁ ρ g, h₁.det g, hcompat]
    · have hcompat : p₂ (algebraMap ℤ_[ℓ] B
          (cyclotomicCharacter (ℚ ᵃˡᵍ) ℓ
            (Field.absoluteGaloisGroup.map (algebraMap ℚ F) g).toRingEquiv)) =
          algebraMap ℤ_[ℓ] A₂
            (cyclotomicCharacter (ℚ ᵃˡᵍ) ℓ
              (Field.absoluteGaloisGroup.map (algebraMap ℚ F) g).toRingEquiv) := by
        rw [← halg₂]; rfl
      rw [← det_framePushforward p₂ hp₂ ρ g, h₂.det g, hcompat]
  refine ⟨hdet, ?_, ?_, ?_⟩
  · -- UNRAMIFIEDNESS: formal. An endomorphism of `Fin 2 → B` killed by
    -- both projections is the identity, entrywise.
    intro w hw2 hwl
    have key : ∀ g : Γ F, framePushforward p₁ hp₁ ρ g = 1 →
        framePushforward p₂ hp₂ ρ g = 1 → ρ g = 1 := by
      intro g hg₁ hg₂
      refine LinearMap.ext fun v => funext fun i => ?_
      refine hinj _ _ ?_ ?_
      · have hv := framePushforward_apply_map p₁ hp₁ ρ g v i
        rw [hg₁] at hv
        simpa using hv.symm
      · have hv := framePushforward_apply_map p₂ hp₂ ρ g v i
        rw [hg₂] at hv
        simpa using hv.symm
    refine ⟨?_⟩
    intro σ hσ
    have e₁ : (framePushforward p₁ hp₁ ρ).toLocal w σ = 1 :=
      (h₁.isUnramified w hw2 hwl).localInertiaGroup_le hσ
    have e₂ : (framePushforward p₂ hp₂ ρ).toLocal w σ = 1 :=
      (h₂.isUnramified w hw2 hwl).localInertiaGroup_le hσ
    show ρ.toLocal w σ = 1
    rw [GaloisRep.toLocal_apply] at e₁ e₂ ⊢
    exact key _ e₁ e₂
  · -- FLATNESS at `ℓ`: Ramakrishna/Raynaud, the first arithmetic leaf.
    intro w hw
    exact isHilbertFlatAt_of_fibreProduct ℓ F f₁ f₂ hf₂ p₁ p₂ hp₁ hp₂ hcomm hemb
      hcart w hw (h₁.isFlat w hw) (h₂.isFlat w hw)
  · -- TAMENESS at `2`: Conrad–Diamond–Taylor, the second arithmetic leaf.
    intro w hw
    exact isHilbertTameAtTwo_of_fibreProduct ℓ hℓ5 F f₁ f₂ hf₂ p₁ p₂ hp₁ hp₂ hcomm
      hemb hcart hdet w hw (h₁.isTameAtTwo w hw) (h₂.isTameAtTwo w hw)

/-! #### Hermite–Minkowski over `F` — the cut of Schlessinger's H3

The four declarations below decompose `isHilbertFiniteFramesClause`
(Schlessinger's H3 at the `F` level) along the same three-step cut that
`Modularity/Patching.lean` runs over `ℚ`
(`finite_setOf_intermediateField_inertiaAt_le` →
`finite_setOf_subgroup_inertiaAt_le` →
`finite_setOf_galoisRep_isUnramifiedAt` →
`finite_setOf_isHardlyRamified`).

That module may NOT be imported here — it is forbidden by this file's
circularity guard, and its chain is in any case stated over `ℚ` only,
place-indexed by rational primes. So the cut is redone over the variable
base field `F`. The split it produces is the point of the exercise:

* the two upper steps are pure Galois-theoretic and
  representation-theoretic BOOKKEEPING and are PROVEN here — a continuous
  representation into a finite discrete monoid has open kernel of bounded
  index, unramifiedness puts the local inertia inside that kernel, and
  the infinite Galois correspondence turns such kernels into finite
  Galois subextensions of `Fᵃˡᵍ/F` of bounded degree;
* ALL the arithmetic is isolated in the single leaf
  `finite_setOf_intermediateField_hilbertInertiaAt_le`, Hermite's theorem
  for `F`: finitely many finite Galois extensions of `F` of bounded degree
  unramified outside the places over `2ℓ`.
-/

/-- **Triviality of the local inertia at a place `w` of `F` on a subgroup
of `Γ F`**: every element of the local inertia group at `w`, pushed into
`Γ F` along the (chosen-embedding) map of absolute Galois groups, lies
in `N`.

For `N = K.fixingSubgroup` this says exactly that the finite Galois
subextension `K ⊆ Fᵃˡᵍ` is unramified at `w`; for `N` the kernel of a
framed representation it is exactly `GaloisRep.IsUnramifiedAt w`
(`finite_setOf_framedGaloisRep_isUnramifiedAt` below performs both
translations). The `F`-level twin of `Modularity/Patching.lean`'s
`InertiaTrivialAt`, indexed by a PLACE of `F` rather than by a rational
prime — `F` has several places over `2` and over `ℓ`, so the rational
indexing of the `ℚ`-level development is not available. -/
def HilbertInertiaTrivialAt {F : Type u} [Field F] [NumberField F]
    (w : HeightOneSpectrum (𝓞 F)) (N : Subgroup (Γ F)) : Prop :=
  ∀ σ ∈ localInertiaGroup w,
    Field.absoluteGaloisGroup.map (algebraMap F (w.adicCompletion F)) σ ∈ N

/-- **Hermite–Minkowski over `F`** (LEAF — the ONLY arithmetic input of
Schlessinger's H3 at the `F` level): for a fixed degree bound `n` there
are only finitely many finite Galois subextensions `K` of `Fᵃˡᵍ/F` with
`[K : F] ≤ n` on which the local inertia at every place of `F` away from
`2` and `ℓ` acts trivially.

MATHEMATICAL CONTENT. Such a `K` is a number field of degree
`[K : ℚ] = [K : F]·[F : ℚ] ≤ n·[F : ℚ]`, and it is unramified over `F`
outside the finitely many places above `2ℓ`, hence unramified over `ℚ`
outside the finite set of rational primes dividing `2·ℓ·d_F`. The
exponent of a prime `q` in the different of `K/ℚ` is bounded by
`e − 1 + e·v_q(e)` with `e ≤ [K : ℚ]` (Serre, *Corps Locaux* III §6
Prop. 13), so `|d_K|` is bounded by a constant depending only on `n`,
`F` and `ℓ`; Hermite's theorem (mathlib's
`NumberField.finite_of_discr_bdd`) then leaves finitely many such
fields.

ROUTE TO A PROOF, and why it is not taken here. `Modularity/Patching.lean`
carries the whole of this argument over `ℚ` and over the two-prime set
`{2, p}`, as the PROVEN
`finite_setOf_intermediateField_inertiaAt_le`, over the
discriminant-exponent bound `exists_discr_factorization_le_of_finrank_le`
and the inertia-to-discriminant transport
`not_dvd_discr_of_inertiaTrivialAt`. None of it is reachable from this
module: `Modularity/*` is forbidden by the circularity guard, and the
`ℚ`-level statement is in any case indexed by rational primes and by
`IntermediateField ℚ ℚᵃˡᵍ`, so consuming it would additionally need the
base-change dictionary "a place of `K` over a place of `F` over a prime
`q`". The honest discharge is the module split recorded in
`~/.flt-design-deformation-patching-dedup.md` — hoist the
Hermite–Minkowski block into a module upstream of BOTH this one and
`Patching.lean`, and generalize it there from `ℚ` and `{2, p}` to a
variable base number field and a finite set of places — not a third
re-proof here.

BOTH-WAYS AUDIT. A plain classical finiteness statement about
extensions of a number field: true outright as cited, with no
representation-theoretic hypothesis and no vacuity. It is NOT vacuous in
the degenerate direction either — the set is nonempty (it contains
`K = ⊥`), so the content is genuinely the finiteness and not an empty
quantification.

CIRCULARITY GUARD: as for every leaf of this file — no import from
`Family.lean`, `Lift.lean`, `Modularity/*` or `Deformation.lean`, and no
discharge through the odd-prime dichotomy
`not_isIrreducible_of_isHardlyRamified_of_five_le`. Neither is a
temptation here: the statement carries no representation at all. -/
theorem finite_setOf_intermediateField_hilbertInertiaAt_le (ℓ : ℕ) [Fact ℓ.Prime]
    (F : Type u) [Field F] [NumberField F] (n : ℕ) :
    {K : IntermediateField F (AlgebraicClosure F) |
      ∃ _ : FiniteDimensional F K,
        IsGalois F K ∧ Module.finrank F K ≤ n ∧
        ∀ w : HeightOneSpectrum (𝓞 F), ((2 : ℕ) : 𝓞 F) ∉ w.asIdeal →
          ((ℓ : ℕ) : 𝓞 F) ∉ w.asIdeal →
            HilbertInertiaTrivialAt w K.fixingSubgroup}.Finite :=
  sorry

set_option backward.isDefEq.respectTransparency false in
/-- **Finiteness of open normal subgroups of `Γ F` of bounded index
unramified outside `2ℓ`** (PROVEN over the Hermite leaf — the
Galois-correspondence step; "`G_{F,S}` is small").

Every such `N` is closed (`Subgroup.isClosed_of_isOpen`), hence by the
infinite Galois correspondence it is the fixing subgroup of its fixed
field `K = (Fᵃˡᵍ)^N` (`InfiniteGalois.fixingSubgroup_fixedField`), which
is finite-dimensional over `F` (`InfiniteGalois.isOpen_iff_finite`),
Galois over `F` (`InfiniteGalois.normal_iff_isGalois`), of degree
`[K : F] = #(Γ F ⧸ N) = N.index ≤ n`
(`InfiniteGalois.normalAutEquivQuotient`, `IsGalois.card_aut_eq_finrank`)
and inertia-trivial away from `2ℓ`. So the set injects into the finite
field set of the leaf above via `fixingSubgroup`.

The `F`-level twin of `Patching.lean`'s
`finite_setOf_subgroup_inertiaAt_le`, and its proof is that one with `ℚ`
replaced by `F` and the rational-prime indexing replaced by places;
`IsGalois F Fᵃˡᵍ` holds for the same reason it holds at `ℚ`, a number
field being perfect. -/
theorem finite_setOf_subgroup_hilbertInertiaAt_le (ℓ : ℕ) [Fact ℓ.Prime]
    (F : Type u) [Field F] [NumberField F] (n : ℕ) :
    {N : Subgroup (Γ F) |
      N.Normal ∧ IsOpen (N : Set (Γ F)) ∧ N.FiniteIndex ∧ N.index ≤ n ∧
      ∀ w : HeightOneSpectrum (𝓞 F), ((2 : ℕ) : 𝓞 F) ∉ w.asIdeal →
        ((ℓ : ℕ) : 𝓞 F) ∉ w.asIdeal → HilbertInertiaTrivialAt w N}.Finite := by
  classical
  haveI halgF : Algebra.IsAlgebraic F (AlgebraicClosure F) := AlgebraicClosure.isAlgebraic F
  haveI hacF : IsAlgClosure F (AlgebraicClosure F) := ⟨inferInstance, halgF⟩
  haveI hnormF : Normal F (AlgebraicClosure F) :=
    IsAlgClosure.normal F (AlgebraicClosure F)
  haveI hsepF : Algebra.IsSeparable F (AlgebraicClosure F) :=
    Algebra.IsAlgebraic.isSeparable_of_perfectField
  haveI hgalF : IsGalois F (AlgebraicClosure F) := ⟨⟩
  refine Set.Finite.subset
    ((finite_setOf_intermediateField_hilbertInertiaAt_le ℓ F n).image
      fun K => K.fixingSubgroup) ?_
  rintro N ⟨hnorm, hopen, hFI, hidx, hinert⟩
  have hclosed : IsClosed (N : Set (Γ F)) := Subgroup.isClosed_of_isOpen N hopen
  have hfix : (IntermediateField.fixedField (E := AlgebraicClosure F) N).fixingSubgroup = N :=
    InfiniteGalois.fixingSubgroup_fixedField ⟨N, hclosed⟩
  haveI hfd : FiniteDimensional F (IntermediateField.fixedField (E := AlgebraicClosure F) N) :=
    (InfiniteGalois.isOpen_iff_finite _).mp (by rw [hfix]; exact hopen)
  haveI hgalK : IsGalois F (IntermediateField.fixedField (E := AlgebraicClosure F) N) :=
    (InfiniteGalois.normal_iff_isGalois _).mp (by rw [hfix]; exact hnorm)
  haveI hnorm' := hnorm
  have hcard : Module.finrank F (IntermediateField.fixedField (E := AlgebraicClosure F) N) =
      Nat.card (Γ F ⧸ N) := by
    rw [← IsGalois.card_aut_eq_finrank]
    exact (Nat.card_congr (InfiniteGalois.normalAutEquivQuotient
      (⟨N, hclosed⟩ : ClosedSubgroup (Γ F))).toEquiv).symm
  have hrank : Module.finrank F (IntermediateField.fixedField (E := AlgebraicClosure F) N) ≤ n := by
    rw [hcard, ← Subgroup.index_eq_card N]
    exact hidx
  refine ⟨_, ⟨hfd, hgalK, hrank, ?_⟩, hfix⟩
  intro w h2 hl
  rw [hfix]
  exact hinert w h2 hl

set_option backward.isDefEq.respectTransparency false in
/-- **Finiteness of framed representations of `Γ F` unramified outside
`2ℓ`** (PROVEN — the representations-to-subgroups bookkeeping step).

Over a finite discrete coefficient ring `A` the endomorphism monoid
`E = End_A(A²)` is finite and discrete, so the kernel of a continuous
`ρ : Γ F → E` is an OPEN normal subgroup whose quotient injects into `E`
(index at most `#E`), and it contains the image of the local inertia at
every place away from `2ℓ` (`GaloisRep.IsUnramifiedAt` transported along
`GaloisRep.toLocal_apply`). There are finitely many candidate kernels
(`finite_setOf_subgroup_hilbertInertiaAt_le`) and each carries finitely
many representations, a representation being determined by the function
`Γ F ⧸ N → E` it induces on `Quotient.out` representatives.

The `F`-level twin of `Patching.lean`'s
`finite_setOf_galoisRep_isUnramifiedAt`; the proof is that one with `ℚ`
replaced by `F` and the rational-prime indexing replaced by places. -/
theorem finite_setOf_framedGaloisRep_isUnramifiedAt.{uA} (ℓ : ℕ) [Fact ℓ.Prime]
    (F : Type u) [Field F] [NumberField F]
    {A : Type uA} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [DiscreteTopology A] [Finite A] :
    {ρ : FramedGaloisRep F A (Fin 2) |
      ∀ w : HeightOneSpectrum (𝓞 F), ((2 : ℕ) : 𝓞 F) ∉ w.asIdeal →
        ((ℓ : ℕ) : 𝓞 F) ∉ w.asIdeal → ρ.IsUnramifiedAt w}.Finite := by
  classical
  haveI hfinE : Finite (Module.End A (Fin 2 → A)) :=
    Finite.of_injective
      (fun f => (f : (Fin 2 → A) → (Fin 2 → A))) DFunLike.coe_injective
  -- the kernel subgroup of a representation
  let kerOf : FramedGaloisRep F A (Fin 2) → Subgroup (Γ F) := fun ρ =>
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
  have hmem : ∀ (ρ : FramedGaloisRep F A (Fin 2)) (g : Γ F),
      g ∈ kerOf ρ ↔ ρ g = 1 := fun _ _ => Iff.rfl
  -- a representation is recovered on `Quotient.out` representatives
  have hout : ∀ (ρ : FramedGaloisRep F A (Fin 2)) (N : Subgroup (Γ F)),
      kerOf ρ = N → ∀ g : Γ F, ρ (QuotientGroup.mk (s := N) g).out = ρ g := by
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
  have hinj : ∀ ρ : FramedGaloisRep F A (Fin 2),
      Function.Injective (fun x : Γ F ⧸ kerOf ρ => ρ x.out) := by
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
  have hopenker : ∀ ρ : FramedGaloisRep F A (Fin 2),
      IsOpen ((kerOf ρ : Subgroup (Γ F)) : Set (Γ F)) := by
    intro ρ
    letI := moduleTopology A (Module.End A (Fin 2 → A))
    haveI : Module.Finite A (Module.End A (Fin 2 → A)) := Module.Finite.of_finite
    haveI : DiscreteTopology (Module.End A (Fin 2 → A)) := by
      obtain ⟨m, f, hf⟩ := Module.Finite.exists_fin' A (Module.End A (Fin 2 → A))
      refine @DiscreteTopology.mk _ (moduleTopology A (Module.End A (Fin 2 → A))) ?_
      rw [ModuleTopology.eq_coinduced_of_surjective hf,
        DiscreteTopology.eq_bot (α := Fin m → A), coinduced_bot]
    have hcont : Continuous fun g : Γ F => ρ g :=
      ContinuousMonoidHom.continuous_toFun ρ
    exact (isOpen_discrete ({1} : Set (Module.End A (Fin 2 → A)))).preimage hcont
  have hnormal : ∀ ρ : FramedGaloisRep F A (Fin 2), (kerOf ρ).Normal := by
    intro ρ
    refine ⟨fun x hx g => ?_⟩
    show ρ (g * x * g⁻¹) = 1
    rw [map_mul, map_mul, (hx : ρ x = 1), mul_one, ← map_mul, mul_inv_cancel, map_one]
  have hfinquot : ∀ ρ : FramedGaloisRep F A (Fin 2), Finite (Γ F ⧸ kerOf ρ) :=
    fun ρ => Finite.of_injective _ (hinj ρ)
  have hidx : ∀ ρ : FramedGaloisRep F A (Fin 2),
      (kerOf ρ).index ≤ Nat.card (Module.End A (Fin 2 → A)) := by
    intro ρ
    rw [Subgroup.index_eq_card]
    exact Nat.card_le_card_of_injective _ (hinj ρ)
  -- unramifiedness puts the local inertia inside the kernel
  have hinertker : ∀ ρ : FramedGaloisRep F A (Fin 2),
      (∀ w : HeightOneSpectrum (𝓞 F), ((2 : ℕ) : 𝓞 F) ∉ w.asIdeal →
        ((ℓ : ℕ) : 𝓞 F) ∉ w.asIdeal → ρ.IsUnramifiedAt w) →
      ∀ w : HeightOneSpectrum (𝓞 F), ((2 : ℕ) : 𝓞 F) ∉ w.asIdeal →
        ((ℓ : ℕ) : 𝓞 F) ∉ w.asIdeal → HilbertInertiaTrivialAt w (kerOf ρ) := by
    intro ρ hρ w h2 hl σ hσ
    have h1 : (ρ.toLocal w) σ = 1 := (hρ w h2 hl).localInertiaGroup_le hσ
    rw [GaloisRep.toLocal_apply] at h1
    exact (hmem ρ _).mpr h1
  -- assemble: finitely many kernels, finitely many maps per kernel
  have h𝒩fin := finite_setOf_subgroup_hilbertInertiaAt_le ℓ F
    (Nat.card (Module.End A (Fin 2 → A)))
  refine Set.Finite.subset (h𝒩fin.biUnion
    (t := fun N => {ρ : FramedGaloisRep F A (Fin 2) | kerOf ρ = N})
    fun N hN => ?_) ?_
  · -- the fiber over a fixed kernel injects into `Γ F ⧸ N → E`
    haveI : N.FiniteIndex := hN.2.2.1
    haveI : Finite (Γ F ⧸ N) := Subgroup.finite_quotient_of_finiteIndex
    refine Set.Finite.of_finite_image (f := fun ρ => fun x : Γ F ⧸ N => ρ x.out)
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

/-- **Finiteness of the hardly ramified frames over a finite level**
(PROVEN 2026-07-26 over the Hermite–Minkowski cut above; Schlessinger's
H3).

Over `ℚ` this is `Deformation.lean`'s leaf
`finite_setOf_isHardlyRamified_frames`. The argument is Hermite–Minkowski:
a hardly ramified frame over the finite ring `A` is a homomorphism
`G_F → GL₂(A)` unramified outside the finitely many places of `F` above
`2ℓ` and with bounded ramification at those, hence factors through the
Galois group of an extension of `F` of bounded degree and bounded
discriminant, of which there are finitely many; and `GL₂(A)` is finite.

Only the FIRST clause of `IsHilbertHardlyRamified` that the argument
touches is used — `isUnramified` — so the assembly is a `Set.Finite.subset`
of `finite_setOf_framedGaloisRep_isUnramifiedAt`: the determinant,
flatness and tameness clauses only shrink the set further. -/
theorem isHilbertFiniteFramesClause (ℓ : ℕ) [Fact ℓ.Prime]
    (F : Type u) [Field F] [NumberField F] :
    IsHilbertFiniteFramesClause ℓ F := by
  intro A _ _ _ _ _ _ _
  exact (finite_setOf_framedGaloisRep_isUnramifiedAt ℓ F (A := A)).subset
    fun _ hρ w h2 hl => hρ.isUnramified w h2 hl

/-! #### Bricks for the pro-limit clause (added 2026-07-26)

Six elementary transport lemmas consumed only by `isHilbertProLimitClause`
below. Each is the `F`-level (respectively base-field-generic) twin of a
declaration `Deformation.lean` states over `ℚ`; the proofs are verbatim the
`ℚ`-level ones, because none of them uses anything about the base field.
They are restated rather than reused for the usual reason: `Deformation.lean`
is DOWNSTREAM of this module (it `public import`s it), so nothing there is
in scope here. The names are deliberately different from the `ℚ`-level ones
— `Deformation.lean` re-exports this namespace, so a name collision would
break its elaboration outright, as it once did for a duplicated
`det_pushforwardFrame`. -/

set_option backward.isDefEq.respectTransparency false in
open scoped TensorProduct in
/-- **Matrix entries of a pushed-forward frame** (PROVEN, elementary; the
`F`-level twin of `Deformation.lean`'s `pushforwardFrame_apply`):
`framePushforward ψ` is "apply `ψ` to the matrix entries", so on a vector
already in the image of `ψ` it acts entrywise through `ψ`.

`(1 : A) ⊗ₜ x` is a preimage of `ψ ∘ x` under `TensorProduct.piScalarRight`,
so `LinearEquiv.conj_apply_apply` moves the conjugation out of the way and
`GaloisRep.baseChange_tmul` finishes. This is the dictionary that lets a
statement about `framePushforward` over `R ⧸ I` be read back as a
congruence in `R`, which is what the unramifiedness clause of
`isHilbertProLimitClause` runs on. -/
lemma framePushforward_apply {F : Type u} [Field F] [NumberField F]
    {B : Type u} [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
    {A : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    (ψ : B →+* A) (hψ : Continuous ψ) (ρ : FramedGaloisRep F B (Fin 2))
    (g : Γ F) (x : Fin 2 → B) :
    (framePushforward ψ hψ ρ) g (fun i => ψ (x i)) = fun j => ψ (ρ g x j) := by
  letI : Algebra B A := ψ.toAlgebra
  letI : ContinuousSMul B A := continuousSMul_of_algebraMap B A
    (by rw [RingHom.algebraMap_toAlgebra]; exact hψ)
  have hsm : ∀ b : B, b • (1 : A) = ψ b := by
    intro b
    rw [Algebra.smul_def, RingHom.algebraMap_toAlgebra, mul_one]
  have hx : (fun i => ψ (x i)) =
      (TensorProduct.piScalarRight B A A (Fin 2)) ((1 : A) ⊗ₜ[B] x) := by
    funext i
    rw [TensorProduct.piScalarRight_apply, TensorProduct.piScalarRightHom_tmul]
    exact (hsm (x i)).symm
  show ((ρ.baseChange A).conj (TensorProduct.piScalarRight B A A (Fin 2))) g _ = _
  rw [hx, GaloisRep.conj_apply, LinearEquiv.conj_apply_apply,
    LinearEquiv.symm_apply_apply, GaloisRep.baseChange_tmul]
  funext j
  rw [TensorProduct.piScalarRight_apply, TensorProduct.piScalarRightHom_tmul]
  exact hsm _

open scoped TensorProduct in
/-- **A flat prolongation descends through the base change to `A ⧸ ⊥`**
(PROVEN, over an arbitrary number field; the base-field-generic twin of
`Deformation.lean`'s `hasFlatProlongationAt_of_baseChange_bot`):
`A ⧸ ⊥ ≃ A` is `Submodule.quotEquivOfEqBot`, and tensoring it with the
identity collapses `(A ⧸ ⊥) ⊗_A N` onto `N` equivariantly — the Galois
action on the base change is `g ⊗ 1`, so the transport is `map_smul`.

This is the step that turns the flatness clause of the level-`I` datum
(which quantifies over the open ideals of `R ⧸ I`, evaluated at `⊥`) back
into a statement about `ρ.baseChange (R ⧸ I)`. -/
lemma hasFlatProlongationAt_of_quotBot {K : Type u} [Field K] [NumberField K]
    {A : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    {N : Type v} [AddCommGroup N] [Module A N] [Module.Finite A N]
    [Module.Free A N] (τ : GaloisRep K A N)
    (w : HeightOneSpectrum (𝓞 K))
    (h : (τ.baseChange (A ⧸ (⊥ : Ideal A))).HasFlatProlongationAt w) :
    τ.HasFlatProlongationAt w := by
  let φ : (A ⧸ (⊥ : Ideal A)) ≃ₗ[A] A := Submodule.quotEquivOfEqBot _ rfl
  let E : ((A ⧸ (⊥ : Ideal A)) ⊗[A] N) ≃ₗ[A] N :=
    (TensorProduct.congr φ (LinearEquiv.refl A N)).trans (TensorProduct.lid A N)
  refine h.of_equiv _ E.toAddEquiv ?_
  intro g x
  show E (((τ.baseChange (A ⧸ (⊥ : Ideal A))).toLocal w g) x) =
    (τ.toLocal w g) (E x)
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => simp only [map_add, ha, hb]
  | tmul c y =>
    show E (c ⊗ₜ[A] (τ.toLocal w g) y) = (τ.toLocal w g) (E (c ⊗ₜ[A] y))
    show φ c • ((τ.toLocal w g) y) = (τ.toLocal w g) (φ c • y)
    rw [map_smul]

/-- **A flat prolongation descends through conjugation** (PROVEN, over an
arbitrary number field; the base-field-generic twin of
`Deformation.lean`'s `hasFlatProlongationAt_of_conj`): the inverse of the
conjugating isomorphism is itself equivariant, so
`GaloisRep.HasFlatProlongationAt.of_equiv` transports the Hopf-algebra
witness back. This is what strips the framing identification
`TensorProduct.piScalarRight` off `framePushforward`. -/
lemma hasFlatProlongationAt_of_conjugate {K : Type u} [Field K] [NumberField K]
    {A : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    {M : Type v} [AddCommGroup M] [Module A M]
    {N : Type v} [AddCommGroup N] [Module A N] (τ : GaloisRep K A M)
    (e : M ≃ₗ[A] N) (w : HeightOneSpectrum (𝓞 K))
    (h : (τ.conj e).HasFlatProlongationAt w) :
    τ.HasFlatProlongationAt w := by
  refine h.of_equiv _ e.symm.toAddEquiv ?_
  intro g x
  show e.symm (((τ.conj e).toLocal w g) x) = (τ.toLocal w g) (e.symm x)
  rw [GaloisRep.toLocal_apply, GaloisRep.conj_apply, LinearEquiv.conj_apply_apply,
    LinearEquiv.symm_apply_apply, GaloisRep.toLocal_apply]

/-- **A flat prolongation is inherited by any representation on a
subsingleton space** (PROVEN, over an arbitrary number field; the
base-field-generic twin of `Deformation.lean`'s
`hasFlatProlongationAt_of_subsingleton`): the Hopf-algebra witness is reused
and the geometric-points identification is composed with the unique additive
isomorphism of one-element groups, every side condition being
`Subsingleton.elim`.

This is what discharges the `I = ⊤` case of `GaloisRep.IsFlatAt`, whose
quantifier runs over ALL open ideals — including the unit ideal, at which
the coefficient ring is trivial and no level datum is available, since
`IsLocalRing (R ⧸ ⊤)` is false. -/
lemma hasFlatProlongationAt_of_bothSubsingleton {K : Type u} [Field K]
    [NumberField K] {A : Type u} [CommRing A] [TopologicalSpace A]
    {M : Type v} [AddCommGroup M] [Module A M] [Subsingleton M]
    {A' : Type u} [CommRing A'] [TopologicalSpace A']
    {M' : Type v} [AddCommGroup M'] [Module A' M'] [Subsingleton M']
    {τ₁ : GaloisRep K A M} (τ₂ : GaloisRep K A' M')
    (w : HeightOneSpectrum (𝓞 K))
    (h : τ₁.HasFlatProlongationAt w) :
    τ₂.HasFlatProlongationAt w := by
  haveI : Subsingleton (τ₁.toLocal w).Space := inferInstanceAs (Subsingleton M)
  haveI : Subsingleton (τ₂.toLocal w).Space := inferInstanceAs (Subsingleton M')
  exact h.of_equiv _ ⟨⟨fun _ => 0, fun _ => 0, fun _ => Subsingleton.elim _ _,
    fun _ => Subsingleton.elim _ _⟩, fun _ _ => Subsingleton.elim _ _⟩
    fun _ _ => Subsingleton.elim _ _

open scoped TensorProduct in
/-- A tensor product with a subsingleton left factor is a subsingleton
(PROVEN, elementary: every pure tensor is `0 ⊗ₜ y = 0`; the twin of
`Deformation.lean`'s `subsingleton_tensorProduct_of_left`). -/
lemma subsingleton_tensorProduct_left {A : Type u} [CommRing A]
    {X : Type v} [AddCommGroup X] [Module A X] [Subsingleton X]
    {N : Type v} [AddCommGroup N] [Module A N] : Subsingleton (X ⊗[A] N) := by
  have hall : ∀ z : X ⊗[A] N, z = 0 := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => rfl
    | add a b ha hb => rw [ha, hb, add_zero]
    | tmul c y => rw [Subsingleton.elim c 0, TensorProduct.zero_tmul]
  exact ⟨fun a b => by rw [hall a, hall b]⟩

/-- **The tame quotient at a place over `2` is detected on the finite
levels** (LEAF, new 2026-07-26 — the ONE clause of
`isHilbertProLimitClause` that is a genuine pro-limit statement rather
than a congruence).

WHY THE OTHER THREE CLAUSES ARE NOT HERE. The determinant condition is an
equality in `R`, unramifiedness is the vanishing of `ρ(σ) − 1`, and both
are read off the levels by `𝔪`-adic separatedness
(`IsAdicComplete → IsHausdorff`); flatness at `w ∣ ℓ` is *literally* a
condition on the reductions (`GaloisRep.IsFlatAt.cond` quantifies over
open ideals), so it transfers by re-indexing. Only the tame quotient asks
for the EXISTENCE of an object over `R` — a rank-one free quotient — and
existence is exactly what does not descend from a compatible system for
free: the `π_I` supplied at different levels are UNRELATED, `hq` being a
family of independent existence statements, so the whole content is
manufacturing compatibility.

THE ROUTE. `Deformation.lean` carries out precisely this argument over
`ℚ`, as the PROVEN `isTameAtTwo_of_forall_isOpen_quotient`, and its four
steps transpose verbatim with `Γ ℚ_2` replaced by `Γ F_w` and
`AddSubgroup.inertia 𝔪_{Z₂ᵃˡᵍ} (Γ ℚ_2)` by `localInertiaGroup w`:

1. *the character is `±1`-valued, hence rigid* — `δ_I(g)² = 1` and `2` is
   a unit, so `(x−1)(x+1) = 0` forces `x = ±1` and the sign lifts
   uniquely to a multiplicative `ε : Γ F_w → {±1} ⊆ R`;
2. *only two characters can occur*, so some `ε` is realised at EVERY
   level — three distinct quotient characters of a rank-two space over
   the residue field would give three pairwise independent lines in a
   plane;
3. *with `ε` FIXED the fibres are `R`-MODULES*, being cut out by the
   `R`-linear conditions `∑ᵢ ρ(g)_{ji} xᵢ − ε(g) x_j ∈ 𝔪ⁿ⁺¹` — this
   linearity is the crux, and it is why no finiteness of the residue
   field is needed;
4. *Mittag-Leffler comes free from Artinian-ness* of `R ⧸ 𝔪ⁿ⁺¹`, and
   `IsPrecomplete`/`IsHausdorff` assemble the limit; unimodularity of the
   level witnesses survives it, which over the local ring `R` is exactly
   surjectivity of `p`.

That development is some 900 lines and lives DOWNSTREAM of this module, so
it must be re-run here rather than imported.

CAUTION — THE ODDNESS OF `ℓ` IS NOT AVAILABLE HERE, AND STEP 1 NEEDS IT.
Over `ℚ` the ambient `hℓOdd : Odd ℓ` is what makes `2` a unit of
`ℤ_[ℓ]`, hence of `R` (`isUnit_two_of_oddPrime`), and the `ℚ`-level
docstring records that this is the ONE place oddness is used and that it
is used essentially. `IsHilbertProLimitClause`, and therefore this leaf,
carries only `[Fact ℓ.Prime]`: at `ℓ = 2` the equation `x² = 1` in a
`ℤ_[2]`-algebra no longer pins `x` to `±1`, the rigidity of step 1
collapses, and steps 2–4 have nothing to propagate. So whoever attacks
this leaf should FIRST settle `ℓ = 2` — either by finding the substitute
rigidity (note that at `ℓ = 2` the places over `ℓ` and the places over
`2` COINCIDE, so `IsHilbertHardlyRamified.isFlat` is available at exactly
the same `w` and may supply it), or by refuting the leaf there, which
would be a faithfulness defect in `IsHilbertProLimitClause` itself and a
cut-level repair rather than a proof obligation.

FAITHFULNESS: the inertia quantifier is inside `δ.ker` and must stay
there. `δ` is UNRAMIFIED, not trivial, and widening `localInertiaGroup w`
to all of `Γ F_w` makes the statement false for every unramified
quadratic twist — the standing rule of this development.

References: Mazur, *Deforming Galois representations*, MSRI Publ. 16
(1989), §1.2; Conrad–Diamond–Taylor, JAMS 12 (1999), §2; Grothendieck,
EGA III 5.4.1. -/
theorem isHilbertTameAtTwo_of_forall_isOpen_quotient (ℓ : ℕ) [Fact ℓ.Prime]
    (F : Type u) [Field F] [NumberField F]
    {R : Type u} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    [IsLocalRing R] [Algebra ℤ_[ℓ] R] [IsNoetherianRing R]
    (hadic : IsAdic (IsLocalRing.maximalIdeal R))
    (hcomplete : IsAdicComplete (IsLocalRing.maximalIdeal R) R)
    {ρ : FramedGaloisRep F R (Fin 2)}
    (hq : ∀ (I : Ideal R), IsOpen (I : Set R) → ∀ [IsLocalRing (R ⧸ I)]
      (hmk : Continuous (Ideal.Quotient.mk I)),
      IsHilbertHardlyRamified ℓ F (rank_finTwoPi (R ⧸ I))
        (framePushforward (Ideal.Quotient.mk I) hmk ρ))
    (w : HeightOneSpectrum (𝓞 F)) (hw : ((2 : ℕ) : 𝓞 F) ∈ w.asIdeal) :
    ∃ (p : (Fin 2 → R) →ₗ[R] R) (_ : Function.Surjective p)
      (δ : GaloisRep (w.adicCompletion F) R R),
      (∀ g : Γ (w.adicCompletion F), ∀ v : Fin 2 → R,
        p (ρ.toLocal w g v) = δ g (p v)) ∧
      localInertiaGroup w ≤ δ.ker ∧
      ∀ g : Γ (w.adicCompletion F), δ g * δ g = 1 :=
  sorry

set_option backward.isDefEq.respectTransparency false in
/-- **Detection of the `F`-level condition on the finite levels** (PROVEN
2026-07-26 over the single residual leaf
`isHilbertTameAtTwo_of_forall_isOpen_quotient` above).

Over `ℚ` this is `Deformation.lean`'s PROVEN
`isHardlyRamified_of_forall_isOpen_quotient`, and the cut here is that
one's cut: three clauses are congruences or re-indexings and are proven
below, and the tame quotient at the places over `2` is the one genuine
pro-limit statement, isolated as the leaf above.

* *determinant* (PROVEN): `det_framePushforward` reads the level-`𝔪ⁿ⁺¹`
  identity back as a congruence in `R`, and `R` is `𝔪`-adically SEPARATED
  (`IsAdicComplete → IsHausdorff`), so holding modulo every `𝔪ⁿ` gives it
  outright. Note the `F`-level determinant clause is stated through the
  RESTRICTION of the `ℚ`-adic cyclotomic character, so the level datum and
  the limit statement name literally the same scalar.
* *unramifiedness* (PROVEN): `ρ(σ) − 1` is read entrywise through
  `framePushforward_apply`, and the same separatedness kills it.
* *flatness at `w ∣ ℓ`* (PROVEN, and this is the clause the leaf's author
  called definitional): `GaloisRep.IsFlatAt.cond` quantifies over the open
  ideals of the COEFFICIENT ring, so the level-`I` datum evaluated at `⊥`
  already IS the statement wanted at `I`, up to the two formal transports
  `hasFlatProlongationAt_of_quotBot` and `hasFlatProlongationAt_of_conjugate`.
  The quantifier of `IsFlatAt` includes the UNIT ideal, at which no level
  datum exists (`R ⧸ ⊤` is not local); that case is discharged separately
  through `hasFlatProlongationAt_of_bothSubsingleton`, transporting the
  witness at `𝔪¹`.
* *tameness at `w ∣ 2`*: the leaf.

The hypothesis is stated over ALL open ideals rather than over the powers
`𝔪ⁿ` because that is the form `IsFlatAt` consumes; `hadic` makes the two
interchangeable. -/
theorem isHilbertProLimitClause (ℓ : ℕ) [Fact ℓ.Prime]
    (F : Type u) [Field F] [NumberField F] :
    IsHilbertProLimitClause ℓ F := by
  classical
  intro R _ _ _ _ _ _ hadic hcomplete ρ hq
  haveI := hcomplete
  have hcont : ∀ J : Ideal R, Continuous (Ideal.Quotient.mk J) :=
    fun _ => continuous_quot_mk
  -- separation: the topology is `𝔪`-adic and `R` is `𝔪`-adically separated
  have hsep : ∀ x y : R,
      (∀ n : ℕ, x - y ∈ (IsLocalRing.maximalIdeal R ^ (n + 1) : Ideal R)) → x = y := by
    intro x y hxy
    have h0 : x - y = 0 := by
      refine IsHausdorff.haus
        (inferInstance : IsHausdorff (IsLocalRing.maximalIdeal R) R) _ fun n => ?_
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
  -- a proper ideal of a local ring has local quotient
  have hlocal : ∀ J : Ideal R, J ≠ ⊤ → IsLocalRing (R ⧸ J) := by
    intro J hJt
    haveI : Nontrivial (R ⧸ J) := Ideal.Quotient.nontrivial_iff.mpr hJt
    exact IsLocalRing.of_surjective' (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- the cyclotomic determinant, level by level
    intro g
    refine hsep _ _ fun n => ?_
    haveI := hlocal _ (hnetop n)
    have hd := (hq _ (hpow (n + 1)) (hcont _)).det g
    rw [det_framePushforward,
      IsScalarTower.algebraMap_apply ℤ_[ℓ] R
        (R ⧸ IsLocalRing.maximalIdeal R ^ (n + 1))] at hd
    exact Ideal.Quotient.eq.mp hd
  · -- unramifiedness outside the places over `2` and `ℓ`
    intro w hw2 hwl
    refine ⟨fun σ hσ => ?_⟩
    show (ρ.toLocal w) σ = 1
    refine LinearMap.ext fun x => funext fun j => ?_
    show (ρ.toLocal w) σ x j = x j
    rw [GaloisRep.toLocal_apply]
    refine hsep _ _ fun n => ?_
    set J : Ideal R := IsLocalRing.maximalIdeal R ^ (n + 1)
    haveI := hlocal J (hnetop n)
    have h1 : (framePushforward (Ideal.Quotient.mk J) (hcont J) ρ).toLocal w σ = 1 :=
      ((hq J (hpow (n + 1)) (hcont J)).isUnramified w hw2 hwl).localInertiaGroup_le hσ
    have h2 : (framePushforward (Ideal.Quotient.mk J) (hcont J) ρ).toLocal w σ
        (fun i => Ideal.Quotient.mk J (x i)) = fun i => Ideal.Quotient.mk J (x i) := by
      rw [h1]
      rfl
    rw [GaloisRep.toLocal_apply, framePushforward_apply] at h2
    exact Ideal.Quotient.eq.mp (congrFun h2 j)
  · -- flatness at the places over `ℓ`: literally a condition on the levels
    intro w hw
    constructor
    intro I hI
    by_cases hIt : I = ⊤
    · -- the unit ideal carries no level datum; both spaces are trivial
      subst hIt
      have hmtop : IsOpen ((⊤ : Ideal (R ⧸ IsLocalRing.maximalIdeal R ^ 1)) :
          Set (R ⧸ IsLocalRing.maximalIdeal R ^ 1)) := by
        rw [Submodule.top_coe]
        exact isOpen_univ
      haveI := hlocal _ (hnetop 0)
      have h1 := ((hq _ (hpow 1) (hcont _)).isFlat w hw).cond ⊤ hmtop
      haveI : Subsingleton ((R ⧸ IsLocalRing.maximalIdeal R ^ 1) ⧸
          (⊤ : Ideal (R ⧸ IsLocalRing.maximalIdeal R ^ 1))) :=
        Ideal.Quotient.subsingleton_iff.mpr rfl
      haveI : Subsingleton (R ⧸ (⊤ : Ideal R)) :=
        Ideal.Quotient.subsingleton_iff.mpr rfl
      haveI := subsingleton_tensorProduct_left
        (A := R ⧸ IsLocalRing.maximalIdeal R ^ 1)
        (X := (R ⧸ IsLocalRing.maximalIdeal R ^ 1) ⧸
          (⊤ : Ideal (R ⧸ IsLocalRing.maximalIdeal R ^ 1)))
        (N := Fin 2 → (R ⧸ IsLocalRing.maximalIdeal R ^ 1))
      haveI := subsingleton_tensorProduct_left (A := R)
        (X := R ⧸ (⊤ : Ideal R)) (N := Fin 2 → R)
      exact hasFlatProlongationAt_of_bothSubsingleton _ _ h1
    · haveI := hlocal I hIt
      have hbot : IsOpen (((⊥ : Ideal (R ⧸ I))) : Set (R ⧸ I)) := by
        have hqm : Topology.IsQuotientMap (Ideal.Quotient.mk I) :=
          (QuotientRing.isOpenQuotientMap_mk I).isQuotientMap
        have hpre : (Ideal.Quotient.mk I) ⁻¹' ((⊥ : Ideal (R ⧸ I)) : Set (R ⧸ I)) =
            (I : Set R) := by
          ext z
          simp [Ideal.Quotient.eq_zero_iff_mem]
        rw [← hqm.isOpen_preimage, hpre]
        exact hI
      have h1 := ((hq I hI (hcont I)).isFlat w hw).cond ⊥ hbot
      have h2 := hasFlatProlongationAt_of_quotBot _ _ h1
      exact hasFlatProlongationAt_of_conjugate _
        (TensorProduct.piScalarRight R (R ⧸ I) (R ⧸ I) (Fin 2)) _ h2
  · -- the tame quotient at the places over `2`: the one genuine pro-limit clause
    intro w hw
    exact isHilbertTameAtTwo_of_forall_isOpen_quotient ℓ F hadic hcomplete hq w hw

/-- **Brauer–Nesbitt over `F`** (PROVEN 2026-07-26): equal characteristic
polynomials at every element identify a framed representation with the
irreducible `ρbar|_{G_F}` up to conjugation. See
`IsHilbertResidualRigidityClause` for the argument and for why the `ℚ`-level
twin is the harder statement.

The proof is a direct application of the abstract dimension-`2` Brauer–Nesbitt
core `exists_linearEquiv_of_charpoly_eq` (`BrauerNesbittConjugacy.lean`), which
is exactly this statement for representations of an ABSTRACT group and carries
no topology: the charpolys here are given at every `g ∈ G_F`, so — unlike the
`ℚ`-level twin `exists_conj_of_charFrob_eq`, which is the same core preceded by
a Chebotarev density argument turning Frobenius data into all-of-`G` data —
there is nothing to do before invoking it. The only glue is the passage between
`Module.rank` and `Module.finrank`, `Module.finrank k (Fin 2 → k) = 2`, and the
translation of the intertwining `e ∘ τ g = ρbar g ∘ e` into the equality of
`GaloisRep`s `τ.conj e = ρbar|_{G_F}` (`GaloisRep.ext` plus
`GaloisRep.conj_apply`), verbatim as in `exists_conj_of_charFrob_eq_away`'s
final step.

HYPOTHESIS ADDED, AND WHY (2026-07-26, part of proving it). This theorem —
NOT the clause `IsHilbertResidualRigidityClause`, which is unchanged and stays
general — carries `[Finite k]`. Brauer–Nesbitt itself is true over an arbitrary
field, but the dimension-`2` proof available here goes through
`false_of_trace_toModuleEnd_eq_zero`, whose endgame needs the commutant
`D = End_A W` to be a FIELD (little Wedderburn) and `D/k` to be SEPARABLE — and
the latter genuinely fails over an imperfect field: for `k = 𝔽₂(t)` and
`D = k(√t)` every `k`-trace on `D` vanishes identically, which is precisely the
configuration that argument must exclude. So `[Finite k]` is not decoration
here; it is the hypothesis the available core is proven under.

Nothing downstream loses anything: `k` is the RESIDUE field of the deformation
problem, and every consumer of this module in the chain that reaches
`exists_finiteIndex_isIntegral_charpolyCoeff_of_isHardlyRamified` already
carries `[Finite k]` (and `[DiscreteTopology k]`) in its own binder list. The
only declaration that had to grow the binder is the four-line wrapper
`exists_isWeaklyUniversal_hilbertDeformationDatum` below, which is where this
theorem is applied; the arithmetic-free machine leaf
`exists_isWeaklyUniversal_hilbertDeformationDatum_of_clauses` still takes the
GENERAL clause as its hypothesis and is untouched. -/
theorem isHilbertResidualRigidityClause (F : Type u) [Field F] [NumberField F]
    {k : Type u} [Field k] [Finite k] [TopologicalSpace k]
    {V : Type v} [AddCommGroup V] [Module k V] [Module.Finite k V]
    [Module.Free k V] (ρbar : GaloisRep ℚ k V) :
    IsHilbertResidualRigidityClause F ρbar := by
  intro hrank hirrF τ hcp
  have hfrV : Module.finrank k V = 2 :=
    Module.finrank_eq_of_rank_eq (by exact_mod_cast hrank)
  have hfrW : Module.finrank k (Fin 2 → k) = 2 := by simp
  obtain ⟨e, he⟩ := exists_linearEquiv_of_charpoly_eq hfrV hfrW
    (ρbar.map (algebraMap ℚ F)).toRepresentation τ.toRepresentation hirrF hcp
  refine ⟨e, GaloisRep.ext fun σ => LinearMap.ext fun x => ?_⟩
  have h1 : e (τ σ (e.symm x)) = (ρbar.map (algebraMap ℚ F)) σ (e (e.symm x)) :=
    he σ (e.symm x)
  rw [e.apply_symm_apply] at h1
  calc (τ.conj e) σ x = (e.conj (τ σ)) x := by rw [GaloisRep.conj_apply]
    _ = e (τ σ (e.symm x)) := by rw [LinearEquiv.conj_apply]; rfl
    _ = (ρbar.map (algebraMap ℚ F)) σ x := h1

/-! #### The CONSTRUCTION / FINITENESS / LIMIT cut of the Schlessinger machine

(2026-07-26.) `exists_isWeaklyUniversal_hilbertDeformationDatum_of_clauses`
below is now PROVEN as the bridge of the three-way cut that
`Deformation.lean` makes at the `ℚ` level, and that this section mirrors
declaration for declaration:

* `exists_universalFrame_profinite_hilbert_of_clauses` (LEAF) — the
  CONSTRUCTION. Schlessinger's inductive small-extension argument over the
  four clauses, delivered over a coefficient ring that is only PROFINITE
  (compact, Hausdorff, open ideals a neighbourhood basis of `0`), together
  with the two clauses a limit construction naturally supplies:
  hardly ramifiedness at every FINITE DISCRETE level, and minimality in the
  form "distinct `π`-compatible continuous points give distinct frames".
  The `ℚ`-level twin is `exists_universalFrame_profinite_of_deformationCondition`.
* `ProfiniteLocalNoetherian.isNoetherianRing_isAdic_of_profinite_of_finite_ringHom`
  (PROVEN, upstream) — the FINITENESS. Mazur's `Φ_ℓ` criterion, pure
  commutative algebra: a profinite local ring with finitely many
  `π`-compatible continuous points in every finite discrete local test ring
  is Noetherian, maximal-adic and maximal-adically complete.
* `HilbertDeformationDatum.isWeaklyUniversal_of_finiteFrames` (LEAF) — the
  LIMIT passage, from the finite discrete test objects the construction
  classifies to the whole of Mazur's category. The `ℚ`-level twin is
  `isWeaklyUniversalOnIdentifiedFrames_of_finite`.

and the assembly below is where `hfin` and `hlim` are actually spent:
`hfin` bounds the hardly ramified frames over each finite discrete test
ring, the minimality clause injects the continuous points of `R` into
those frames, whence the `Φ_ℓ` criterion applies; and `hlim` upgrades the
finite levels of `ρuniv` — the quotients `R ⧸ I` at open `I`, finite
because `R` is compact and `I` open — to hardly ramifiedness over `R`
itself, which is the last field `HilbertDeformationDatum` needs.

WHY THE LIMIT PASSAGE IS EASIER HERE THAN OVER `ℚ`. The `ℚ`-level leaf
`isWeaklyUniversalOnIdentifiedFrames_of_finite` records that its Kőnig
step does not go through directly, because the classifying datum there is
a PAIR `(ψₙ, eₙ)` whose second component's type depends on the first
(the algebra structure used to form the base change is `ψₙ.toAlgebra`), so
the inverse system is one of Σ-types. Here `IsWeaklyUniversal` is
CHARPOLY-ONLY: the datum at level `n` is a bare ring homomorphism
`ψₙ : 𝒟.R →+* 𝒟'.R ⧸ 𝔪'ⁿ` subject to an equation, an element of a type not
depending on anything, so Kőnig applies to the plain product and
`IsAdicComplete.liftRingHom` assembles the tower. That is why no
`framePushforward`-transport lemma is cut out here. -/

/-- **Weak universality on FINITE DISCRETE framed test objects, on a RAW
package** — the `F`-level, charpoly-only analogue of `Deformation.lean`'s
`IsStrictlyUniversalOnFrames`, with the bundled datum `𝒟` replaced by the
unbundled data `(R, ρuniv, πuniv)` it is tested through.

It is phrased on the raw package because the Schlessinger construction
produces `R` BEFORE `R` is known to be an object of Mazur's category:
`HilbertDeformationDatum` demands `IsNoetherianRing`, `IsAdic` and
`IsAdicComplete`, which are exactly what the finiteness half of the cut
supplies afterwards. The bundled form is `IsHilbertWeaklyUniversalOnFiniteFrames
ℓ F ρbar 𝒟.ρ 𝒟.π`, which is how the limit leaf below states its
hypothesis — one predicate, used in both places, so the two cannot drift.

The test objects carry `[Finite A]` and `[DiscreteTopology A]` for the
same reason as their `ℚ`-level twins: those are precisely the binders of
`IsHilbertFiniteFramesClause`, and a merely finite (possibly
non-Hausdorff) `A` would let discontinuous derivations masquerade as
continuous ring maps — see the STATEMENT REPAIR paragraph on
`exists_universalFrame_profinite_of_deformationCondition`.

The residual condition asked of a test object is charpoly agreement with
`ρbar|_{G_F}`, exactly the `resid` field of `HilbertDeformationDatum`, so
that the limit leaf can feed an arbitrary object's finite levels to it
with no Brauer–Nesbitt matching in between: the conjugation is already
absorbed into the construction leaf, through `hrig`. -/
def IsHilbertWeaklyUniversalOnFiniteFrames (ℓ : ℕ) [Fact ℓ.Prime]
    (F : Type u) [Field F] [NumberField F]
    {k : Type u} [Field k] [TopologicalSpace k]
    {V : Type v} [AddCommGroup V] [Module k V] [Module.Finite k V]
    [Module.Free k V] (ρbar : GaloisRep ℚ k V)
    {R : Type u} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    [IsLocalRing R] [Algebra ℤ_[ℓ] R]
    (ρuniv : FramedGaloisRep F R (Fin 2)) (πuniv : R →+* k) : Prop :=
  ∀ (A : Type u) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [IsLocalRing A] [Algebra ℤ_[ℓ] A] [Finite A] [DiscreteTopology A]
    (ρA : FramedGaloisRep F A (Fin 2)),
    IsHilbertHardlyRamified ℓ F (rank_finTwoPi A) ρA →
    ∀ πA : A →+* k, Function.Surjective πA →
    (∀ g : Γ F, ((ρA g).charpoly).map πA =
      ((ρbar.map (algebraMap ℚ F)) g).charpoly) →
    ∃ ψ : R →+* A, Continuous ψ ∧
      ψ.comp (algebraMap ℤ_[ℓ] R) = algebraMap ℤ_[ℓ] A ∧
      πA.comp ψ = πuniv ∧
      ∀ g : Γ F, ((ρuniv g).charpoly).map ψ = (ρA g).charpoly

/-- **Pro-representability of the `F`-level hardly ramified deformation
problem by a PROFINITE ring** (LEAF — the CONSTRUCTION half of the
2026-07-26 cut; the `F`-level twin of `Deformation.lean`'s
`exists_universalFrame_profinite_of_deformationCondition`).

Everything Schlessinger's machine constructs, delivered over a ring that
is only assumed PROFINITE — compact, Hausdorff, with the open ideals a
neighbourhood basis of `0` — rather than Noetherian: the universal framed
representation `ρuniv`, the surjective continuous reduction `πuniv` whose
charpolys are those of `ρbar|_{G_F}`, and weak universality on finite
discrete framed test objects. That is exactly what an inverse limit of the
finite levels gives, and all a construction can give without a separate
finiteness argument, an inverse limit of finite local rings being in
general NOT Noetherian.

THE TWO EXTRA CLAUSES, and why they belong here rather than downstream:

* `hquot` — every continuous `ℤ_ℓ`-algebra map of `R` into a FINITE
  DISCRETE local ring carries `ρuniv` to a hardly ramified frame. These
  are the finite levels of the construction, and they are what the
  pro-limit clause `hlim` consumes in the assembly below (through
  `I ↦ R ⧸ I`, whose finiteness is compactness plus openness of `I`). It
  does NOT say `ρuniv` itself is hardly ramified: that is exactly what
  `hlim` is for, and asserting it here would make `hlim` unused.
* `hinj` — two `πuniv`-compatible continuous points of `R` in a finite
  discrete local ring carrying `ρuniv` to the SAME framed representation
  are equal. This is minimality, and it is what converts the
  restricted-ramification finiteness `hfin` into finiteness of the point
  sets of `R`, i.e. into the hypothesis of Mazur's `Φ_ℓ` criterion.
  Without it the Noetherian upgrade would be FALSE rather than merely
  unproven: the naive inverse limit over ALL test objects surjects onto
  everything and is wildly non-Noetherian.

WHAT IS AND IS NOT IN THIS LEAF. In: Schlessinger's inductive
small-extension argument over H1–H3 (`hglue` supplies H1 and H2, `hfin`
H3), the directed system of finite test objects and the passage to its
inverse limit, and the conjugation of a test object's residual frame onto
the frame the machine deforms, supplied by `hrig`. No H4/Schur input is
needed: FRAMED deformations have no automorphisms, and
`IsHilbertWeaklyUniversalOnFiniteFrames` asks only for the EXISTENCE of a
classifying map, i.e. versality, so a hull suffices. Out: (i) the
Noetherian/`IsAdic`/`IsAdicComplete` upgrade, which is the upstream pure
commutative algebra
`ProfiniteLocalNoetherian.isNoetherianRing_isAdic_of_profinite_of_finite_ringHom`;
(ii) the pro-limit clause `hlim`; (iii) the passage from the finite
discrete levels to the whole category, the separate leaf
`HilbertDeformationDatum.isWeaklyUniversal_of_finiteFrames`; (iv) every
arithmetic statement about `IsHilbertHardlyRamified`, which enters only
through `hbase`, `hglue`, `hfin` and `hrig`.

WHY `𝒟₀`. It is Schlessinger's "`F(k)` is a point": the nonemptiness of
the category. It pins `Module.rank k V = 2` (through
`rank_eq_two_of_hilbertDeformationDatum`, which is what feeds `hrig`) and
it exhibits the residual frame the machine deforms. Without it the
statement is FALSE — see the faithfulness repair recorded above.

A prover who finds it more convenient to build `R` directly as a quotient
of `Λ[[x₁, …, x_g]]` (the de Smit–Lenstra presentation) may of course do
so and read the profinite clauses off the presentation.

CIRCULARITY GUARD (inherited): nothing from `Family.lean`, `Lift.lean`,
`Modularity/*` or `Deformation.lean` may be imported to discharge this;
in particular the odd-prime dichotomy
`not_isIrreducible_of_isHardlyRamified_of_five_le`, under whose hypotheses
this node would be vacuous, is proven over pillar α, which is proven over
this node.

References: Schlessinger, *Functors of Artin rings*, Trans. AMS 130
(1968), Thm. 2.11; Mazur, *Deforming Galois representations*, MSRI Publ.
16 (1989), §1.2; de Smit–Lenstra, *Explicit construction of universal
deformation rings*, Prop. 2.3. -/
theorem exists_universalFrame_profinite_hilbert_of_clauses
    (ℓ : ℕ) [Fact ℓ.Prime] (F : Type u) [Field F] [NumberField F]
    {k : Type u} [Field k] [Finite k] [TopologicalSpace k]
    [DiscreteTopology k] [Algebra ℤ_[ℓ] k]
    {V : Type v} [AddCommGroup V] [Module k V] [Module.Finite k V]
    [Module.Free k V]
    {ρbar : GaloisRep ℚ k V}
    (hirrF : (ρbar.map (algebraMap ℚ F)).IsIrreducible)
    (𝒟₀ : HilbertDeformationDatum ℓ F ρbar)
    (hbase : IsHilbertBaseChangeClause ℓ F)
    (hglue : IsHilbertFibreProductClause ℓ F)
    (hfin : IsHilbertFiniteFramesClause ℓ F)
    (hrig : IsHilbertResidualRigidityClause F ρbar) :
    ∃ (R : Type u) (_ : CommRing R) (_ : TopologicalSpace R)
      (_ : IsTopologicalRing R) (_ : IsLocalRing R) (_ : Algebra ℤ_[ℓ] R)
      (_ : CompactSpace R) (_ : T2Space R)
      (ρuniv : FramedGaloisRep F R (Fin 2))
      (πuniv : R →+* k) (_ : Function.Surjective πuniv)
      (_ : Continuous πuniv),
      (∀ U ∈ nhds (0 : R), ∃ I : Ideal R, IsOpen (I : Set R) ∧
        (I : Set R) ⊆ U) ∧
      (∀ g : Γ F, ((ρuniv g).charpoly).map πuniv =
        ((ρbar.map (algebraMap ℚ F)) g).charpoly) ∧
      (∀ (A : Type u) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
        [IsLocalRing A] [Algebra ℤ_[ℓ] A] [Finite A] [DiscreteTopology A]
        (φ : R →+* A) (hφ : Continuous φ),
        φ.comp (algebraMap ℤ_[ℓ] R) = algebraMap ℤ_[ℓ] A →
        IsHilbertHardlyRamified ℓ F (rank_finTwoPi A)
          (framePushforward φ hφ ρuniv)) ∧
      (∀ (A : Type u) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
        [IsLocalRing A] [Algebra ℤ_[ℓ] A] [Finite A] [DiscreteTopology A]
        (πA : A →+* k) (φ₁ φ₂ : R →+* A)
        (hφ₁ : Continuous φ₁) (hφ₂ : Continuous φ₂),
        πA.comp φ₁ = πuniv → πA.comp φ₂ = πuniv →
        framePushforward φ₁ hφ₁ ρuniv = framePushforward φ₂ hφ₂ ρuniv →
        φ₁ = φ₂) ∧
      IsHilbertWeaklyUniversalOnFiniteFrames ℓ F ρbar ρuniv πuniv :=
  sorry

/-- **From the finite discrete levels to the whole of Mazur's category**
(LEAF — the LIMIT half of the 2026-07-26 cut; the `F`-level twin of
`Deformation.lean`'s `isWeaklyUniversalOnIdentifiedFrames_of_finite`): a
datum that classifies every FINITE DISCRETE framed test object classifies
every datum.

THE ARGUMENT, which is the one that file's docstring lays out, simplified
by this module's charpoly-only formulation. Let `𝒟'` be an arbitrary
datum and `J = 𝔪_{𝒟'.R}`.

1. Each level `𝒟'.R ⧸ Jⁿ` is FINITE — `𝒟'.π` is a surjection onto the
   finite `k` with kernel `J`, so `natCast`-counting gives `|𝒟'.R ⧸ Jⁿ| ≤
   |k|ⁿ` (`finite_quotient_of_maximalIdeal_pow_le`) — and DISCRETE,
   because `𝒟'.isAdic` makes `Jⁿ` open and the quotient map is open. It is
   local, a `ℤ_ℓ`-algebra, and it carries the pushforward of `𝒟'.ρ`, which
   is hardly ramified by the functoriality clause and reduces to
   `ρbar|_{G_F}` because `𝒟'.resid` does.
2. So the hypothesis produces, for each `n`, a nonempty FINITE set of
   classifying maps `ψ : 𝒟.R →+* 𝒟'.R ⧸ Jⁿ` (finiteness: a compatible `ψ`
   is determined by its values, and `Patching.lean`'s
   `finite_setOf_ringHom_comp_eq` over `Ideal.finite_quotient_pow` bounds
   them).
3. The truncations `𝒟'.R ⧸ J^{n+1} ↠ 𝒟'.R ⧸ Jⁿ` make those sets an
   inverse system of nonempty finite sets, so Kőnig's lemma
   (`nonempty_sections_of_finite_inverse_system`) gives a COMPATIBLE tower
   `(ψₙ)`. Unlike the `ℚ`-level twin the system is NOT one of Σ-types —
   the classifying datum here is a bare ring homomorphism — so the lemma
   applies to it directly.
4. `IsAdicComplete.liftRingHom` assembles the tower into
   `f : 𝒟.R →+* 𝒟'.R` with `(Ideal.Quotient.mk Jⁿ).comp f = ψₙ`, and the
   three conclusions of `IsWeaklyUniversal` follow from the corresponding
   level-wise statements by adic separatedness of `𝒟'.R`
   (`IsHausdorff.haus`), the charpoly clause coefficient by coefficient.

CIRCULARITY GUARD (inherited): as for the construction leaf. -/
theorem HilbertDeformationDatum.isWeaklyUniversal_of_finiteFrames
    {ℓ : ℕ} [Fact ℓ.Prime] {F : Type u} [Field F] [NumberField F]
    {k : Type u} [Field k] [Finite k] [TopologicalSpace k]
    [DiscreteTopology k]
    {V : Type v} [AddCommGroup V] [Module k V] [Module.Finite k V]
    [Module.Free k V]
    {ρbar : GaloisRep ℚ k V}
    (hbase : IsHilbertBaseChangeClause ℓ F)
    (𝒟 : HilbertDeformationDatum ℓ F ρbar)
    (h𝒟 : IsHilbertWeaklyUniversalOnFiniteFrames ℓ F ρbar 𝒟.ρ 𝒟.π) :
    𝒟.IsWeaklyUniversal :=
  sorry

/-- **Existence of the `F`-level universal deformation ring `R_F`, over the
deformation-condition package** (item 2 of the audit's missing-machinery
list; PROVEN 2026-07-26 as the ASSEMBLY of the three-way
construction/finiteness/limit cut described in the section header above,
after the SECOND FAITHFULNESS REPAIR recorded below. This is the
ARITHMETIC-FREE half of item 2: it contains no statement about
`IsHilbertHardlyRamified`, which enters only through the five clauses.)

Mazur's representability theorem for the hardly ramified deformation
problem over the totally real field `F`, for a residually IRREDUCIBLE
`ρbar|_{G_F}`. GIVEN that the local conditions of `IsHilbertHardlyRamified`
form a deformation condition in the sense of Mazur §§18–23 /
Conrad–Diamond–Taylor §2 (the four clauses `hbase`, `hglue`, `hfin`,
`hlim`) and that the residual frame is rigid (`hrig`), Schlessinger's
theorem produces a hull; the FRAMED functor needs no H4, since framed
deformations have no automorphisms, so `IsWeaklyUniversal` — which asks
only for the EXISTENCE of a classifying map, i.e. versality — follows from
the hull without an irreducibility input beyond `hrig`.

WHERE EACH HYPOTHESIS IS SPENT, since the point of the cut is that none of
them is spent twice. `hirrF`, `𝒟₀`, `hbase`, `hglue` and `hrig` go into
the construction leaf and are not touched here. `hfin` is used TWICE and
for two different purposes: once inside the construction (Schlessinger's
H3) and once here, to bound the `πuniv`-compatible continuous points of
`R` in each finite discrete test ring — that is the hypothesis of Mazur's
`Φ_ℓ` criterion, and the minimality clause `hinj` of the construction leaf
is what turns the frame bound into a point bound. `hlim` is used only
here, to upgrade the finite levels of `ρuniv` to hardly ramifiedness over
`R` itself, which is the last field `HilbertDeformationDatum` needs.
`hbase` is passed on once more, to the limit leaf, which needs it to know
that the finite levels of an ARBITRARY datum are hardly ramified.

**SECOND FAITHFULNESS REPAIR (2026-07-26): `k` NOW CARRIES `[Finite k]`,
`[DiscreteTopology k]` AND `[Algebra ℤ_[ℓ] k]`.** The statement as first
written imposed nothing on the residual coefficient field beyond
`[Field k] [TopologicalSpace k]`, and in that generality it is not Mazur's
theorem and cannot be proven by Mazur's argument: the whole finiteness
half of the proof — Mazur's `Φ_ℓ` criterion, i.e. the upstream
`ProfiniteLocalNoetherian.isNoetherianRing_isAdic_of_profinite_of_finite_ringHom`
— is spent at the dual-number test ring `k[ε]`, which is a legitimate
(finite, discrete, local) test object exactly when `k` is a finite
discrete `ℤ_ℓ`-algebra. Over an infinite residue field the tangent space
need not be finite-dimensional over `ℤ_ℓ`, the pro-object of the
construction need not be Noetherian, and `HilbertDeformationDatum`
REQUIRES `IsNoetherianRing` of its coefficient ring — so the category can
fail to contain any versal object at all while every hypothesis of the
un-narrowed statement holds. (This is not backed here by an explicit
counterexample, so it is recorded as an under-hypothesis rather than as a
refutation; what IS mechanical is that the three instances are exactly
what the `ℚ`-level twin carries — `Deformation.lean`'s variable block has
`[Finite k] [Algebra ℤ_[ℓ] k] [DiscreteTopology k]` in force over the
whole of its deformation-theoretic development — and that without them the
`Φ_ℓ` criterion does not typecheck.)

The narrowing costs the consumer NOTHING: the sole consumer of this node's
assembly, `exists_finiteIndex_isIntegral_charpolyCoeff_of_isHardlyRamified`
at the bottom of this module, already assumes `[Finite k]`,
`[DiscreteTopology k]` and `[Algebra ℤ_[ℓ] k]` on its residual field, as
does every `ℚ`-level statement it is called from. Adding hypotheses that
the only caller already supplies cannot make anything downstream
unprovable.

WHY `𝒟₀`. It is the nonemptiness of the category, i.e. Schlessinger's
"`F(k)` is a point": it supplies the residual frame that the machine
deforms and it pins `finrank k V = 2`. Without it the statement is FALSE —
see the first faithfulness repair recorded above.

`Deformation.lean` carries the whole of this argument over `ℚ`, as the
PROVEN assembly `exists_isWeaklyUniversalOnIdentifiedFrames` over the same
construction/finiteness split, but that development is downstream of this
module and specific to the `ℚ`-level conditions, so it cannot be reused
here; its architecture is what this section mirrors declaration for
declaration.

CIRCULARITY GUARD (inherited). Nothing from `Family.lean`, `Lift.lean`,
`Modularity/*` or `Deformation.lean` may be imported to discharge the
leaves below; in particular the odd-prime dichotomy
`not_isIrreducible_of_isHardlyRamified_of_five_le`, under whose hypotheses
this node would be vacuous, is proven over pillar α, which is proven over
this node.

References: Schlessinger, *Functors of Artin rings*, Trans. AMS 130 (1968),
Thm. 2.11; Mazur, *Deforming Galois representations*, MSRI Publ. 16 (1989),
§1.2; de Smit–Lenstra, *Explicit construction of universal deformation
rings*, Prop. 2.3; Barnet-Lamb–Gee–Geraghty–Taylor, *Potential automorphy
and change of weight*, §1 (the `F`-level ring in the shape used here). -/
theorem exists_isWeaklyUniversal_hilbertDeformationDatum_of_clauses
    (ℓ : ℕ) [Fact ℓ.Prime] (F : Type u) [Field F] [NumberField F]
    {k : Type u} [Field k] [Finite k] [TopologicalSpace k]
    [DiscreteTopology k] [Algebra ℤ_[ℓ] k]
    {V : Type v} [AddCommGroup V] [Module k V] [Module.Finite k V]
    [Module.Free k V]
    {ρbar : GaloisRep ℚ k V}
    (hirrF : (ρbar.map (algebraMap ℚ F)).IsIrreducible)
    (𝒟₀ : HilbertDeformationDatum ℓ F ρbar)
    (hbase : IsHilbertBaseChangeClause ℓ F)
    (hglue : IsHilbertFibreProductClause ℓ F)
    (hfin : IsHilbertFiniteFramesClause ℓ F)
    (hlim : IsHilbertProLimitClause ℓ F)
    (hrig : IsHilbertResidualRigidityClause F ρbar) :
    ∃ 𝒟 : HilbertDeformationDatum ℓ F ρbar, 𝒟.IsWeaklyUniversal := by
  classical
  obtain ⟨R, iCR, iTS, iTR, iLR, iAlg, iCompact, iT2, ρuniv, πuniv, hπsurj,
      hπcont, hbasis, hres, hquot, hinj, huniv⟩ :=
    exists_universalFrame_profinite_hilbert_of_clauses ℓ F hirrF 𝒟₀ hbase
      hglue hfin hrig
  -- **The `πuniv`-compatible continuous points of `R` in a finite DISCRETE
  -- test ring are finite in number**: they inject, by the minimality clause
  -- `hinj`, into the hardly ramified frames over that ring, of which `hfin`
  -- gives finitely many. This is the hypothesis of Mazur's `Φ_ℓ` criterion.
  have hhom : ∀ (A : Type u) [CommRing A] [TopologicalSpace A]
      [IsTopologicalRing A] [IsLocalRing A] [Algebra ℤ_[ℓ] A] [Finite A]
      [DiscreteTopology A] (πA : A →+* k),
      {φ : R →+* A | Continuous φ ∧ πA.comp φ = πuniv ∧
        φ.comp (algebraMap ℤ_[ℓ] R) = algebraMap ℤ_[ℓ] A}.Finite := by
    intro A _ _ _ _ _ _ _ πA
    rw [← Set.finite_coe_iff]
    haveI : Finite {ρ : FramedGaloisRep F A (Fin 2) |
        IsHilbertHardlyRamified ℓ F (rank_finTwoPi A) ρ} := (hfin A).to_subtype
    refine Finite.of_injective
      (fun φ : {φ : R →+* A | Continuous φ ∧ πA.comp φ = πuniv ∧
          φ.comp (algebraMap ℤ_[ℓ] R) = algebraMap ℤ_[ℓ] A} =>
        (⟨framePushforward φ.1 φ.2.1 ρuniv, hquot A φ.1 φ.2.1 φ.2.2.2⟩ :
          {ρ : FramedGaloisRep F A (Fin 2) |
            IsHilbertHardlyRamified ℓ F (rank_finTwoPi A) ρ})) ?_
    intro φ₁ φ₂ heq
    exact Subtype.ext (hinj A πA φ₁.1 φ₂.1 φ₁.2.1 φ₂.2.1 φ₁.2.2.1 φ₂.2.2.1
      (congrArg Subtype.val heq))
  -- **Mazur's `Φ_ℓ` criterion** turns that finiteness into the three
  -- Mazur-category ring clauses.
  obtain ⟨iNoeth, hadic, hcomplete⟩ :=
    _root_.ProfiniteLocalNoetherian.isNoetherianRing_isAdic_of_profinite_of_finite_ringHom
      hbasis πuniv hπsurj hπcont hhom
  haveI := iNoeth
  -- **Hardly ramifiedness of the universal representation**, from its finite
  -- levels: for `I` open the quotient `R ⧸ I` is discrete (the quotient map
  -- is open) and compact, hence finite, so `hquot` applies to it and `hlim`
  -- assembles the levels.
  have hHR : IsHilbertHardlyRamified ℓ F (rank_finTwoPi R) ρuniv := by
    refine hlim hadic hcomplete ?_
    intro I hI _ hmk
    haveI : DiscreteTopology (R ⧸ I) := by
      rw [discreteTopology_iff_isOpen_singleton_zero]
      have hzero : ({0} : Set (R ⧸ I)) = Ideal.Quotient.mk I '' (I : Set R) := by
        ext x
        constructor
        · rintro rfl
          exact ⟨0, I.zero_mem, map_zero _⟩
        · rintro ⟨y, hy, rfl⟩
          exact (Ideal.Quotient.eq_zero_iff_mem).mpr hy
      rw [hzero]
      exact (QuotientRing.isOpenQuotientMap_mk I).isOpenMap _ hI
    haveI : Finite (R ⧸ I) := finite_of_compact_of_discrete
    exact hquot (R ⧸ I) (Ideal.Quotient.mk I) hmk rfl
  -- **The datum**: the profinite package upgraded by the two steps above is
  -- an object of Mazur's `F`-level category.
  refine ⟨{ R := R
            isAdic := hadic
            isAdicComplete := hcomplete
            ρ := ρuniv
            isHilbertHardlyRamified := hHR
            π := πuniv
            π_surjective := hπsurj
            resid := hres }, ?_⟩
  -- **Weak universality**, by the limit passage from the finite levels.
  exact HilbertDeformationDatum.isWeaklyUniversal_of_finiteFrames hbase _ huniv

/-- **Existence of the `F`-level universal deformation ring `R_F`** (item 2
of the audit's missing-machinery list; PROVEN 2026-07-26 as an ASSEMBLY
over the six leaves above, after the FAITHFULNESS REPAIR recorded at the
head of this section — the statement previously carried no `𝒟₀` and was
FALSE, refuted by `rank_eq_two_of_hilbertDeformationDatum`).

The cut is the `ℚ`-level one: the Schlessinger machine
(`exists_isWeaklyUniversal_hilbertDeformationDatum_of_clauses`, which
contains no arithmetic) over the four clauses that make
`IsHilbertHardlyRamified` a deformation condition, plus residual
rigidity.

`k` carries `[Finite k]`, `[DiscreteTopology k]` and `[Algebra ℤ_[ℓ] k]`.
`[Finite k]` (added 2026-07-26 with the proof of
`isHilbertResidualRigidityClause`, which is the only place it is used) is the
hypothesis under which the residual-rigidity clause is discharged; see that
theorem's docstring for why the available dimension-`2` Brauer–Nesbitt core
needs it and why no consumer loses anything — the residue field of the
deformation problem is finite in every consumer of this module. The other
two come by inheritance from the machine node, whose SECOND FAITHFULNESS
REPAIR (2026-07-26) added them. The consumer at the bottom of this module
already assumes all three, so nothing downstream changes.

**`hℓ5 : 5 ≤ ℓ` (added 2026-07-26) IS LOAD-BEARING AND IS SPENT ON THE
GLUING CLAUSE**, exactly as at the `ℚ` level. It reaches this assembly from
`isHilbertFibreProductClause`, whose tame-at-`2` residue is FALSE at
`ℓ = 3` — see the faithfulness repair recorded on that theorem, and the
explicit counterexample it points at. Nothing else here needs it, and the
consumer at the bottom of this module,
`exists_finiteIndex_isIntegral_charpolyCoeff_of_isHardlyRamified`, already
carried `5 ≤ ℓ`, so the hypothesis costs nothing downstream. -/
theorem exists_isWeaklyUniversal_hilbertDeformationDatum
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ5 : 5 ≤ ℓ)
    (F : Type u) [Field F] [NumberField F]
    {k : Type u} [Field k] [Finite k] [TopologicalSpace k]
    [DiscreteTopology k] [Algebra ℤ_[ℓ] k]
    {V : Type v} [AddCommGroup V] [Module k V] [Module.Finite k V]
    [Module.Free k V]
    {ρbar : GaloisRep ℚ k V}
    (hirrF : (ρbar.map (algebraMap ℚ F)).IsIrreducible)
    (𝒟₀ : HilbertDeformationDatum ℓ F ρbar) :
    ∃ 𝒟 : HilbertDeformationDatum ℓ F ρbar, 𝒟.IsWeaklyUniversal :=
  exists_isWeaklyUniversal_hilbertDeformationDatum_of_clauses ℓ F hirrF 𝒟₀
    (isHilbertBaseChangeClause ℓ F) (isHilbertFibreProductClause ℓ hℓ5 F)
    (isHilbertFiniteFramesClause ℓ F) (isHilbertProLimitClause ℓ F)
    (isHilbertResidualRigidityClause F ρbar)

/-! ### Items 3 and 5 — the Hecke algebra `T_F` and potential modularity -/

/-- **The Hecke algebra `T_F` of Hilbert modular forms over `F`**
(interface structure): the `ℤ_ℓ`-algebra generated by the Hecke operators
`T_w` at the places `w` away from a finite bad set, acting on the space
of Hilbert modular forms over `F` of parallel weight `2` and fixed level,
localized at the maximal ideal attached to `ρbar|_{G_F}`.

The components that carry the arithmetic:

* the instance fields `moduleFinite` and `moduleFree`, i.e. **`T` is a
  finite FREE `ℤ_[ℓ]`-module**, together with `IsLocalRing T`. Finiteness
  is the item `Modularity/Patching.lean` takes as a HYPOTHESIS and that
  nothing in the repository supplies; classically it holds because the
  space of Hilbert modular forms of fixed weight and level is a finitely
  generated `ℤ_ℓ`-module on which `T` acts faithfully, and freeness because
  `T` is then a torsion-free finitely generated module over a PID. Freeness
  is not decoration — see the vacuity audit below, where it is what
  distinguishes a Hecke algebra from its own residue ring.
* `adjoin_heckeT` — `T` is generated over `ℤ_ℓ` by the good-place Hecke
  operators. Without it the structure would be inhabited by `ℤ_ℓ` itself
  with `heckeT` arbitrary, and would record nothing.
* `ρT`, `charFrobT` and `residT` — **modularity of `ρbar|_{G_F}`** in the
  only form that has content: a hardly ramified `ρT : G_F → GL₂(T)` in
  characteristic zero whose Frobenius traces are the Hecke operators and
  which reduces to `ρbar|_{G_F}` along `πT`. The clause that used to stand
  here, `residualT` (the reduced eigensystem is the system of Frobenius
  traces of `ρbar|_{G_F}`), is now the PROVEN lemma of that name below;
  `−(charFrob w).coeff 1` is the trace of Frobenius at `w`, the `charFrob`
  being monic of degree `2`.

No non-degeneracy clause is imposed on `bad`: every statement here
quantifies over places OUTSIDE `bad`, so a larger bad set is a weaker
datum, which is the direction that keeps the production leaf honest.

## VACUITY AUDIT (2026-07-26) — the first form of this structure was EMPTY

As first written this structure had exactly the fields `T`, `[CommRing T]`,
`[Algebra ℤ_[ℓ] T]`, `[Module.Finite ℤ_[ℓ] T]`, `bad`, `heckeT`,
`adjoin_heckeT`, `πT`, `residualT`. In that form it recorded **no
automorphic content whatsoever**: it is inhabited for EVERY number field
`F` and EVERY `ρbar` with finite coefficient field, by the junk witness

* `T := Algebra.adjoin ℤ_[ℓ] (Set.range t) ⊆ k`, where
  `t w = -((ρbar.map (algebraMap ℚ F)).charFrob w).coeff 1`;
* `bad := ∅`, `heckeT w := ⟨t w, Algebra.subset_adjoin ⟨w, rfl⟩⟩`,
  `πT := Subalgebra.val`.

`Module.Finite ℤ_[ℓ] T` is FREE for that witness, because `T ⊆ k` is a
finite set and `Module.Finite.of_finite` is an instance — i.e. the
finiteness clause, the one this structure exists to carry, is satisfied by
a **residual** (`ℓ`-torsion) ring; `adjoin_heckeT` is
`Algebra.adjoin_adjoin_coe_preimage`, and `residualT` is `rfl`. The witness
was written out in Lean and compiled against this file's imports before the
repair below was made; it is not a sketch.

Consequences, which is why this was repaired rather than exploited:
`nonempty_potentialHeckeDatum_of_five_le` would have been a leaf with no
content — a leaf that looks stronger than it is — and the ENTIRE modularity
burden of the cluster would have sat silently on
`exists_heckeAlgebra_algEquiv_of_isWeaklyUniversal`, which, given a vacuous
`T₀`, would be asked to prove `Module.Finite ℤ_[ℓ] R_F` with no automorphic
input at all. That is exactly the circularity this module was built to
avoid.

**The repair.** Three instance fields and four fields are added, and one
component (`residualT`) is REMOVED from what is assumed and proven instead
(`HilbertHeckeAlgebra.residualT` below):

* `[IsLocalRing T]` (hence `Nontrivial T`) and `[Module.Free ℤ_[ℓ] T]`.
  Together these kill the residual witness outright: a residual `T` is
  `ℓ`-torsion, hence not `ℤ_[ℓ]`-free unless trivial. `T` is now forced to
  be a nonzero finite FREE `ℤ_[ℓ]`-algebra, i.e. genuinely of
  characteristic zero — which is what a Hecke algebra of weight-`2` forms
  is, and what its `ℤ_[ℓ]`-finiteness is supposed to be a theorem about.
* `ρT`, `isHilbertHardlyRamified`, `charFrobT`, `residT` — the
  **Hecke-valued Galois representation** (Carayol; Taylor for Hilbert
  modular forms): a hardly ramified `ρT : G_F → GL₂(T)` whose Frobenius
  traces ARE the Hecke operators and whose reduction along `πT` has the
  characteristic polynomials of `ρbar|_{G_F}`. This is the component that
  makes the datum SAY modularity — `ρbar|_{G_F}` admits a hardly ramified
  characteristic-zero lift with coefficients in a finite flat `ℤ_[ℓ]`-
  algebra generated by its own Frobenius traces — and it is the component
  `exists_heckeAlgebra_algEquiv_of_isWeaklyUniversal`'s docstring already
  appealed to ("the traces of the deformation attached to the Hecke-valued
  representation") but which did not exist.

## FAITHFULNESS AUDIT (2026-07-26, second pass) — the residue field of `T`

The previous version of this docstring carried a paragraph headed **"Why NOT
`Function.Surjective πT`"**. It observed, correctly, that `k` may properly
contain the field generated by the Frobenius traces (`ρbar` defined over
`𝔽_ℓ` and viewed over `𝔽_{ℓ²}`, say), while `adjoin_heckeT` — as it then
stood, an `Algebra.adjoin ℤ_[ℓ]` of the Hecke operators ALONE — confines the
image of `πT` to the `ℤ_[ℓ]`-algebra generated by those traces; and it
concluded that surjectivity must therefore not be demanded, the residual-field
bookkeeping being left to consumers.

**That conclusion was wrong, and it made the consumer
`exists_heckeDatum_isWeaklyUniversal_isTraceGenerated` — the `R_F = T_F` leaf
below — FALSE as stated.** The bookkeeping it deferred cannot be supplied by
any consumer, because the consumer's conclusion is an ISOMORPHISM
`𝒟T.R ≃ₐ[ℤ_[ℓ]] T.T`, and an isomorphism identifies residue fields:

* `HilbertDeformationDatum` demands `π_surjective`, so `𝒟T.R` has residue
  field exactly `k`;
* under the old `adjoin_heckeT`, `Set.range πT` is the subring of `k`
  generated by the image of `ℤ_[ℓ]` together with the values
  `πT (heckeT w) = -((ρbar.map (algebraMap ℚ F)).charFrob w).coeff 1`
  (`HilbertHeckeAlgebra.residualT` below) — that is, the TRACE FIELD — and
  when `char k = ℓ` the kernel of `πT` is maximal (`T` is module-finite over
  `ℤ_[ℓ]`, so `Set.range πT` is an integral domain integral over the prime
  field `Set.range (πT.comp (algebraMap ℤ_[ℓ] T))`, hence itself a field), so
  the residue field of `T` IS the trace field.

So the isomorphism forces `k` to be the trace field. **Explicit
counterexample to the old form**, the very scenario the deleted paragraph
described: let `ρbar = ρ₀ ⊗ k` for an absolutely irreducible modular
`ρ₀ : G_ℚ → GL₂(𝔽_ℓ)` and `k = 𝔽_{ℓ²}`. Every hypothesis of the `R_F = T_F`
leaf holds — `ρbar` is irreducible over `k` and stays so over the
potentially-modular `F`, and the genuine Hecke algebra `𝕋_𝔪` over `ℤ_[ℓ]`,
with `πT : 𝕋_𝔪 ↠ 𝔽_ℓ ↪ 𝔽_{ℓ²}`, is a `HilbertHeckeAlgebra` in the old
sense — while the conclusion fails for EVERY `T`, since `𝒟T.R` has residue
field `𝔽_{ℓ²}` and every old-style `T` has residue field `𝔽_ℓ`.

**THE REPAIR, and why it is the one `IsTraceGenerated` already made.** Note
what the deleted paragraph's own diagnosis says: a `ℤ_[ℓ]`-algebra generated
by traces alone has the trace field as its residue field. That is verbatim
the defect recorded at `teichmullerRootSet` below and at the head of the
`R_F = T_F` section — "over `ℤ_ℓ` alone the residue field of the generated
subring is only the trace field of `ρbar`" — and it was repaired there, for
`HilbertDeformationDatum.IsTraceGenerated`, by putting the `ℓ`-power
TEICHMÜLLER ROOTS into the generating set. The same repair is made here, and
the two definitions now match clause for clause:

* `adjoin_heckeT` generates `T` over `ℤ_[ℓ]` from the Teichmüller roots
  TOGETHER WITH the good-place Hecke operators. Classically this replaces
  `𝕋_𝔪` by the local factor of `𝕋_𝔪 ⊗_{ℤ_[ℓ]} W(k)`, which is exactly the
  ring the deformation-theoretic `R = T` theorem is about: the deformation
  functor is taken on complete local `W(k)`-algebras with residue field `k`,
  so the Hecke side must be an unramified base change of the classical
  `ℤ_[ℓ]`-Hecke algebra. `W(k) = ℤ_[ℓ][ζ_{|k|-1}]` is generated by
  Teichmüller roots, so the local factor is generated over `ℤ_[ℓ]` by
  Teichmüller roots and Hecke operators, and it is still finite and free
  over `ℤ_[ℓ]`.
* `πT_surjective` is then CONSISTENT — it is what the weakened
  `adjoin_heckeT` makes room for — and it is what the isomorphism in the
  `R_F = T_F` leaf needs. It is not decoration: without it the leaf below is
  false, and with the old `adjoin_heckeT` it would have been contradictory.

The vacuity audit above survives the weakening unchanged: the residual junk
witness is killed by `[IsLocalRing T]` + `[Module.Free ℤ_[ℓ] T]`, not by
`adjoin_heckeT`, and the Hecke-valued `ρT` is untouched. What the weakening
costs is that `adjoin_heckeT` no longer pins `T` down to the trace algebra
over `ℤ_[ℓ]`; what it buys is that `T` may be the trace algebra over `W(k)`,
which is the object that is actually isomorphic to `R_F`. The production
leaf `nonempty_potentialHeckeDatum_of_five_le` remains classically TRUE
under both changes, and its statement is again unchanged. -/
structure HilbertHeckeAlgebra (ℓ : ℕ) [Fact ℓ.Prime]
    (F : Type u) [Field F] [NumberField F]
    {k : Type u} [Field k] [TopologicalSpace k]
    {V : Type v} [AddCommGroup V] [Module k V] [Module.Finite k V]
    [Module.Free k V]
    (ρbar : GaloisRep ℚ k V) where
  /-- The Hecke algebra. -/
  T : Type u
  [commRing : CommRing T]
  [topologicalSpace : TopologicalSpace T]
  [isTopologicalRing : IsTopologicalRing T]
  [isLocalRing : IsLocalRing T]
  [algebra : Algebra ℤ_[ℓ] T]
  [moduleFinite : Module.Finite ℤ_[ℓ] T]
  /-- `T` is `ℤ_[ℓ]`-FREE: with `IsLocalRing T` this is what forces the
  Hecke algebra to be of characteristic zero, and is what no residual junk
  witness can satisfy. -/
  [moduleFree : Module.Free ℤ_[ℓ] T]
  /-- The finite bad set: the level of the newform and the places over
  `2` and `ℓ`. -/
  bad : Finset (HeightOneSpectrum (𝓞 F))
  /-- The Hecke operator at a place. -/
  heckeT : HeightOneSpectrum (𝓞 F) → T
  /-- `T` is generated over `ℤ_ℓ` by the `ℓ`-power Teichmüller roots
  (`teichmullerRootSet ℓ T`, written out here because that definition lives
  below this structure) together with the good-place Hecke operators.

  The Teichmüller half was added 2026-07-26 by the FAITHFULNESS AUDIT above:
  over `ℤ_[ℓ]` and the Hecke operators alone the residue field of `T` is the
  trace field of `ρbar`, which makes `πT_surjective` — and with it the
  `R_F = T_F` leaf below — false whenever `k` properly contains that field.
  This is clause-for-clause the generating set of
  `HilbertDeformationDatum.IsTraceGenerated`. -/
  adjoin_heckeT : Algebra.adjoin ℤ_[ℓ]
    ({x : T | ∃ n : ℕ, 0 < n ∧ x ^ ℓ ^ n = x} ∪ heckeT '' {w | w ∉ bad}) = ⊤
  /-- The reduction map onto the residual coefficient field. -/
  πT : T →+* k
  /-- **`k` IS the residue field of `T`.** Added 2026-07-26 with the
  weakening of `adjoin_heckeT` above; the two changes stand or fall
  together, and without this one the `R_F = T_F` leaf below is FALSE (the
  isomorphism it asserts identifies the residue field of `T` with that of a
  deformation datum, which is `k` by `HilbertDeformationDatum.π_surjective`). -/
  πT_surjective : Function.Surjective πT
  /-- **The Hecke-valued Galois representation** `ρT : G_F → GL₂(T)`. -/
  ρT : FramedGaloisRep F T (Fin 2)
  /-- `ρT` satisfies the same `F`-level local conditions as the deformations
  of `ρbar|_{G_F}` — this is what pins the level and the weight of the
  Hilbert newform to the deformation problem. -/
  isHilbertHardlyRamified : IsHilbertHardlyRamified ℓ F (rank_finTwoPi T) ρT
  /-- **Hecke = Frobenius trace**: the Hecke operator at a good place is the
  trace of `ρT` at the Frobenius there (`charFrob` is monic of degree `2`,
  so its `coeff 1` is minus that trace). -/
  charFrobT : ∀ w ∉ bad, (ρT.charFrob w).coeff 1 = -heckeT w
  /-- **Residual modularity of `ρbar|_{G_F}`**: `ρT` reduces to it along
  `πT`, at every element of `G_F`. -/
  residT : ∀ g : Γ F, ((ρT g).charpoly).map πT =
    ((ρbar.map (algebraMap ℚ F)) g).charpoly

attribute [instance] HilbertHeckeAlgebra.commRing
  HilbertHeckeAlgebra.topologicalSpace HilbertHeckeAlgebra.isTopologicalRing
  HilbertHeckeAlgebra.isLocalRing
  HilbertHeckeAlgebra.algebra HilbertHeckeAlgebra.moduleFinite
  HilbertHeckeAlgebra.moduleFree

/-- **The reduced Hecke eigensystem is the system of Frobenius traces of
`ρbar|_{G_F}`** (PROVEN — this was a FIELD of the structure before the
vacuity audit above, and is now derived from `charFrobT` and `residT`; the
citation assumes one component fewer).

`charFrob w` is by definition the characteristic polynomial at the fixed
arithmetic Frobenius `Field.AbsoluteGaloisGroup.adicArithFrob w`, pulled
back along `F → F_w`, so `residT` at that ONE group element says exactly
that `ρT.charFrob w` reduces to `(ρbar|_{G_F}).charFrob w`; taking
`coeff 1` and feeding in `charFrobT` gives the eigenvalue statement. -/
lemma HilbertHeckeAlgebra.residualT {ℓ : ℕ} [Fact ℓ.Prime]
    {F : Type u} [Field F] [NumberField F]
    {k : Type u} [Field k] [TopologicalSpace k]
    {V : Type v} [AddCommGroup V] [Module k V] [Module.Finite k V]
    [Module.Free k V]
    {ρbar : GaloisRep ℚ k V} (H : HilbertHeckeAlgebra ℓ F ρbar)
    (w : HeightOneSpectrum (𝓞 F)) (hw : w ∉ H.bad) :
    H.πT (H.heckeT w) =
      -((ρbar.map (algebraMap ℚ F)).charFrob w).coeff 1 := by
  have key : (H.ρT.charFrob w).map H.πT = (ρbar.map (algebraMap ℚ F)).charFrob w :=
    H.residT (Field.absoluteGaloisGroup.map (algebraMap F (w.adicCompletion F))
      (Field.AbsoluteGaloisGroup.adicArithFrob w))
  have hc : H.πT ((H.ρT.charFrob w).coeff 1) =
      ((ρbar.map (algebraMap ℚ F)).charFrob w).coeff 1 := by
    rw [← key, Polynomial.coeff_map]
  have hh : H.heckeT w = -((H.ρT.charFrob w).coeff 1) := by
    rw [H.charFrobT w hw, neg_neg]
  rw [hh, map_neg, hc]

/-- **The potential-modularity package**: the totally real field `F`
produced by Taylor's Moret–Bailly argument, together with the Hecke
algebra of the Hilbert newform over `F` attached to `ρbar|_{G_F}`.

`galoisF` (Galois over `ℚ`) and `irreducibleF` (restriction preserves
irreducibility — Moret–Bailly's `F` is chosen linearly disjoint from the
splitting field of `ρbar`, so restriction PRESERVES the image) are the
two enabling hypotheses of the modularity lifting theorem over `F`;
`totallyReal` is what makes Hilbert modular forms available at all.

The same interface exists, in a different vocabulary, as
`Modularity/KhareWintenberger.lean`'s `PotentialModularityWitness` and
`MoretBaillySeed`, which record ONE modular lift over `F` through its
Hecke eigensystem. That is a strictly weaker datum than this one: a
single modular lift does not make the whole universal family Hecke, which
is what the leaf needs. Hoisting those structures upstream would
therefore not shorten this development; the reverse direction — deriving
a `PotentialModularityWitness` from `R_F = T_F` — is the useful one, and
is not needed by pillar α. -/
structure PotentialHeckeDatum (ℓ : ℕ) [Fact ℓ.Prime]
    {k : Type u} [Field k] [TopologicalSpace k]
    {V : Type v} [AddCommGroup V] [Module k V] [Module.Finite k V]
    [Module.Free k V]
    (ρbar : GaloisRep ℚ k V) where
  /-- The totally real base field of potential modularity. -/
  F : Type u
  [fieldF : Field F]
  [numberFieldF : NumberField F]
  /-- `F` is totally real (Taylor 2002). -/
  totallyReal : NumberField.IsTotallyReal F
  /-- `F/ℚ` is Galois — the enabling hypothesis of Brauer induction. -/
  galoisF : IsGalois ℚ F
  /-- Restriction preserves irreducibility (linear disjointness). -/
  irreducibleF : (ρbar.map (algebraMap ℚ F)).IsIrreducible
  /-- The Hecke algebra of the attached Hilbert newform over `F`. -/
  hecke : HilbertHeckeAlgebra ℓ F ρbar

attribute [instance] PotentialHeckeDatum.fieldF PotentialHeckeDatum.numberFieldF

/-- **Potential modularity together with finiteness of the Hilbert Hecke
algebra** (LEAF — items 5 and 3 of the audit's missing-machinery list,
merged because the production of `F` and the production of the newform
over `F` are one theorem in the literature).

Taylor's Theorem B (*Remarks on a conjecture of Fontaine and Mazur*, J.
Inst. Math. Jussieu 1 (2002)): for an irreducible mod-`ℓ` representation
of `G_ℚ` with `ℓ ≥ 5`, Moret–Bailly's theorem on rational points of
twisted Hilbert–Blumenthal moduli varieties over totally real fields
(*Groupes de Picard et problèmes de Skolem II*, Ann. Sci. ÉNS 22 (1989),
Thm 1.3) supplies a totally real `F`, Galois over `ℚ` and linearly
disjoint from the splitting field of `ρbar`, over which `ρbar|_{G_F}`
becomes modular: it is the residual representation of a Hilbert newform
of parallel weight `2` over `F` (residually dihedral modularity from
converse theorems and Jacquet–Langlands, promoted by modularity lifting
at an auxiliary prime). The Hecke algebra of that newform's level and
weight, localized at the corresponding maximal ideal, is `T_F`; its
`ℤ_ℓ`-module-finiteness is the classical finiteness of the space of
Hilbert modular forms of fixed weight and level.

`Modularity/KhareWintenberger.lean` decomposes the FIRST half of this
statement — production of `F` — into a geometric joint
(`exists_totallyReal_point_of_geometricallyIrreducible`,
`exists_twistedHilbertBlumenthalModuli_of_five_le`) and an automorphic
joint, all of which live downstream of this module and are stated in a
witness vocabulary recording only one lift. When that development is
hoisted into a KW-free module the geometric half of this leaf can be
consumed from it; the Hecke-algebra half (item 3) has no counterpart
anywhere.

CIRCULARITY GUARD: this leaf may only ever be discharged by the
independent Moret–Bailly/Taylor construction. Discharging it from the
odd-prime dichotomy — under whose hypotheses it is vacuously true — would
be circular, since that dichotomy is proven over pillar α, which is
proven over this leaf.

## AUDIT (2026-07-26): the leaf was VACUOUS, and is not any more

Read against the FIRST form of `HilbertHeckeAlgebra` this leaf had no
content, and the fact was not visible from the statement. Two independent
collapses were available:

1. `HilbertHeckeAlgebra ℓ F ρbar` was inhabited for every `F` and every
   `ρbar` here (`k` is `Finite` and carries `Algebra ℤ_[ℓ] k`), by the
   residual junk witness written out in that structure's VACUITY AUDIT and
   compiled in Lean. So the only surviving obligations of
   `PotentialHeckeDatum` were `totallyReal`, `galoisF` and `irreducibleF`.
2. Those three are discharged by `F = ℚ`: `ℚ` is totally real, `IsGalois ℚ ℚ`
   holds, and `ρbar.map (algebraMap ℚ ℚ)` is `ρbar` precomposed with an
   automorphism of `Γ ℚ`, hence irreducible. Two obstacles remain, and
   both are bookkeeping rather than arithmetic: `PotentialHeckeDatum.F` is
   in `Type u` while `ℚ : Type`, so one needs a `NumberField (ULift.{u} ℚ)`
   instance; and irreducibility has to be transported across
   `Field.absoluteGaloisGroup.map (algebraMap ℚ F)` for that `F`, which is
   a group isomorphism because `algebraMap ℚ F` is.

So the leaf was a page of instance plumbing away from `exact ⟨{F := ULift ℚ,
…}⟩`, with no automorphy anywhere in it. The repair was made in
`HilbertHeckeAlgebra`, not here: the statement of this leaf is UNCHANGED,
and it now asks for what it always claimed to. Collapse (2) alone is not
enough any more — over `F = ℚ` the datum would still have to produce a
hardly ramified characteristic-zero lift of `ρbar` itself, which is the
`ℚ`-level statement that pillar α proves and that potential modularity
exists to route around.

## WHAT REMAINS, AND WHY IT IS TERMINAL AT THIS PIN

The residue is a genuine citation, and it is not one leaf but two theorems
that the literature proves together:

* **Moret–Bailly / Taylor**: a totally real `F`, Galois over `ℚ` and
  linearly disjoint from the splitting field of `ρbar`, over which
  `ρbar|_{G_F}` is modular. The geometric half needs twisted
  Hilbert–Blumenthal moduli varieties and a rational-point theorem over
  totally real fields; the automorphic half needs residually dihedral
  modularity, Jacquet–Langlands, and a modularity lifting theorem at an
  auxiliary prime.
* **Carayol / Taylor**: the Galois representation attached to a Hilbert
  newform, with `Module.Finite` and `Module.Free` for the localized Hecke
  algebra, and the local–global compatibility that makes `ρT` hardly
  ramified at the places over `2` and `ℓ`. This last part silently
  contains level lowering over totally real fields (Fujiwara, Jarvis,
  Rajaei): the newform Taylor's theorem produces is of SOME level, and
  `isHilbertHardlyRamified` demands the MINIMAL one. That minimality is
  not decoration either — `HilbertHeckeAlgebra`'s own docstring records
  that without it `R_F` is of unbounded level, not module-finite, and
  `R_F = T_F` is false.

Neither is reachable at this mathlib pin. A survey by the owner of the
neighbouring `PotentialModularityWitness` interface established that there
is NO Weil group anywhere in mathlib or in the reference FLT project, no
local class field theory, no smooth or admissible representations, and a
54-line ramification-group development with a TODO for the higher groups.
The same survey killed the obvious piecewise route: solvable base change
does not preserve unramifiedness downwards, and `Ind` of an unramified
representation is unramified at `p` only when `p` is unramified in the
intermediate field — classically the pieces' ramification cancels in the
VIRTUAL SUM, which is invisible piecewise. That is why the citation has to
be taken on the sum, and it is why no cut of this leaf into smaller Lean
statements reduces what is assumed; it would only rename it. -/
theorem nonempty_potentialHeckeDatum_of_five_le
    (ℓ : ℕ) [Fact ℓ.Prime] {hℓOdd : Odd ℓ} (hℓ5 : 5 ≤ ℓ)
    {k : Type u} [Field k] [Finite k] [TopologicalSpace k]
    [DiscreteTopology k] [Algebra ℤ_[ℓ] k]
    {V : Type v} [AddCommGroup V] [Module k V] [Module.Finite k V]
    [Module.Free k V]
    {hdim : Module.rank k V = 2} {ρbar : GaloisRep ℚ k V}
    (hbar : IsHardlyRamified hℓOdd hdim ρbar) (hirr : ρbar.IsIrreducible) :
    Nonempty (PotentialHeckeDatum ℓ ρbar) :=
  sorry

/-! ### Item 4 — `R_F = T_F`

#### FAITHFULNESS AUDIT (2026-07-26): weak universality does NOT pin `R_F`

The statement of `exists_heckeAlgebra_algEquiv_of_isWeaklyUniversal` as it
was first written — with `𝒟.IsWeaklyUniversal` as its only hypothesis on
`𝒟` — is **FALSE**, and so was the corollary
`moduleFinite_hilbertDeformation_of_isWeaklyUniversal` derived from it.

The counterexample. `HilbertDeformationDatum.IsWeaklyUniversal` asks only
for the EXISTENCE of a compatible `f : 𝒟.R → 𝒟'.R` into every other
datum, never for its uniqueness. That property is not rigid: if `𝒟₀` is
the genuine universal datum, put `R := 𝒟₀.R⟦X⟧` with its maximal-adic
topology (still complete Noetherian local), let `ρ` be `𝒟₀.ρ` pushed
forward along the inclusion `𝒟₀.R → 𝒟₀.R⟦X⟧`, and let `π` be
`𝒟₀.π ∘ (X ↦ 0)`. Every clause of `IsHilbertHardlyRamified` is stable
under pushforward along a local `ℤ_ℓ`-algebra map (the determinant clause
is an identity; `ker ρ` only grows, so unramifiedness and the
unramifiedness of the tame-at-`2` character survive; `δ g * δ g = 1` is an
identity; finite flat group schemes base change), so this is a legitimate
`HilbertDeformationDatum`. It is weakly universal: for any `𝒟'`, compose
`X ↦ 0` with the classifying map of `𝒟₀`. And `𝒟₀.R⟦X⟧` is **not**
module-finite over `ℤ_ℓ`, hence not isomorphic to any `T.T`, every one of
which carries `Module.Finite ℤ_[ℓ] T`.

This is not a new discovery at the `ℚ` level: `Deformation.lean` records
exactly this witness (`R^{univ}[[t]]`) in the docstring of
`HardlyRamifiedDeformation.IsUniversal`, and repaired its own finiteness
stratum on 2026-07-26 by adding `IsTraceGenerated` — its
`moduleFinite_of_isWeaklyUniversal_isTraceGenerated` carries BOTH
hypotheses. This module, written the same day, did not inherit the
repair; the audit above transports it to the `F` level.

THE REPAIR, mirroring `Deformation.lean` exactly. `IsTraceGenerated`
below says the coefficient ring is topologically generated by the image of
`ℤ_ℓ`, the Teichmüller roots and the `charpoly` coefficients of `𝒟.ρ`.
It kills the witness (`X` is not in the closure of the subring generated
by the traces, which all lie in `𝒟₀.R`), and — this is the point — it
turns weak universality into genuine universality
(`isUniversal_of_isWeaklyUniversal_isTraceGenerated`), which IS rigid
(`exists_ringEquiv_of_isUniversal`). Consumers get the missing hypothesis
from `exists_isWeaklyUniversal_isTraceGenerated_hilbertDeformationDatum`,
the `F`-level twin of `Deformation.lean`'s Carayol trace descent — PROVEN
2026-07-26 over the two arithmetic leaves of the Carayol package; see the
subsection note there.

WHY THE TEICHMÜLLER ROOTS ARE IN THE GENERATING SET: over `ℤ_ℓ` alone the
residue field of the generated subring is only the trace field of `ρbar`,
so the descended datum could not supply `π_surjective` onto `k` and the
descent leaf would be false. This is the same repair, for the same
reason, as `Deformation.lean`'s `teichmullerRoots` component; see the
docstring of `teichmullerRootSet` below.

#### Formal prerequisites (local copies)

The four commutative-algebra helpers used by the rigidity argument all
exist in `Deformation.lean`, which is DOWNSTREAM of this module and so
unusable here; they are re-stated below under distinct names, exactly as
`rank_finTwoPi` re-states `rank_finTwoFun`. Hoisting the shared originals
into `Defs.lean` would remove the duplication and is the right long-term
fix; it is not done here because `Deformation.lean` has concurrent owners.
-/

/-- **The `ℓ`-power Teichmüller roots of `R`** — a local copy of
`Deformation.lean`'s `teichmullerRoots`, which lives DOWNSTREAM of this
module. Over a complete local ring with finite residue field of
characteristic `ℓ` these are exactly the Teichmüller representatives:
`X ^ ℓ ^ n − X` is separable modulo the maximal ideal, so reduction is a
bijection from this set onto the residue field.

They belong in the generating set of `IsTraceGenerated` because over
`ℤ_ℓ` alone the residue field of the generated subring is merely the
trace field of `ρbar`; adjoining them makes it `k` by construction. -/
def teichmullerRootSet (ℓ : ℕ) (R : Type*) [CommRing R] : Set R :=
  {x : R | ∃ n : ℕ, 0 < n ∧ x ^ ℓ ^ n = x}

/-- Teichmüller roots are preserved by every ring homomorphism (the
defining condition is an identity). -/
lemma map_mem_teichmullerRootSet {ℓ : ℕ} {R : Type*} [CommRing R]
    {S : Type*} [CommRing S] (f : R →+* S) {x : R}
    (hx : x ∈ teichmullerRootSet ℓ R) : f x ∈ teichmullerRootSet ℓ S := by
  obtain ⟨n, hn, hxe⟩ := hx
  exact ⟨n, hn, by rw [← map_pow, hxe]⟩

/-- `x ^ ℓ ^ n = x` upgrades to `x ^ ℓ ^ (n * j) = x` for every `j`. -/
lemma pow_pow_mul_of_pow_pow_eq {ℓ : ℕ} {R : Type*} [CommRing R] {x : R} {n : ℕ}
    (hx : x ^ ℓ ^ n = x) (j : ℕ) : x ^ ℓ ^ (n * j) = x := by
  induction j with
  | zero => simp
  | succ j ih =>
    have hnj : n * (j + 1) = n * j + n := by ring
    rw [hnj, pow_add, pow_mul, ih, hx]

/-- **Uniqueness of Teichmüller roots** (PROVEN, elementary Hensel): in a
local ring in which `ℓ` is a nonunit, two Teichmüller roots with the same
residue are equal. Writing `M = ℓ ^ (n * m)` so that both are `M`-th
roots, `x − y = x^M − y^M = S · (x − y)` with `S` congruent to
`M · y^{M−1} = 0` modulo the maximal ideal, so `1 − S` is a unit. -/
lemma eq_of_mem_teichmullerRootSet {ℓ : ℕ} [Fact ℓ.Prime]
    {R : Type*} [CommRing R] [IsLocalRing R]
    (hlR : ((ℓ : ℕ) : R) ∈ IsLocalRing.maximalIdeal R)
    {x y : R} (hx : x ∈ teichmullerRootSet ℓ R)
    (hy : y ∈ teichmullerRootSet ℓ R)
    (hxy : x - y ∈ IsLocalRing.maximalIdeal R) : x = y := by
  classical
  obtain ⟨n, hn, hxe⟩ := hx
  obtain ⟨m, hm, hye⟩ := hy
  set M : ℕ := ℓ ^ (n * m) with hM
  have hxM : x ^ M = x := pow_pow_mul_of_pow_pow_eq hxe m
  have hyM : y ^ M = y := by
    have hpm := pow_pow_mul_of_pow_pow_eq hye n
    rwa [Nat.mul_comm m n] at hpm
  set S : R := ∑ i ∈ Finset.range M, x ^ i * y ^ (M - 1 - i) with hS
  have hgeom : S * (x - y) = x - y := by
    rw [hS, geom_sum₂_mul, hxM, hyM]
  have hSmem : S ∈ IsLocalRing.maximalIdeal R := by
    have hxy' : Ideal.Quotient.mk (IsLocalRing.maximalIdeal R) x
        = Ideal.Quotient.mk (IsLocalRing.maximalIdeal R) y := by
      rw [← sub_eq_zero, ← map_sub, Ideal.Quotient.eq_zero_iff_mem]
      exact hxy
    rw [← Ideal.Quotient.eq_zero_iff_mem, hS, map_sum]
    have hterm : ∀ i ∈ Finset.range M,
        Ideal.Quotient.mk (IsLocalRing.maximalIdeal R) (x ^ i * y ^ (M - 1 - i))
          = Ideal.Quotient.mk (IsLocalRing.maximalIdeal R) y ^ (M - 1) := by
      intro i hi
      rw [map_mul, map_pow, map_pow, hxy', ← pow_add]
      congr 1
      simp only [Finset.mem_range] at hi
      omega
    rw [Finset.sum_congr rfl hterm, Finset.sum_const, Finset.card_range,
      nsmul_eq_mul]
    have hMz : ((M : ℕ) : R ⧸ IsLocalRing.maximalIdeal R) = 0 := by
      have hlz : ((ℓ : ℕ) : R ⧸ IsLocalRing.maximalIdeal R) = 0 := by
        rw [← map_natCast (Ideal.Quotient.mk (IsLocalRing.maximalIdeal R)) ℓ,
          Ideal.Quotient.eq_zero_iff_mem]
        exact hlR
      rw [hM, Nat.cast_pow, hlz, zero_pow (Nat.mul_pos hn hm).ne']
    rw [hMz, zero_mul]
  have hunit : IsUnit (1 - S) := by
    refine IsLocalRing.notMem_maximalIdeal.mp ?_
    intro hmem
    have hone : (1 : R) ∈ IsLocalRing.maximalIdeal R := by
      have hsplit : (1 : R) = (1 - S) + S := by ring
      rw [hsplit]
      exact Ideal.add_mem _ hmem hSmem
    exact (IsLocalRing.notMem_maximalIdeal.mpr isUnit_one) hone
  have h0 : (x - y) * (1 - S) = 0 := by linear_combination -hgeom
  obtain ⟨u, hu⟩ := hunit
  have hz : x - y = 0 := by
    have h1 : (x - y) * (1 - S) * (↑u⁻¹ : R) = 0 := by rw [h0, zero_mul]
    rwa [← hu, mul_assoc, Units.mul_inv, mul_one] at h1
  exact sub_eq_zero.mp hz

/-- `ℓ` lies in the maximal ideal of a local ring carrying a surjection
onto a field of characteristic `ℓ`. -/
lemma natCast_mem_maximalIdeal_of_surjective {ℓ : ℕ}
    {R : Type*} [CommRing R] [IsLocalRing R] {k : Type*} [Field k]
    (π : R →+* k) (hπ : Function.Surjective π) (hlk : ((ℓ : ℕ) : k) = 0) :
    ((ℓ : ℕ) : R) ∈ IsLocalRing.maximalIdeal R := by
  rw [← IsLocalRing.ker_eq_maximalIdeal π hπ, RingHom.mem_ker, map_natCast]
  exact hlk

/-- **A finite field receiving `ℤ_ℓ` has characteristic `ℓ`** (PROVEN,
elementary) — a local copy of `Deformation.lean`'s `natCast_self_eq_zero`,
which lives downstream. Were `char k = p ≠ ℓ`, then `p` would be a unit of
`ℤ_ℓ` dying in the nontrivial `k` under the structure map. -/
lemma natCast_eq_zero_of_finite_algebra (ℓ : ℕ) [Fact ℓ.Prime]
    (k : Type*) [Field k] [Finite k] [Algebra ℤ_[ℓ] k] : ((ℓ : ℕ) : k) = 0 := by
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

/-- An adically-topologized, adically-separated ring is Hausdorff: `{0}`
is the intersection of the open (hence closed) subgroups `I ^ n`. Local
copy of `Deformation.lean`'s `t2Space_of_isAdic`. -/
lemma t2Space_of_isAdic_of_isHausdorff {R : Type*} [CommRing R]
    [TopologicalSpace R] [IsTopologicalRing R] {I : Ideal R} (hadic : IsAdic I)
    [IsHausdorff I R] : T2Space R := by
  have hclosed : IsClosed ({(0 : R)} : Set R) := by
    have h0 : ({(0 : R)} : Set R) = ⋂ n : ℕ, ((I ^ n : Ideal R) : Set R) := by
      ext x
      simp only [Set.mem_singleton_iff, Set.mem_iInter, SetLike.mem_coe]
      constructor
      · rintro rfl n
        exact Submodule.zero_mem _
      · intro hx
        refine IsHausdorff.haus (inferInstance : IsHausdorff I R) x fun n => ?_
        rw [SModEq.zero, smul_eq_mul, Ideal.mul_top]
        exact hx n
    rw [h0]
    refine isClosed_iInter fun n => ?_
    exact AddSubgroup.isClosed_of_isOpen (Submodule.toAddSubgroup (I ^ n))
      ((isAdic_iff.mp hadic).1 n)
  haveI := IsTopologicalAddGroup.t1Space R hclosed
  infer_instance

open Topology in
/-- A **local homomorphism between adically-topologized local rings is
continuous**: `f (𝔪_R ^ n) ⊆ 𝔪_S ^ n` for every `n`, which is continuity
at `0`. Local copy of `Deformation.lean`'s
`continuous_of_map_maximalIdeal_le`. -/
lemma continuous_of_isAdic_of_map_maximalIdeal_le {R S : Type*} [CommRing R]
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
  intro n _
  have hmem : ((IsLocalRing.maximalIdeal R ^ n : Ideal R) : Set R) ∈
      𝓝 (0 : R) := hR.hasBasis_nhds_zero.mem_of_mem trivial
  filter_upwards [hmem] with x hx
  have hle : Ideal.map f (IsLocalRing.maximalIdeal R ^ n) ≤
      IsLocalRing.maximalIdeal S ^ n := by
    rw [Ideal.map_pow]
    exact Ideal.pow_right_mono hloc n
  exact hle (Ideal.mem_map_of_mem f hx)

/-! #### Trace generation and genuine universality at the `F` level -/

/-- **Trace generation** (Carayol), `F`-level: the coefficient ring of `𝒟`
is topologically generated by the image of `ℤ_ℓ`, the Teichmüller roots
and the coefficients of the characteristic polynomials of `𝒟.ρ`.

For the genuine universal ring of an absolutely irreducible
`ρbar|_{G_F}` this holds by Carayol's theorem. It is what makes
compatible homomorphisms out of `𝒟` UNIQUE, i.e. what turns weak
universality into universality — see the faithfulness audit above, and
`Deformation.lean`'s `HardlyRamifiedDeformation.IsTraceGenerated`, of
which this is the `F`-level twin (the `charFrob`-at-good-primes
generating set is replaced by the `charpoly`-at-every-`g` one, matching
this module's `resid`/`IsWeaklyUniversal`, which are also stated at every
group element). -/
def HilbertDeformationDatum.IsTraceGenerated {ℓ : ℕ} [Fact ℓ.Prime]
    {F : Type u} [Field F] [NumberField F]
    {k : Type u} [Field k] [TopologicalSpace k]
    {V : Type v} [AddCommGroup V] [Module k V] [Module.Finite k V]
    [Module.Free k V]
    {ρbar : GaloisRep ℚ k V} (𝒟 : HilbertDeformationDatum ℓ F ρbar) : Prop :=
  (Subring.closure (Set.range (algebraMap ℤ_[ℓ] 𝒟.R) ∪
    (teichmullerRootSet ℓ 𝒟.R ∪
      {x : 𝒟.R | ∃ (g : Γ F) (n : ℕ),
        x = ((𝒟.ρ g).charpoly).coeff n}))).topologicalClosure = ⊤

/-- **Genuine (Mazur) universality of an `F`-level datum**: every datum
receives a UNIQUE compatible `ℤ_ℓ`-algebra homomorphism from `𝒟`.

Both halves are load-bearing, and the uniqueness half is exactly what
`IsWeaklyUniversal` lacks: `𝒟₀.R⟦X⟧` (deformation constant in `X`) maps
to `𝒟₀.R⟦X⟧/(X²)` compatibly by both `X ↦ 0` and `X ↦ X̄`. See the
faithfulness audit above. -/
def HilbertDeformationDatum.IsUniversal {ℓ : ℕ} [Fact ℓ.Prime]
    {F : Type u} [Field F] [NumberField F]
    {k : Type u} [Field k] [TopologicalSpace k]
    {V : Type v} [AddCommGroup V] [Module k V] [Module.Finite k V]
    [Module.Free k V]
    {ρbar : GaloisRep ℚ k V} (𝒟 : HilbertDeformationDatum ℓ F ρbar) : Prop :=
  ∀ 𝒟' : HilbertDeformationDatum ℓ F ρbar,
    ∃! f : 𝒟.R →+* 𝒟'.R,
      f.comp (algebraMap ℤ_[ℓ] 𝒟.R) = algebraMap ℤ_[ℓ] 𝒟'.R ∧
      𝒟'.π.comp f = 𝒟.π ∧
      ∀ g : Γ F, ((𝒟.ρ g).charpoly).map f = (𝒟'.ρ g).charpoly

/-- **Uniqueness from trace generation** (PROVEN, the formal Carayol
argument; the `F`-level twin of `Deformation.lean`'s
`isUniversal_of_isWeaklyUniversal_isTraceGenerated`): a weakly universal,
trace-generated `F`-level datum is universal.

Two compatible homomorphisms `f, f' : 𝒟.R → 𝒟'.R` agree on the image of
`ℤ_ℓ` (both restrict to the structure map), on the Teichmüller roots
(their images are Teichmüller roots with the same residue, and such a
root is pinned by its residue), and on every `charpoly` coefficient (both
carry the `charpoly` of `𝒟.ρ` to that of `𝒟'.ρ`). They are continuous,
because compatibility with the reduction maps makes them local and local
homomorphisms of adic local rings are continuous; so their equalizer is a
closed subring containing the generating set, hence contains its
topological closure, which is everything.

The hypothesis `hlk` — the residue field has characteristic `ℓ` — is what
makes `ℓ` a nonunit in the coefficient rings, which the Teichmüller
uniqueness needs. It is automatic wherever this module is used: at the
assembly `k` is finite and a `ℤ_ℓ`-algebra, so
`natCast_eq_zero_of_finite_algebra` supplies it. -/
theorem HilbertDeformationDatum.isUniversal_of_isWeaklyUniversal_isTraceGenerated
    {ℓ : ℕ} [Fact ℓ.Prime] {F : Type u} [Field F] [NumberField F]
    {k : Type u} [Field k] [TopologicalSpace k]
    {V : Type v} [AddCommGroup V] [Module k V] [Module.Finite k V]
    [Module.Free k V]
    {ρbar : GaloisRep ℚ k V} (hlk : ((ℓ : ℕ) : k) = 0)
    (𝒟 : HilbertDeformationDatum ℓ F ρbar)
    (hw : 𝒟.IsWeaklyUniversal) (ht : 𝒟.IsTraceGenerated) :
    𝒟.IsUniversal := by
  intro 𝒟'
  haveI := 𝒟'.isAdicComplete
  haveI : IsHausdorff (IsLocalRing.maximalIdeal 𝒟'.R) 𝒟'.R :=
    (𝒟'.isAdicComplete).toIsHausdorff
  obtain ⟨f, hf⟩ := hw 𝒟'
  refine ⟨f, hf, fun f' hf' => ?_⟩
  have hker : RingHom.ker 𝒟.π = IsLocalRing.maximalIdeal 𝒟.R :=
    IsLocalRing.eq_maximalIdeal
      (RingHom.ker_isMaximal_of_surjective 𝒟.π 𝒟.π_surjective)
  have hker' : RingHom.ker 𝒟'.π = IsLocalRing.maximalIdeal 𝒟'.R :=
    IsLocalRing.eq_maximalIdeal
      (RingHom.ker_isMaximal_of_surjective 𝒟'.π 𝒟'.π_surjective)
  have hcont : ∀ h : 𝒟.R →+* 𝒟'.R, 𝒟'.π.comp h = 𝒟.π → Continuous h := by
    intro h hh
    refine continuous_of_isAdic_of_map_maximalIdeal_le 𝒟.isAdic 𝒟'.isAdic h ?_
    rw [Ideal.map_le_iff_le_comap, ← hker, ← hker']
    intro x hx
    show 𝒟'.π (h x) = 0
    rw [← RingHom.comp_apply, hh]
    exact hx
  haveI : T2Space 𝒟'.R := t2Space_of_isAdic_of_isHausdorff 𝒟'.isAdic
  have hclosed : IsClosed ((RingHom.eqLocus f' f : Subring 𝒟.R) : Set 𝒟.R) :=
    isClosed_eq (hcont f' hf'.2.1) (hcont f hf.2.1)
  have hgen : Subring.closure (Set.range (algebraMap ℤ_[ℓ] 𝒟.R) ∪
      (teichmullerRootSet ℓ 𝒟.R ∪
        {x : 𝒟.R | ∃ (g : Γ F) (n : ℕ),
          x = ((𝒟.ρ g).charpoly).coeff n})) ≤ RingHom.eqLocus f' f := by
    rw [Subring.closure_le]
    rintro x (⟨c, rfl⟩ | hx | ⟨g, n, rfl⟩)
    · show f' (algebraMap ℤ_[ℓ] 𝒟.R c) = f (algebraMap ℤ_[ℓ] 𝒟.R c)
      rw [← RingHom.comp_apply, ← RingHom.comp_apply, hf'.1, hf.1]
    · show f' x = f x
      refine eq_of_mem_teichmullerRootSet
        (natCast_mem_maximalIdeal_of_surjective 𝒟'.π 𝒟'.π_surjective hlk)
        (map_mem_teichmullerRootSet f' hx) (map_mem_teichmullerRootSet f hx) ?_
      rw [← hker', RingHom.mem_ker, map_sub, ← RingHom.comp_apply,
        ← RingHom.comp_apply, hf'.2.1, hf.2.1, sub_self]
    · show f' (((𝒟.ρ g).charpoly).coeff n) = f (((𝒟.ρ g).charpoly).coeff n)
      have hcf := (hf'.2.2 g).trans (hf.2.2 g).symm
      have hcoeff := congrArg (fun p : Polynomial 𝒟'.R => p.coeff n) hcf
      simpa [Polynomial.coeff_map] using hcoeff
  have htop : (⊤ : Subring 𝒟.R) ≤ RingHom.eqLocus f' f := by
    have hcl : (Subring.closure (Set.range (algebraMap ℤ_[ℓ] 𝒟.R) ∪
        (teichmullerRootSet ℓ 𝒟.R ∪
          {x : 𝒟.R | ∃ (g : Γ F) (n : ℕ),
            x = ((𝒟.ρ g).charpoly).coeff n}))).topologicalClosure = ⊤ := ht
    rw [← hcl]
    exact Subring.topologicalClosure_minimal _ hgen hclosed
  exact RingHom.ext fun x => htop (Subring.mem_top x)

/-- **Rigidity of universal data** (PROVEN, formal; the `F`-level twin of
`Deformation.lean`'s `exists_ringEquiv_of_isUniversal`): any two universal
`F`-level data have canonically isomorphic coefficient rings, compatibly
with the `ℤ_ℓ`-algebra structure. The two `∃!`-clauses produce
homomorphisms in both directions whose composites are compatible
endomorphisms, hence equal to the identity. -/
theorem HilbertDeformationDatum.exists_ringEquiv_of_isUniversal
    {ℓ : ℕ} [Fact ℓ.Prime] {F : Type u} [Field F] [NumberField F]
    {k : Type u} [Field k] [TopologicalSpace k]
    {V : Type v} [AddCommGroup V] [Module k V] [Module.Finite k V]
    [Module.Free k V]
    {ρbar : GaloisRep ℚ k V}
    (𝒟 𝒟' : HilbertDeformationDatum ℓ F ρbar)
    (h𝒟 : 𝒟.IsUniversal) (h𝒟' : 𝒟'.IsUniversal) :
    ∃ e : 𝒟.R ≃+* 𝒟'.R, ∀ c : ℤ_[ℓ],
      e (algebraMap ℤ_[ℓ] 𝒟.R c) = algebraMap ℤ_[ℓ] 𝒟'.R c := by
  obtain ⟨f, hf, -⟩ := h𝒟 𝒟'
  obtain ⟨g, hg, -⟩ := h𝒟' 𝒟
  have hgf : g.comp f = RingHom.id 𝒟.R := by
    obtain ⟨i, -, hiu⟩ := h𝒟 𝒟
    have h1 : g.comp f = i := by
      refine hiu (g.comp f) ⟨?_, ?_, ?_⟩
      · rw [RingHom.comp_assoc, hf.1, hg.1]
      · rw [← RingHom.comp_assoc, hg.2.1, hf.2.1]
      · intro x
        rw [← Polynomial.map_map, hf.2.2 x, hg.2.2 x]
    have h2 : RingHom.id 𝒟.R = i := by
      refine hiu (RingHom.id 𝒟.R) ⟨?_, ?_, ?_⟩
      · rw [RingHom.id_comp]
      · rw [RingHom.comp_id]
      · intro _
        exact Polynomial.map_id
    rw [h1, h2]
  have hfg : f.comp g = RingHom.id 𝒟'.R := by
    obtain ⟨j, -, hju⟩ := h𝒟' 𝒟'
    have h1 : f.comp g = j := by
      refine hju (f.comp g) ⟨?_, ?_, ?_⟩
      · rw [RingHom.comp_assoc, hg.1, hf.1]
      · rw [← RingHom.comp_assoc, hf.2.1, hg.2.1]
      · intro x
        rw [← Polynomial.map_map, hg.2.2 x, hf.2.2 x]
    have h2 : RingHom.id 𝒟'.R = j := by
      refine hju (RingHom.id 𝒟'.R) ⟨?_, ?_, ?_⟩
      · rw [RingHom.id_comp]
      · rw [RingHom.comp_id]
      · intro _
        exact Polynomial.map_id
    rw [h1, h2]
  refine ⟨RingEquiv.ofRingHom f g hfg hgf, fun c => ?_⟩
  show f (algebraMap ℤ_[ℓ] 𝒟.R c) = algebraMap ℤ_[ℓ] 𝒟'.R c
  rw [← RingHom.comp_apply, hf.1]

/-! #### Carayol's trace subring at the `F` level

The cut of `exists_isWeaklyUniversal_isTraceGenerated_hilbertDeformationDatum`
below is the `F`-level TRANSPORT of the architecture `Deformation.lean`
already carries at the `ℚ` level, declaration for declaration:

| `Deformation.lean` (`ℚ`) | here (`F`) | status |
| --- | --- | --- |
| `traceSubring` | `hilbertTraceSubring` | definition |
| `exists_isLocalRing_traceSubring` | `exists_isLocalRing_hilbertTraceSubring` | LEAF |
| `exists_framedGaloisRep_traceSubring` | `exists_framedGaloisRep_hilbertTraceSubring` | LEAF |
| `traceSubring_eq_top_of_charFrob_map` | `hilbertTraceSubring_eq_top_of_charpoly_map` | PROVEN |
| `exists_isTraceGenerated_ringHom_of_forall_trace_mem` | `exists_hilbertTraceDescent` | PROVEN |
| `exists_isWeaklyUniversal_isTraceGenerated_of_isWeaklyUniversal` | the target below | PROVEN |

**ONE `ℚ`-LEVEL LEAF HAS NO `F`-LEVEL COUNTERPART, AND THAT IS A REAL
SIMPLIFICATION, NOT AN OVERSIGHT.** Over `ℚ` the trace subring is generated
by the Frobenius characteristic polynomials AT THE GOOD PRIMES ONLY, so the
descent needs the hypothesis `htr` — that the subring so generated already
absorbs the trace at EVERY `g ∈ G_ℚ` — and discharging it is a Chebotarev
density argument (`forall_charpoly_coeff_mem_traceSubring`, plus
Brauer–Nesbitt). Here `HilbertDeformationDatum.IsTraceGenerated` is stated
with the charpoly coefficients at EVERY `g : Γ F` — matching this module's
`resid` and `IsWeaklyUniversal`, which are also stated at every group
element — so the generating set literally contains every trace and the
hypothesis is `charpoly_coeff_mem_hilbertTraceSubring`, a one-liner. The
`ℚ`-level Chebotarev leaf simply does not arise.

**THE FOUR COMMUTATIVE-ALGEBRA HELPERS BELOW ARE LOCAL COPIES**, for the
same reason as `rank_finTwoPi`, `teichmullerRootSet` and `framePushforward`
above: their originals are in `Deformation.lean`, which is DOWNSTREAM. That
makes EIGHT duplicated helpers in this module now. Hoisting the shared
originals into `Defs.lean` is the right fix and needs a single owner across
both files; it is not done here because `Deformation.lean` has concurrent
owners.

**FAITHFULNESS: TWO HYPOTHESES WERE ADDED TO THE TARGET ON 2026-07-26**,
`[Finite k]` and `hlk : (ℓ : k) = 0`, and they are NOT cosmetic.

The descended datum's coefficient ring is the trace subring `R'`, and a
`HilbertDeformationDatum` must surject onto `k` — so the descent is
possible AT ALL only if the residue field of `R'` is `k` on the nose. The
residue field of `R'` is generated by `𝔽_ℓ`, by the residues of the
Teichmüller roots, and by the traces of `ρbar|_{G_F}`; the Teichmüller
roots supply exactly the elements of `k` algebraic over `𝔽_ℓ` (Hensel,
`exists_mem_teichmullerRootSet_map_eq`), which is all of `k` when `k` is
FINITE and a proper subfield otherwise. For `k` infinite — say
`k = 𝔽_ℓ(t)`, which satisfies every hypothesis the statement previously
had — `t` lies in no such subring, `R'` has residue field ⊊ `k`, and NO
datum over `ρbar` has coefficient ring `R'`. Hensel also needs `char k = ℓ`
to make the derivative of `X ^ ℓ ^ n − X` a unit, which is `hlk`.

This is not a weakening dressed up as a fix: it is the exact shape the `ℚ`
level already has, where `variable {k : Type u} [Field k] [Finite k]
[Algebra ℤ_[ℓ] k]` is global to the whole module, and where the same
Hensel lemma is used at the same place in the same proof. Both hypotheses
are discharged FOR FREE at the sole consumer
(`exists_finiteIndex_isIntegral_charpolyCoeff_of_isHardlyRamified`, which
already carries `[Finite k]` and `[Algebra ℤ_[ℓ] k]`, the latter giving
`hlk` through the PROVEN `natCast_eq_zero_of_finite_algebra`), so nothing
downstream changes. `hℓ5` is carried for the same reason
`Deformation.lean` carries it on `exists_isLocalRing_traceSubring`: the
soft half consumes none of it, but the arithmetic leaves underneath are
the Carayol package, whose hypotheses this module has no way to check. -/

/-- **Existence of Teichmüller roots** (PROVEN, Hensel; local copy of
`Deformation.lean`'s `exists_mem_teichmullerRoots_map_eq`, which lives
DOWNSTREAM of this module): every element of a FINITE residue field `k` of
characteristic `ℓ` is the residue of a Teichmüller root of a complete local
ring `R` surjecting onto `k`.

Apply Hensel's lemma to the monic `X ^ ℓ ^ n − X` where `ℓ ^ n = |k|`: it
kills every element of `k` (`FiniteField.pow_card`), and its derivative
`ℓ ^ n · X ^ (ℓ ^ n − 1) − 1` reduces to `−1`, a unit, because `k` has
characteristic `ℓ`.

This is what makes the residue field of Carayol's trace subring equal to
`k` on the nose once the Teichmüller roots are among its generators, and it
is the reason the target below carries `[Finite k]`; see the faithfulness
note above. -/
lemma exists_mem_teichmullerRootSet_map_eq {ℓ : ℕ} [Fact ℓ.Prime]
    {R : Type u} [CommRing R] [IsLocalRing R]
    [IsAdicComplete (IsLocalRing.maximalIdeal R) R]
    {k : Type u} [Field k] [Finite k] (hlk : ((ℓ : ℕ) : k) = 0)
    (π : R →+* k) (hπ : Function.Surjective π) (a : k) :
    ∃ x ∈ teichmullerRootSet ℓ R, π x = a := by
  classical
  haveI : Fintype k := Fintype.ofFinite k
  haveI hchar : CharP k ℓ := by
    have hp : (ringChar k).Prime :=
      (CharP.char_is_prime_or_zero k (ringChar k)).resolve_right
        (CharP.char_ne_zero_of_finite k (ringChar k))
    have hdvd : ringChar k ∣ ℓ := (CharP.cast_eq_zero_iff k (ringChar k) ℓ).mp hlk
    have heq : ringChar k = ℓ :=
      (Nat.prime_dvd_prime_iff_eq hp (Fact.out : ℓ.Prime)).mp hdvd
    exact heq ▸ ringChar.charP k
  obtain ⟨n, -, hcard⟩ := FiniteField.card k ℓ
  set M : ℕ := ℓ ^ (n : ℕ) with hM
  have hMcard : Fintype.card k = M := hcard
  have hpow : ∀ b : k, b ^ M = b := fun b => by
    rw [← hMcard]; exact FiniteField.pow_card b
  have hM2 : 1 < M := by
    rw [hM]; exact Nat.one_lt_pow n.2.ne' (Fact.out : ℓ.Prime).one_lt
  haveI : HenselianLocalRing R := by
    constructor
    intro f hf a₀ h₁ h₂
    exact HenselianRing.is_henselian (I := IsLocalRing.maximalIdeal R) f hf a₀ h₁
      (h₂.map (Ideal.Quotient.mk (IsLocalRing.maximalIdeal R)))
  have hmono : (Polynomial.X ^ M - Polynomial.X : Polynomial R).Monic := by
    refine (Polynomial.monic_X_pow M).sub_of_left ?_
    rw [Polynomial.degree_X_pow, Polynomial.degree_X]
    exact_mod_cast hM2
  have hMz : ((M : ℕ) : k) = 0 := by
    rw [hM, Nat.cast_pow, CharP.cast_eq_zero k ℓ]
    exact zero_pow n.2.ne'
  obtain ⟨a₀, ha₀⟩ := hπ a
  have hker : RingHom.ker π = IsLocalRing.maximalIdeal R :=
    IsLocalRing.ker_eq_maximalIdeal π hπ
  have hev : (Polynomial.X ^ M - Polynomial.X : Polynomial R).eval a₀
      ∈ IsLocalRing.maximalIdeal R := by
    rw [← hker, RingHom.mem_ker, Polynomial.eval_sub, Polynomial.eval_pow,
      Polynomial.eval_X, map_sub, map_pow, ha₀, hpow a, sub_self]
  have hder : IsUnit ((Polynomial.X ^ M - Polynomial.X :
      Polynomial R).derivative.eval a₀) := by
    refine IsLocalRing.notMem_maximalIdeal.mp ?_
    rw [← hker, RingHom.mem_ker, Polynomial.derivative_sub,
      Polynomial.derivative_X_pow, Polynomial.derivative_X, Polynomial.eval_sub,
      Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
      Polynomial.eval_X, Polynomial.eval_one, map_sub, map_mul, map_pow,
      map_natCast, map_one, hMz, zero_mul, zero_sub]
    exact fun hcontra => one_ne_zero (neg_eq_zero.mp hcontra)
  obtain ⟨x, hroot, hsub⟩ :=
    HenselianLocalRing.is_henselian (Polynomial.X ^ M - Polynomial.X) hmono a₀
      hev hder
  refine ⟨x, ⟨(n : ℕ), n.2, ?_⟩, ?_⟩
  · rw [Polynomial.IsRoot, Polynomial.eval_sub, Polynomial.eval_pow,
      Polynomial.eval_X] at hroot
    rw [← hM]
    exact sub_eq_zero.mp hroot
  · have hmem : x - a₀ ∈ RingHom.ker π := hker ▸ hsub
    rw [RingHom.mem_ker, map_sub, sub_eq_zero] at hmem
    rw [hmem, ha₀]

/-- **A subring whose image under a topological embedding is dense in the
ambient subring is everything** (PROVEN, elementary topology; local copy of
`Deformation.lean`'s `topologicalClosure_eq_top_of_map_eq`, which lives
DOWNSTREAM of this module): let `C` be a subring of a topological ring `R`
carrying the subspace topology, `T'` a subring of `C` whose image
`T = ι(T')` under the inclusion `ι = C.subtype` satisfies
`C = T.topologicalClosure`. Then `T'` is topologically dense in `C`.

The proof is the inducing-map closure formula
`IsInducing.closure_eq_preimage_closure_image`: the closure of `T'` inside
`C` is the preimage of the closure of `ι '' T' = T` inside `R`, and every
point of `C` lies in that closure by hypothesis. -/
lemma subring_topologicalClosure_eq_top_of_map_eq {R : Type*} [CommRing R]
    [TopologicalSpace R] [IsTopologicalRing R] {C : Subring R}
    {T' : Subring C} {T : Subring R}
    (hmap : T'.map C.subtype = T) (hC : C = T.topologicalClosure) :
    T'.topologicalClosure = ⊤ := by
  refine eq_top_iff.mpr fun x _ => ?_
  have hx : (x : R) ∈ T.topologicalClosure := hC ▸ x.2
  have hind : Topology.IsInducing (fun y : C => (y : R)) := ⟨rfl⟩
  have himg : (fun y : C => (y : R)) '' (T' : Set C) = (T : Set R) := by
    rw [← hmap, Subring.coe_map, Subring.coe_subtype]
  show x ∈ closure ((T' : Set C))
  rw [hind.closure_eq_preimage_closure_image, Set.mem_preimage, himg]
  exact hx

/-- **Carayol's trace subring `R'` at the `F` level**: the closed
`ℤ_ℓ`-subalgebra of the coefficient ring topologically generated by the
image of `ℤ_ℓ`, the Teichmüller roots and the coefficients of the
characteristic polynomials of `ρ` at EVERY element of `G_F`.

This is, verbatim, the subring whose being everything is
`HilbertDeformationDatum.IsTraceGenerated` — so `𝒟.IsTraceGenerated` is
`hilbertTraceSubring ℓ 𝒟.ρ = ⊤` by definition, and the descent below
produces a datum whose ring IS `hilbertTraceSubring ℓ 𝒟.ρ`.

The `ℚ`-level `traceSubring` uses the Frobenius charpolys at the GOOD
PRIMES; here the generating set runs over all of `G_F`, which is what
removes the Chebotarev leaf (see the section note above). The prime `ℓ` is
an explicit argument because it is not determined by `ρ`: it occurs only in
the `ℤ_ℓ`-algebra structure and in the Teichmüller component. -/
def hilbertTraceSubring (ℓ : ℕ) [Fact ℓ.Prime]
    {F : Type u} [Field F] [NumberField F]
    {R : Type*} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    [Algebra ℤ_[ℓ] R] (ρ : FramedGaloisRep F R (Fin 2)) : Subring R :=
  (Subring.closure (Set.range (algebraMap ℤ_[ℓ] R) ∪
    (teichmullerRootSet ℓ R ∪
      {x : R | ∃ (g : Γ F) (n : ℕ),
        x = ((ρ g).charpoly).coeff n}))).topologicalClosure

/-- The trace subring is a `ℤ_ℓ`-algebra: the image of `ℤ_ℓ` is one of its
generating sets, so the structure map corestricts. -/
noncomputable instance instAlgebraHilbertTraceSubring (ℓ : ℕ) [Fact ℓ.Prime]
    {F : Type u} [Field F] [NumberField F]
    {R : Type*} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    [Algebra ℤ_[ℓ] R] (ρ : FramedGaloisRep F R (Fin 2)) :
    Algebra ℤ_[ℓ] (hilbertTraceSubring ℓ ρ) :=
  ((algebraMap ℤ_[ℓ] R).codRestrict (hilbertTraceSubring ℓ ρ)
    (fun c => Subring.le_topologicalClosure _
      (Subring.subset_closure (Or.inl ⟨c, rfl⟩)))).toAlgebra

/-- Every Teichmüller root lies in the trace subring (it is one of its
generators). This is what supplies the descended datum's surjectivity
onto `k`. -/
lemma mem_hilbertTraceSubring_of_mem_teichmullerRootSet (ℓ : ℕ) [Fact ℓ.Prime]
    {F : Type u} [Field F] [NumberField F]
    {R : Type*} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    [Algebra ℤ_[ℓ] R] (ρ : FramedGaloisRep F R (Fin 2))
    {x : R} (hx : x ∈ teichmullerRootSet ℓ R) : x ∈ hilbertTraceSubring ℓ ρ :=
  Subring.le_topologicalClosure _ (Subring.subset_closure (Or.inr (Or.inl hx)))

/-- Every characteristic-polynomial coefficient lies in the trace subring
(it is one of its generators). This is the `F`-level replacement for the
`ℚ`-level Chebotarev leaf `forall_charpoly_coeff_mem_traceSubring`: the
generating set here already runs over every `g : Γ F`. -/
lemma charpoly_coeff_mem_hilbertTraceSubring (ℓ : ℕ) [Fact ℓ.Prime]
    {F : Type u} [Field F] [NumberField F]
    {R : Type*} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    [Algebra ℤ_[ℓ] R] (ρ : FramedGaloisRep F R (Fin 2)) (g : Γ F) (n : ℕ) :
    ((ρ g).charpoly).coeff n ∈ hilbertTraceSubring ℓ ρ :=
  Subring.le_topologicalClosure _
    (Subring.subset_closure (Or.inr (Or.inr ⟨g, n, rfl⟩)))

/-- **The descended representation is trace-generated** (PROVEN — the
*coefficient-ring structure of `R'`* half of Carayol's Théorème 1, and the
`F`-level twin of `Deformation.lean`'s
`traceSubring_eq_top_of_charFrob_map`): if a framed representation `ρ'`
over the trace subring `R' = hilbertTraceSubring ℓ ρ` of `ρ` has `ρ`'s
characteristic polynomials as the images of its own under the inclusion
`R' → R`, then `R'` is topologically generated by the `ℤ_ℓ`-image, the
Teichmüller roots and the charpoly coefficients OF `ρ'` — i.e. `ρ'` is
trace-generated as a coefficient ring in its own right.

This is not a tautology: `R'` is by definition the closure of the subring
`T` generated by the coefficients of `ρ` *inside `R`*, whereas trace
generation of `ρ'` asks for the closure of the subring `T'` generated by
the coefficients of `ρ'` *inside `R'`*, for the subspace topology. The two
are matched because the inclusion `ι : R' → R` is a topological embedding
carrying `T'` isomorphically onto `T` (`RingHom.map_closure` plus the three
generator computations), so `closure T ∩ R' = closure_{R'} T'`
(`subring_topologicalClosure_eq_top_of_map_eq`), and `closure T = R'`. -/
lemma hilbertTraceSubring_eq_top_of_charpoly_map (ℓ : ℕ) [Fact ℓ.Prime]
    {F : Type u} [Field F] [NumberField F]
    {R : Type u} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    [Algebra ℤ_[ℓ] R] (ρ : FramedGaloisRep F R (Fin 2))
    (ρ' : FramedGaloisRep F (hilbertTraceSubring ℓ ρ) (Fin 2))
    (hcp : ∀ g : Γ F, ((ρ' g).charpoly).map (hilbertTraceSubring ℓ ρ).subtype =
      (ρ g).charpoly) :
    hilbertTraceSubring ℓ ρ' = ⊤ := by
  refine subring_topologicalClosure_eq_top_of_map_eq ?_ rfl
  have h1 : (hilbertTraceSubring ℓ ρ).subtype ''
      Set.range (algebraMap ℤ_[ℓ] (hilbertTraceSubring ℓ ρ)) =
      Set.range (algebraMap ℤ_[ℓ] R) := by
    rw [← Set.range_comp]
    rfl
  have h2 : (hilbertTraceSubring ℓ ρ).subtype ''
      {x : hilbertTraceSubring ℓ ρ | ∃ (g : Γ F) (n : ℕ),
        x = ((ρ' g).charpoly).coeff n} =
      {x : R | ∃ (g : Γ F) (n : ℕ), x = ((ρ g).charpoly).coeff n} := by
    ext x
    constructor
    · rintro ⟨y, ⟨g, n, rfl⟩, rfl⟩
      refine ⟨g, n, ?_⟩
      simp only [← hcp g, Polynomial.coeff_map, Subring.coe_subtype]
    · rintro ⟨g, n, rfl⟩
      refine ⟨((ρ' g).charpoly).coeff n, ⟨g, n, rfl⟩, ?_⟩
      simp only [← hcp g, Polynomial.coeff_map, Subring.coe_subtype]
  have h3 : (hilbertTraceSubring ℓ ρ).subtype ''
      (teichmullerRootSet ℓ (hilbertTraceSubring ℓ ρ)) =
      teichmullerRootSet ℓ R := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact map_mem_teichmullerRootSet (hilbertTraceSubring ℓ ρ).subtype hy
    · intro hx
      refine ⟨⟨x, mem_hilbertTraceSubring_of_mem_teichmullerRootSet ℓ ρ hx⟩, ?_, rfl⟩
      obtain ⟨n, hn, hxe⟩ := hx
      exact ⟨n, hn, Subtype.ext (by simpa using hxe)⟩
  rw [RingHom.map_closure, Set.image_union, Set.image_union, h1, h3, h2]

/-- **`𝒟'` is a trace descent of `𝒟`**: `𝒟'` is trace-generated and maps
compatibly INTO `𝒟` — the `F`-level twin of `Deformation.lean`'s
`HardlyRamifiedDeformation.IsTraceDescent`.

Weak universality plays no role in it: it is restored formally by the
composition glue in
`exists_isWeaklyUniversal_isTraceGenerated_hilbertDeformationDatum`. The
three compatibility clauses are exactly the three of `IsWeaklyUniversal`,
read in the opposite direction. -/
def HilbertDeformationDatum.IsTraceDescent {ℓ : ℕ} [Fact ℓ.Prime]
    {F : Type u} [Field F] [NumberField F]
    {k : Type u} [Field k] [TopologicalSpace k]
    {V : Type v} [AddCommGroup V] [Module k V] [Module.Finite k V]
    [Module.Free k V]
    {ρbar : GaloisRep ℚ k V}
    (𝒟 𝒟' : HilbertDeformationDatum ℓ F ρbar) : Prop :=
  𝒟'.IsTraceGenerated ∧
  ∃ ι : 𝒟'.R →+* 𝒟.R,
    ι.comp (algebraMap ℤ_[ℓ] 𝒟'.R) = algebraMap ℤ_[ℓ] 𝒟.R ∧
    𝒟.π.comp ι = 𝒟'.π ∧
    ∀ g : Γ F, ((𝒟'.ρ g).charpoly).map ι = (𝒟.ρ g).charpoly

/-- **Carayol's Lemme 1 at the `F` level** (LEAF — new 2026-07-26; the
`F`-level twin of `Deformation.lean`'s `exists_isLocalRing_traceSubring`,
which is PROVEN there over its own four-way cut): the closed trace subring
`R' = hilbertTraceSubring ℓ 𝒟.ρ` is again a COEFFICIENT RING — local,
Noetherian, adically topologized and adically complete.

THE CONTENT IS NOETHERIANITY, and it is FALSE for a general closed subring
of a complete Noetherian local ring: `k[[x, xy, xy², …]]` inside `k[[x,y]]`
is a closed local subring with the same residue field and a
non-finitely-generated maximal ideal, and it also refutes Lemme 1. So the
Carayol hypotheses — `hℓ5`, irreducibility of `ρbar|_{G_F}`, and the local
conditions bundled inside `𝒟.isHilbertHardlyRamified` — are carried here
even though a soft-half proof would consume none of them.

THE `ℚ`-LEVEL ROUTE, which is the one to port. `exists_isLocalRing_traceSubring`
is proven over: `exists_uniform_span_maximalIdeal_traceSubring` (a UNIFORM
bound on the number of generators of `𝔪'` modulo the induced filtration,
obtained by running Carayol's Théorème 1 at each FINITE level `R ⧸ 𝔪ⁿ`,
where the trace subring is automatically local, Noetherian, adic and
complete); `fg_comap_maximalIdeal_traceSubring` (finite generation of `𝔪'`,
by the compactness transfer `ProfiniteLocal.fg_comap_of_uniform_span`);
`exists_pow_comap_le_pow_maximalIdeal_traceSubring` (Lemme 1 proper,
`∀ n, ∃ m, 𝔪^m ∩ R' ⊆ 𝔪'^n`, by Chevalley's theorem in its compactness
form); and the general `isNoetherianRing_of_fg_maximalIdeal` ("complete +
`𝔪` f.g. ⟹ Noetherian", Stacks 05GH, in
`HardlyRamified/CompleteLocalNoetherian.lean`, which IS upstream of this
module and so directly usable here). Only the first three are `ℚ`-specific.

The `[Finite k]` hypothesis is what makes the residue field of `𝒟.R`
finite, which the closed-subring machinery uses throughout.

References: Carayol, *Formes modulaires et représentations galoisiennes à
valeurs dans un anneau local complet* (Contemp. Math. 165), Théorème 1 and
Lemme 1; Nyssen, *Pseudo-représentations*; Rouquier, *Caractérisation des
caractères et pseudo-caractères*. -/
theorem exists_isLocalRing_hilbertTraceSubring
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ5 : 5 ≤ ℓ) (F : Type u) [Field F] [NumberField F]
    {k : Type u} [Field k] [Finite k] [TopologicalSpace k]
    {V : Type v} [AddCommGroup V] [Module k V] [Module.Finite k V]
    [Module.Free k V]
    {ρbar : GaloisRep ℚ k V}
    (hirrF : (ρbar.map (algebraMap ℚ F)).IsIrreducible)
    (𝒟 : HilbertDeformationDatum ℓ F ρbar) :
    ∃ hloc : IsLocalRing (hilbertTraceSubring ℓ 𝒟.ρ),
      letI := hloc
      IsNoetherianRing (hilbertTraceSubring ℓ 𝒟.ρ) ∧
      IsAdic (IsLocalRing.maximalIdeal (hilbertTraceSubring ℓ 𝒟.ρ)) ∧
      IsAdicComplete (IsLocalRing.maximalIdeal (hilbertTraceSubring ℓ 𝒟.ρ))
        (hilbertTraceSubring ℓ 𝒟.ρ) :=
  sorry

/-- **Carayol's Théorème 1 at the `F` level** (LEAF — new 2026-07-26; the
`F`-level twin of `Deformation.lean`'s `exists_framedGaloisRep_traceSubring`,
which is PROVEN there over its own three-way cut): a framed deformation
whose residual representation is irreducible is CONJUGATE, inside
`GL₂(𝒟.R)`, to one taking values in `GL₂(R')` for the closed trace subring
`R'`; and the conjugated representation still satisfies the `F`-level local
conditions.

The conclusion is stated through the characteristic polynomials rather than
through an explicit conjugating matrix, because that is all the descent
assembly needs and because the matrix is not canonical (it is unique only
up to `R'ˣ`). Irreducibility is what makes the `R'`-span of `𝒟.ρ(G_F)` a
full matrix algebra, which is Carayol's actual argument; without it the
theorem is false (a reducible `ρ` with an extension class outside `R'`
cannot be conjugated into `GL₂(R')`).

THE `ℚ`-LEVEL ROUTE, which is the one to port:
`exists_framedGaloisRep_traceSubring` is proven over
`exists_framedGaloisRep_baseChange_traceSubring` (the representation
itself, via `repr_mem_subring_of_trace_mem` and
`exists_basis_repr_mem_traceSubring`: the `R'`-span of the image is free of
rank `2`, and a basis of it has coordinates in `R'`) plus the two local
transfers `isFlatAt_of_baseChange_traceSubring` and
`isTameAtTwo_of_baseChange_traceSubring`. Here there are FOUR local clauses
to transfer, `det`, `isUnramified`, `isFlat` and `isTameAtTwo`, indexed by
places of `F` rather than by rational primes; the `det` clause is formal
(the determinant is a charpoly coefficient, so it lands in `R'` by
construction and is detected by the injective `R' → 𝒟.R`).

References: Carayol, op. cit., Théorème 1; Mazur, *Deforming Galois
representations*, §1.8. -/
theorem exists_framedGaloisRep_hilbertTraceSubring
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ5 : 5 ≤ ℓ) (F : Type u) [Field F] [NumberField F]
    {k : Type u} [Field k] [Finite k] [TopologicalSpace k]
    {V : Type v} [AddCommGroup V] [Module k V] [Module.Finite k V]
    [Module.Free k V]
    {ρbar : GaloisRep ℚ k V}
    (hirrF : (ρbar.map (algebraMap ℚ F)).IsIrreducible)
    (𝒟 : HilbertDeformationDatum ℓ F ρbar)
    (hloc : IsLocalRing (hilbertTraceSubring ℓ 𝒟.ρ)) :
    letI := hloc
    ∃ ρ' : FramedGaloisRep F (hilbertTraceSubring ℓ 𝒟.ρ) (Fin 2),
      IsHilbertHardlyRamified ℓ F
        (rank_finTwoPi (hilbertTraceSubring ℓ 𝒟.ρ)) ρ' ∧
      ∀ g : Γ F, ((ρ' g).charpoly).map (hilbertTraceSubring ℓ 𝒟.ρ).subtype =
        (𝒟.ρ g).charpoly :=
  sorry

/-- **Carayol subring-descent stratum at the `F` level** (PROVEN 2026-07-26
as glue over the two leaves above; the `F`-level twin of
`Deformation.lean`'s `exists_isTraceGenerated_ringHom_of_forall_trace_mem`,
minus its Chebotarev hypothesis, which does not arise here): every
`F`-level datum admits a *trace-generated* datum mapping compatibly INTO
it.

The descended datum is built on the coefficient ring
`R' = hilbertTraceSubring ℓ 𝒟.ρ` itself: its ring structure comes from the
first leaf, its representation from the second, its reduction map is
`𝒟.π ∘ ι` for the inclusion `ι = R'.subtype`, and its `resid` is the
factorization `map (𝒟.π ∘ ι) = map 𝒟.π ∘ map ι` through the second leaf's
charpoly clause. Surjectivity of `𝒟.π ∘ ι` onto `k` is Hensel: every
element of the FINITE `k` is the residue of a Teichmüller root
(`exists_mem_teichmullerRootSet_map_eq`), and the Teichmüller roots are
among the generators of `R'`. The two clauses of `IsTraceDescent` then hold
with `ι`: trace generation is `hilbertTraceSubring_eq_top_of_charpoly_map`,
and the three compatibilities are, respectively, the definition of the
corestricted `ℤ_ℓ`-structure map, the definition of `𝒟'.π`, and the second
leaf's charpoly clause. -/
theorem exists_hilbertTraceDescent
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ5 : 5 ≤ ℓ) (F : Type u) [Field F] [NumberField F]
    {k : Type u} [Field k] [Finite k] [TopologicalSpace k]
    {V : Type v} [AddCommGroup V] [Module k V] [Module.Finite k V]
    [Module.Free k V]
    {ρbar : GaloisRep ℚ k V} (hlk : ((ℓ : ℕ) : k) = 0)
    (hirrF : (ρbar.map (algebraMap ℚ F)).IsIrreducible)
    (𝒟 : HilbertDeformationDatum ℓ F ρbar) :
    ∃ 𝒟' : HilbertDeformationDatum ℓ F ρbar, 𝒟.IsTraceDescent 𝒟' := by
  classical
  obtain ⟨hloc, hnoeth, hadic, hcompl⟩ :=
    exists_isLocalRing_hilbertTraceSubring ℓ hℓ5 F hirrF 𝒟
  letI := hloc
  obtain ⟨ρ', hhr', hcp'⟩ :=
    exists_framedGaloisRep_hilbertTraceSubring ℓ hℓ5 F hirrF 𝒟 hloc
  refine ⟨{ R := hilbertTraceSubring ℓ 𝒟.ρ
            isLocalRing := hloc
            isNoetherianRing := hnoeth
            isAdic := hadic
            isAdicComplete := hcompl
            ρ := ρ'
            isHilbertHardlyRamified := hhr'
            π := 𝒟.π.comp (hilbertTraceSubring ℓ 𝒟.ρ).subtype
            π_surjective := ?_
            resid := ?_ }, ?_, (hilbertTraceSubring ℓ 𝒟.ρ).subtype, ?_, rfl,
          hcp'⟩
  · -- surjectivity of the descended reduction map: every element of `k` is
    -- the residue of a Teichmüller root of `𝒟.R` (Hensel), and the
    -- Teichmüller roots are generators of `R'`
    intro y
    haveI : IsAdicComplete (IsLocalRing.maximalIdeal 𝒟.R) 𝒟.R := 𝒟.isAdicComplete
    obtain ⟨x, hx, hxy⟩ :=
      exists_mem_teichmullerRootSet_map_eq (ℓ := ℓ) hlk 𝒟.π 𝒟.π_surjective y
    exact ⟨⟨x, mem_hilbertTraceSubring_of_mem_teichmullerRootSet ℓ 𝒟.ρ hx⟩, hxy⟩
  · -- residual compatibility of the descended datum
    intro g
    rw [← Polynomial.map_map, hcp' g]
    exact 𝒟.resid g
  · -- trace generation of the descended datum
    exact hilbertTraceSubring_eq_top_of_charpoly_map ℓ 𝒟.ρ ρ' hcp'
  · -- the `ℤ_ℓ`-structure map of the descended datum
    exact RingHom.ext fun c => rfl

/-- **Carayol trace descent at the `F` level** (PROVEN 2026-07-26 as
composition glue over the two arithmetic leaves
`exists_isLocalRing_hilbertTraceSubring` and
`exists_framedGaloisRep_hilbertTraceSubring`, through
`exists_hilbertTraceDescent`; the `F`-level twin of `Deformation.lean`'s
PROVEN `exists_isWeaklyUniversal_isTraceGenerated_of_isWeaklyUniversal`): a
weakly universal `F`-level datum may be replaced by one that is ALSO
trace-generated.

THE GLUE, which is all this declaration is: the descent produces `𝒟'`
together with a compatible ring homomorphism `ι : 𝒟'.R → 𝒟.R` (the trace
subring inclusion), and `𝒟'` is weakly universal because any datum `𝒟''`
receives `f : 𝒟.R → 𝒟''.R` from weak universality of `𝒟`, and `f ∘ ι` is
compatible since every piece of compatibility data — the `ℤ_ℓ`-structure
map, the reduction map, the charpoly coefficients — composes.

WHY THIS NODE EXISTS AT ALL:
`exists_isWeaklyUniversal_hilbertDeformationDatum` produces only weak
universality, and the faithfulness audit at the head of this section shows
that weak universality alone cannot support `R_F = T_F`. This is the step
that supplies the missing hypothesis.

HYPOTHESES ADDED 2026-07-26 (`[Finite k]`, `hlk`, `hℓ5`): see the
faithfulness note at the head of this subsection. All three are discharged
for free at the sole consumer. -/
theorem exists_isWeaklyUniversal_isTraceGenerated_hilbertDeformationDatum
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ5 : 5 ≤ ℓ) (F : Type u) [Field F] [NumberField F]
    {k : Type u} [Field k] [Finite k] [TopologicalSpace k]
    {V : Type v} [AddCommGroup V] [Module k V] [Module.Finite k V]
    [Module.Free k V]
    {ρbar : GaloisRep ℚ k V} (hlk : ((ℓ : ℕ) : k) = 0)
    (hirrF : (ρbar.map (algebraMap ℚ F)).IsIrreducible)
    (𝒟 : HilbertDeformationDatum ℓ F ρbar) (h𝒟 : 𝒟.IsWeaklyUniversal) :
    ∃ 𝒟' : HilbertDeformationDatum ℓ F ρbar,
      𝒟'.IsWeaklyUniversal ∧ 𝒟'.IsTraceGenerated := by
  obtain ⟨𝒟', ht', ι, hι1, hι2, hι3⟩ :=
    exists_hilbertTraceDescent ℓ hℓ5 F hlk hirrF 𝒟
  refine ⟨𝒟', ?_, ht'⟩
  intro 𝒟''
  obtain ⟨f, hf1, hf2, hf3⟩ := h𝒟 𝒟''
  refine ⟨f.comp ι, ?_, ?_, ?_⟩
  · rw [RingHom.comp_assoc, hι1, hf1]
  · rw [← RingHom.comp_assoc, hf2, hι2]
  · intro g
    rw [← Polynomial.map_map, hι3 g, hf3 g]

/-! #### The three halves of `R_F = T_F`

The cut below is `Modularity/Patching.lean`'s, transported to the `F` level.
That module proves the `ℚ`-level statement in exactly two pieces —
`surjective_ringHom_of_charFrob_eq` (Carayol generation) and
`injective_ringHom_of_isWeaklyUniversal` (Taylor–Wiles patching) — applied to
a ring homomorphism `ψ : R_univ → 𝕋` whose source and target are handed to it
as separate packets of hypotheses.

Here a third piece is needed first, and it is the one the `ℚ`-level module
does not have to state: over `ℚ` the Hecke packet arrives from `Interface.lean`
already carrying its topology (`IsModuleTopology ℤ_[p] T`), its
`IsHardlyRamified` representation and its reduction map, whereas here the
Hecke input is a `HilbertHeckeAlgebra`, which pins no topology, and the target
of the classifying map must be an object of the `F`-level deformation
CATEGORY. Manufacturing that object out of the automorphic input is
`exists_hilbertHeckeDatum_of_hilbertHeckeAlgebra`, and it is where level
lowering over totally real fields sits.

Why the classifying map is not left implicit: `IsWeaklyUniversal` produces it
with its three compatibilities, and those three are exactly the hypotheses the
two halves consume, so passing `ψ` explicitly keeps each half a statement
about a MAP rather than about an existential, which is what makes them
independently attackable and independently auditable. -/

/-- **The Hecke algebra of the matching level is an object of the `F`-level
deformation category** (LEAF — new 2026-07-26; the automorphic half of
`R_F = T_F`, and the piece with no `ℚ`-level counterpart).

Given the residual-modularity input `T₀`, produce a Hilbert Hecke algebra `T`
— of the level and weight matching the deformation condition, which need not
be `T₀`'s — together with a `HilbertDeformationDatum` whose coefficient ring
IS `T.T`.

WHAT THIS ASKS FOR, and why each part is genuine arithmetic:

* **Level lowering over `F`** (Fujiwara, Jarvis, Rajaei). `T₀` is the Hecke
  algebra of the newform Taylor's potential-modularity theorem produces, which
  is of SOME level; `HilbertDeformationDatum` requires
  `IsHilbertHardlyRamified`, i.e. the MINIMAL level — unramified outside the
  places over `2ℓ`, flat over `ℓ`, tame with square-trivial unramified
  quotient character over `2`. Passing from `T₀` to the minimal-level `T` is
  level lowering. `HilbertHeckeAlgebra` already carries
  `isHilbertHardlyRamified` for its own `ρT`, so formally this clause is
  inherited; what is NOT inherited is everything in the next two items, and
  the classical content of producing such a `T` at all is level lowering.
* **The adic topology and completeness.** `HilbertHeckeAlgebra` fixes only
  `IsTopologicalRing T`; `HilbertDeformationDatum` demands
  `IsAdic (maximalIdeal R)`, `IsAdicComplete` and `IsNoetherianRing`. For a
  local `T` that is module-finite over `ℤ_[ℓ]` all three hold classically —
  `T` is Noetherian because `ℤ_[ℓ]` is and `T` is a finite algebra over it,
  and the maximal-adic topology agrees with the `ℓ`-adic one because `T/ℓT`
  is Artinian local — but the topology `T` CARRIES is not thereby the adic
  one, and `ρT`'s continuity is asserted for the topology it carries. This is
  a genuine gap in the interface and it is recorded here rather than papered
  over; the honest fix, if this leaf is ever attacked, is to pin the topology
  in `HilbertHeckeAlgebra` (as `Modularity/Patching.lean` does with
  `[IsModuleTopology ℤ_[p] T]`) and re-derive `isHilbertHardlyRamified`.
* **The residual frame.** A datum needs `π` SURJECTIVE onto `k` and `resid` at
  every `g ∈ G_F`; `HilbertHeckeAlgebra` supplies `πT_surjective` and `residT`
  since the 2026-07-26 repair, so this part is now inherited rather than
  assumed. Before that repair this leaf would have been FALSE — see the
  FAITHFULNESS AUDIT in `HilbertHeckeAlgebra`'s docstring.

`𝒟₀` is passed because the produced datum must live in a category this leaf
is entitled to assume nonempty; `hℓ5`, `htr` and `hgal` because the newform
whose Hecke algebra `T` is exists only for `ℓ ≥ 5` over a totally real `F`
Galois over `ℚ`.

CONCLUSION STRENGTHENED 2026-07-26 (`Nonempty (𝒟T.R ≃ₐ T.T)` ⇝ an
isomorphism CARRYING THE CHARPOLY COMPATIBILITY). A bare algebra isomorphism
does not say that the datum's representation is the Hecke one, and the
consumer `surjective_classifyingMap_hilbertHeckeDatum` is UNPROVABLE without
that link — see the faithfulness repair in its docstring. Nothing arithmetic
is added: the datum this leaf produces IS `(T.T, ρT, πT)` with its adic
topology supplied, so `e` is the identity up to transport and the extra
clause is `rfl` on the nose for any honest construction. The clause is
written with `charpoly` at every `g ∈ G_F` to match `resid`, `residT` and the
`IsWeaklyUniversal` compatibilities, which are all stated that way.

References: Carayol, *Sur les représentations `ℓ`-adiques associées aux formes
modulaires de Hilbert*, Ann. Sci. ÉNS 19 (1986); Taylor, *On Galois
representations associated to Hilbert modular forms*, Invent. Math. 98 (1989);
Fujiwara, *Deformation rings and Hecke algebras in the totally real case*;
Jarvis, *Level lowering for modular mod `ℓ` representations over totally real
fields*, Math. Ann. 313 (1999); Rajaei, *On the levels of mod `ℓ` Hilbert
modular forms*, J. reine angew. Math. 537 (2001). -/
theorem exists_hilbertHeckeDatum_of_hilbertHeckeAlgebra
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ5 : 5 ≤ ℓ)
    (F : Type u) [Field F] [NumberField F]
    {k : Type u} [Field k] [TopologicalSpace k]
    {V : Type v} [AddCommGroup V] [Module k V] [Module.Finite k V]
    [Module.Free k V]
    {ρbar : GaloisRep ℚ k V}
    (htr : NumberField.IsTotallyReal F) (hgal : IsGalois ℚ F)
    (hirrF : (ρbar.map (algebraMap ℚ F)).IsIrreducible)
    (𝒟₀ : HilbertDeformationDatum ℓ F ρbar)
    (T₀ : HilbertHeckeAlgebra ℓ F ρbar) :
    ∃ (T : HilbertHeckeAlgebra ℓ F ρbar) (𝒟T : HilbertDeformationDatum ℓ F ρbar)
      (e : 𝒟T.R ≃ₐ[ℤ_[ℓ]] T.T), ∀ g : Γ F,
        ((𝒟T.ρ g).charpoly).map e.toAlgHom.toRingHom = (T.ρT g).charpoly :=
  sorry

/-! #### Teichmüller lifting into a closed subring

The three ring-theoretic lemmas below and the Hensel argument they feed are
step 3 of `surjective_classifyingMap_hilbertHeckeDatum`: the image of the
classifying map, being closed and having full residue field, already contains
every Teichmüller root of the target. They are stated for an abstract adic
local ring rather than for `𝒟T.R` because nothing in them is deformation
theory. -/

/-- `a ≡ b` modulo an ideal is preserved by taking `t`-th powers:
`a ^ t − b ^ t = (∑ a^i b^{t−1−i}) · (a − b)`. -/
lemma pow_sub_pow_mem_of_sub_mem {R : Type*} [CommRing R] {J : Ideal R} {a b : R}
    (t : ℕ) (hab : a - b ∈ J) : a ^ t - b ^ t ∈ J := by
  rw [← geom_sum₂_mul a b t]
  exact Ideal.mul_mem_left _ _ hab

/-- **The `ℓ`-th power map contracts congruences by one step of the
`I`-adic filtration**, whenever `ℓ ∈ I`: if `a − b ∈ I ^ m` with `m ≥ 1`
then `a ^ ℓ − b ^ ℓ ∈ I ^ (m + 1)`.

`a ^ ℓ − b ^ ℓ = S · (a − b)` with `S = ∑_{i < ℓ} a^i b^{ℓ−1−i}`, and modulo
`I` every summand is `b ^ (ℓ − 1)`, so `S ≡ ℓ · b ^ (ℓ − 1) ≡ 0`. -/
lemma pow_sub_pow_mem_pow_succ_of_natCast_mem {R : Type*} [CommRing R]
    {I : Ideal R} {ℓ : ℕ} (hl : ((ℓ : ℕ) : R) ∈ I) {a b : R} {m : ℕ}
    (hm : 1 ≤ m) (hab : a - b ∈ I ^ m) : a ^ ℓ - b ^ ℓ ∈ I ^ (m + 1) := by
  have hab' : Ideal.Quotient.mk I a = Ideal.Quotient.mk I b := by
    rw [← sub_eq_zero, ← map_sub, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.pow_le_self (by omega) hab
  have hS : (∑ i ∈ Finset.range ℓ, a ^ i * b ^ (ℓ - 1 - i)) ∈ I := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sum]
    have hterm : ∀ i ∈ Finset.range ℓ,
        Ideal.Quotient.mk I (a ^ i * b ^ (ℓ - 1 - i))
          = Ideal.Quotient.mk I b ^ (ℓ - 1) := by
      intro i hi
      rw [map_mul, map_pow, map_pow, hab', ← pow_add]
      congr 1
      simp only [Finset.mem_range] at hi
      omega
    rw [Finset.sum_congr rfl hterm, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    have hlz : ((ℓ : ℕ) : R ⧸ I) = 0 := by
      rw [← map_natCast (Ideal.Quotient.mk I) ℓ, Ideal.Quotient.eq_zero_iff_mem]
      exact hl
    rw [hlz, zero_mul]
  rw [← geom_sum₂_mul a b ℓ, pow_succ']
  exact Ideal.mul_mem_mul hS hab

/-- The `ℓ ^ n`-th power version of the previous lemma, for `n ≥ 1`: raise to
the `ℓ ^ (n − 1)` (which preserves the congruence) and then to the `ℓ`. -/
lemma pow_pow_sub_pow_pow_mem_pow_succ_of_natCast_mem {R : Type*} [CommRing R]
    {I : Ideal R} {ℓ : ℕ} (hl : ((ℓ : ℕ) : R) ∈ I) {a b : R} {m n : ℕ}
    (hm : 1 ≤ m) (hn : 1 ≤ n) (hab : a - b ∈ I ^ m) :
    a ^ ℓ ^ n - b ^ ℓ ^ n ∈ I ^ (m + 1) := by
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
  have h1 : a ^ ℓ ^ n' - b ^ ℓ ^ n' ∈ I ^ m := pow_sub_pow_mem_of_sub_mem _ hab
  have h2 := pow_sub_pow_mem_pow_succ_of_natCast_mem hl hm h1
  rwa [← pow_mul, ← pow_mul, ← pow_succ] at h2

/-- **Teichmüller roots lie in every closed subring with full residue field**
(PROVEN 2026-07-26; step 3 of `surjective_classifyingMap_hilbertHeckeDatum`
below, and the reason the strengthened `adjoin_heckeT` is usable at all).

`R` is local, carries its maximal-adic topology, is complete and separated
for it, has `ℓ` in its maximal ideal, and `π` presents `k` as its residue
field. If a CLOSED subring `C ⊆ R` already surjects onto `k` then `C`
contains every `ℓ`-power Teichmüller root of `R`.

ROUTE (elementary Hensel). Let `y ^ ℓ ^ n = y` with `n > 0` and choose
`x ∈ C` with `π x = π y`. Then `π (x ^ ℓ ^ n) = (π y) ^ ℓ ^ n = π y = π x`,
so `x ^ ℓ ^ n − x ∈ ker π = 𝔪`; and since `ℓ ∈ 𝔪` the `ℓ ^ n`-th power map
contracts the `𝔪`-adic filtration by one step
(`pow_pow_sub_pow_pow_mem_pow_succ_of_natCast_mem`), so `j ↦ x ^ (ℓ ^ n) ^ j`
is Cauchy. `IsAdicComplete` produces a limit `L`, which lies in `C` because
`C` is closed, satisfies `L ^ ℓ ^ n = L` because the `ℓ ^ n`-th power map is
continuous and shifts the sequence, and has `π L = π y`. So `L` and `y` are
Teichmüller roots with the same residue, and
`eq_of_mem_teichmullerRootSet` identifies them. -/
lemma teichmullerRootSet_subset_of_isClosed {ℓ : ℕ} [Fact ℓ.Prime]
    {R : Type*} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    [IsLocalRing R] (hadic : IsAdic (IsLocalRing.maximalIdeal R))
    [IsAdicComplete (IsLocalRing.maximalIdeal R) R]
    {k : Type*} [Field k] (π : R →+* k)
    (hlR : ((ℓ : ℕ) : R) ∈ IsLocalRing.maximalIdeal R)
    (C : Subring R) (hCclosed : IsClosed (C : Set R))
    (hCπ : ∀ c : k, ∃ x ∈ C, π x = c) :
    teichmullerRootSet ℓ R ⊆ (C : Set R) := by
  classical
  set I : Ideal R := IsLocalRing.maximalIdeal R with hIdef
  have hπsurj : Function.Surjective π := fun c => by
    obtain ⟨x, _, hx⟩ := hCπ c
    exact ⟨x, hx⟩
  have hker : RingHom.ker π = I := IsLocalRing.ker_eq_maximalIdeal π hπsurj
  haveI : T2Space R := t2Space_of_isAdic_of_isHausdorff hadic
  intro y hyT
  obtain ⟨n, hn, hy⟩ := hyT
  obtain ⟨x, hxC, hx⟩ := hCπ (π y)
  set f : ℕ → R := fun j => x ^ (ℓ ^ n) ^ j with hfdef
  have hfe : ∀ i : ℕ, f (i + 1) = f i ^ ℓ ^ n := by
    intro i
    show x ^ (ℓ ^ n) ^ (i + 1) = (x ^ (ℓ ^ n) ^ i) ^ ℓ ^ n
    rw [pow_succ (ℓ ^ n) i, pow_mul]
  have hπf : π (f 1) = π y := by
    have h1 : π (f 1) = π y ^ ℓ ^ n := by
      simp only [hfdef, pow_one, map_pow, hx]
    rw [h1, ← map_pow, hy]
  have hπf0 : π (f 0) = π y := by
    simp only [hfdef, pow_zero, pow_one, hx]
  -- the sequence is Cauchy for the `I`-adic filtration
  have hstep : ∀ j : ℕ, f j - f (j + 1) ∈ I ^ (j + 1) := by
    intro j
    induction j with
    | zero =>
      rw [pow_one, ← hker, RingHom.mem_ker, map_sub, hπf, hπf0, sub_self]
    | succ j ih =>
      have h2 := pow_pow_sub_pow_pow_mem_pow_succ_of_natCast_mem (I := I) hlR
        (m := j + 1) (n := n) (by omega) hn ih
      rwa [← hfe, ← hfe] at h2
  have hmono : ∀ m j : ℕ, m ≤ j → f m - f j ∈ I ^ m := by
    intro m j hmj
    induction j, hmj using Nat.le_induction with
    | base => simp
    | succ j hj ih =>
      have h1 : f m - f (j + 1) = (f m - f j) + (f j - f (j + 1)) := by ring
      rw [h1]
      exact Ideal.add_mem _ ih (Ideal.pow_le_pow_right (by omega) (hstep j))
  obtain ⟨L, hL⟩ := IsPrecomplete.prec (inferInstance : IsPrecomplete I R) (f := f)
    (fun {m j} hmj => by
      rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top]
      exact hmono m j hmj)
  have hLmem : ∀ j : ℕ, f j - L ∈ I ^ j := by
    intro j
    have h := hL j
    rwa [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top] at h
  -- the limit lies in `C`, is a Teichmüller root, and has the residue of `y`
  have h0 : Filter.Tendsto (fun j => f j - L) Filter.atTop (nhds 0) := by
    rw [hadic.hasBasis_nhds_zero.tendsto_right_iff]
    intro m _
    filter_upwards [Filter.eventually_ge_atTop m] with j hj
    exact Ideal.pow_le_pow_right hj (hLmem j)
  have htend : Filter.Tendsto f Filter.atTop (nhds L) := by
    have hc : Filter.Tendsto (fun _ : ℕ => L) Filter.atTop (nhds L) := tendsto_const_nhds
    have h := h0.add hc
    simpa using h
  have hLC : L ∈ C :=
    hCclosed.mem_of_tendsto htend
      (Filter.Eventually.of_forall fun j => C.pow_mem hxC _)
  have hLpow : L ^ ℓ ^ n = L := by
    have h1 : Filter.Tendsto (fun j => f (j + 1)) Filter.atTop (nhds L) :=
      htend.comp (Filter.tendsto_add_atTop_nat 1)
    have h2 : Filter.Tendsto (fun j => f j ^ ℓ ^ n) Filter.atTop (nhds (L ^ ℓ ^ n)) :=
      htend.pow _
    have h3 : (fun j => f (j + 1)) = fun j => f j ^ ℓ ^ n := funext hfe
    rw [h3] at h1
    exact tendsto_nhds_unique h2 h1
  have hπL : π L = π y := by
    have h1 : f 1 - L ∈ I := by simpa using hLmem 1
    have h2 : π (f 1) - π L = 0 := by
      rw [← map_sub, ← RingHom.mem_ker, hker]
      exact h1
    rw [sub_eq_zero] at h2
    rw [← h2, hπf]
  have hyL : y - L ∈ I := by
    rw [← hker, RingHom.mem_ker, map_sub, hπL, sub_self]
  have hyeq : y = L :=
    eq_of_mem_teichmullerRootSet hlR ⟨n, hn, hy⟩ ⟨n, hn, hLpow⟩ hyL
  rw [hyeq]
  exact hLC

/-- **`R_F ↠ T_F`: the classifying map is SURJECTIVE** (PROVEN 2026-07-26
after the FAITHFULNESS REPAIR recorded below; the `F`-level twin of
`Modularity/Patching.lean`'s `surjective_ringHom_of_charFrob_eq`, which is
PROVEN there over one arithmetic leaf).

## THE 2026-07-26 FAITHFULNESS REPAIR: `e` HAD NO LINK TO `T.ρT`

As first written this statement was **not provable**, for the fifth instance
of this module's recurring defect — a hypothesis the argument needs and the
statement omits. `e : 𝒟T.R ≃ₐ[ℤ_[ℓ]] T.T` was a BARE algebra isomorphism.
Everything the conclusion can possibly use about `T` enters through
`adjoin_heckeT`, whose generating set is `T.heckeT`, i.e. the Frobenius
traces of `T.ρT`; and the only fact the hypotheses record about the target's
representation is `hψρ`, about `𝒟T.ρ`. With `e` unconstrained, the two
representations are unrelated, so no argument can carry a Hecke operator into
the image of `ψ`: the Teichmüller half of the generating set is reachable
(step 3 below needs only that `ψ` is local and its image closed) and the
Hecke half is not. Concretely, replacing `𝒟T.ρ` by any representation with
the same charpolys and `e` by `e` composed with a `ℤ_[ℓ]`-algebra
automorphism of `T.T` leaves every hypothesis intact and moves the generating
set; nothing pins them together.

The repair is the one the module already uses three times over (`resid`,
`residT`, `hψρ`): a charpoly compatibility, here `he`, saying that `e`
identifies `𝒟T.ρ` with `T.ρT`. It costs the consumer nothing — it is exactly
what `exists_hilbertHeckeDatum_of_hilbertHeckeAlgebra` manufactures, since
the datum it produces IS the Hecke datum `(T.T, ρT, πT)` transported, and
that leaf's conclusion was strengthened to record it (its `sorry` is
unchanged and its arithmetic content — level lowering, the topology gap — is
untouched).

THE ARGUMENT, which is formal once the two generation statements are lined up
— and they now are, clause for clause, by the 2026-07-26 repair of
`adjoin_heckeT`:

1. `Set.range ψ` is a `ℤ_[ℓ]`-subalgebra of `𝒟T.R` (by `hψalg`), and `𝒟T.R`
   is `ℤ_[ℓ]`-module-finite because it is `T.T` (transport along `e`), so the
   range is a finitely generated `ℤ_[ℓ]`-submodule of it, hence compact
   (`Submodule.isCompact_of_fg`, `PadicInt.compactSpace`) and therefore
   CLOSED — `𝒟T.R` is Hausdorff by `t2Space_of_isAdic_of_isHausdorff`. This
   is `Patching.lean`'s argument verbatim, except that the `ContinuousSMul`
   it gets free from `IsModuleTopology` has to be produced here from the
   continuity of `algebraMap ℤ_[ℓ] 𝒟T.R`, which is proven from the adic
   topology and `ℓ ∈ 𝔪`; and `ℓ ∈ 𝔪` is itself Nakayama, since a module-finite
   `ℤ_[ℓ]`-algebra in which `ℓ` is invertible vanishes.
2. The range contains every `charpoly` coefficient of `𝒟T.ρ`, by `hψρ`; in
   particular `e` carries it onto the Hecke operators, since
   `T.heckeT w = -(T.ρT.charFrob w).coeff 1` (`charFrobT`), `charFrob` is a
   `charpoly` at a Frobenius element, and `he` identifies the two charpolys.
3. The range contains every Teichmüller root of `𝒟T.R`
   (`teichmullerRootSet_subset_of_isClosed` above). This is the step that
   the old `adjoin_heckeT` did not need and could not have: `ψ` is LOCAL
   (`hψπ` makes `𝒟T.π ∘ ψ = 𝒟.π`, which is surjective), so the range is a
   closed local subring with residue field all of `k`.
4. So the closed range contains, after transport along `e`, the whole
   generating set of `adjoin_heckeT` — and that adjoin is already `⊤` with no
   closure taken, so `e '' (range ψ) = ⊤` and `ψ` is surjective.

`h𝒟t` (trace generation of the SOURCE), `h𝒟w` and `hirrF` are not used by
this route and are carried, underscore-prefixed, only so that the two halves
of `R_F = T_F` present the same interface to their common consumer. -/

theorem surjective_classifyingMap_hilbertHeckeDatum
    (ℓ : ℕ) [Fact ℓ.Prime]
    (F : Type u) [Field F] [NumberField F]
    {k : Type u} [Field k] [TopologicalSpace k]
    {V : Type v} [AddCommGroup V] [Module k V] [Module.Finite k V]
    [Module.Free k V]
    {ρbar : GaloisRep ℚ k V}
    (_hirrF : (ρbar.map (algebraMap ℚ F)).IsIrreducible)
    (𝒟 𝒟T : HilbertDeformationDatum ℓ F ρbar)
    (T : HilbertHeckeAlgebra ℓ F ρbar) (e : 𝒟T.R ≃ₐ[ℤ_[ℓ]] T.T)
    (he : ∀ g : Γ F,
      ((𝒟T.ρ g).charpoly).map e.toAlgHom.toRingHom = (T.ρT g).charpoly)
    (_h𝒟w : 𝒟.IsWeaklyUniversal) (_h𝒟t : 𝒟.IsTraceGenerated)
    (ψ : 𝒟.R →+* 𝒟T.R)
    (hψalg : ψ.comp (algebraMap ℤ_[ℓ] 𝒟.R) = algebraMap ℤ_[ℓ] 𝒟T.R)
    (hψπ : 𝒟T.π.comp ψ = 𝒟.π)
    (hψρ : ∀ g : Γ F, ((𝒟.ρ g).charpoly).map ψ = (𝒟T.ρ g).charpoly) :
    Function.Surjective ψ := by
  classical
  -- `ψ` as a `ℤ_[ℓ]`-algebra homomorphism
  let ψa : 𝒟.R →ₐ[ℤ_[ℓ]] 𝒟T.R :=
    { toRingHom := ψ, commutes' := fun c => RingHom.congr_fun hψalg c }
  -- (0) `𝒟T.R` is `ℤ_[ℓ]`-module-finite, transported from `T.T` along `e`
  haveI hfin : Module.Finite ℤ_[ℓ] 𝒟T.R := Module.Finite.equiv e.symm.toLinearEquiv
  -- (1) `ℓ` is a nonunit of `𝒟T.R`: were it a unit, Nakayama would collapse
  -- the module-finite `𝒟T.R` to `0`, and a local ring is nontrivial.
  have hlR : ((ℓ : ℕ) : 𝒟T.R) ∈ IsLocalRing.maximalIdeal 𝒟T.R := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    obtain ⟨v, hv⟩ := hu.exists_right_inv
    have hle : (⊤ : Submodule ℤ_[ℓ] 𝒟T.R) ≤
        (IsLocalRing.maximalIdeal ℤ_[ℓ]) • (⊤ : Submodule ℤ_[ℓ] 𝒟T.R) := by
      intro x _
      have hx : x = ((ℓ : ℕ) : ℤ_[ℓ]) • (v * x) := by
        rw [Algebra.smul_def, map_natCast, ← mul_assoc, hv, one_mul]
      rw [hx]
      refine Submodule.smul_mem_smul ?_ Submodule.mem_top
      rw [PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton]
    have htop : (⊤ : Submodule ℤ_[ℓ] 𝒟T.R) = ⊥ :=
      Submodule.eq_bot_of_le_smul_of_le_jacobson_bot _ _ (Module.Finite.fg_top) hle
        (le_of_eq (IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top).symm)
    have h1 : (1 : 𝒟T.R) ∈ (⊥ : Submodule ℤ_[ℓ] 𝒟T.R) := htop ▸ Submodule.mem_top
    rw [Submodule.mem_bot] at h1
    exact one_ne_zero h1
  -- (2) the structure map is continuous for the maximal-adic topology of `𝒟T.R`
  have hcont : Continuous (algebraMap ℤ_[ℓ] 𝒟T.R) := by
    apply continuous_of_continuousAt_zero
    unfold ContinuousAt
    rw [map_zero, 𝒟T.isAdic.hasBasis_nhds_zero.tendsto_right_iff]
    intro n _
    have hpos : (0 : ℝ) < (ℓ : ℝ) ^ (-(n : ℤ)) :=
      zpow_pos (by exact_mod_cast (Fact.out : ℓ.Prime).pos) _
    filter_upwards [Metric.closedBall_mem_nhds (0 : ℤ_[ℓ]) hpos] with x hx
    have hx' : x ∈ Ideal.span {(ℓ : ℤ_[ℓ]) ^ n} := by
      rw [← PadicInt.norm_le_pow_iff_mem_span_pow]
      simpa [Metric.mem_closedBall, dist_zero_right] using hx
    obtain ⟨y, rfl⟩ := Ideal.mem_span_singleton'.mp hx'
    have hsplit : algebraMap ℤ_[ℓ] 𝒟T.R (y * (ℓ : ℤ_[ℓ]) ^ n) =
        algebraMap ℤ_[ℓ] 𝒟T.R y * ((ℓ : ℕ) : 𝒟T.R) ^ n := by
      rw [map_mul, map_pow, map_natCast]
    rw [SetLike.mem_coe, hsplit]
    exact Ideal.mul_mem_left _ _ (Ideal.pow_mem_pow hlR n)
  haveI : ContinuousSMul ℤ_[ℓ] 𝒟T.R := continuousSMul_of_algebraMap ℤ_[ℓ] 𝒟T.R hcont
  -- (3) `𝒟T.R` is Hausdorff
  haveI : IsAdicComplete (IsLocalRing.maximalIdeal 𝒟T.R) 𝒟T.R := 𝒟T.isAdicComplete
  haveI : T2Space 𝒟T.R := t2Space_of_isAdic_of_isHausdorff 𝒟T.isAdic
  -- (4) the range of `ψ` is closed: finitely generated over `ℤ_[ℓ]`, hence compact
  have hCclosed : IsClosed ((ψa.range : Subalgebra ℤ_[ℓ] 𝒟T.R) : Set 𝒟T.R) := by
    have hc := (Submodule.isCompact_of_fg
      (IsNoetherian.noetherian (Subalgebra.toSubmodule ψa.range))).isClosed
    simpa using hc
  -- (5) the range contains every Teichmüller root, since it is closed and
  -- surjects onto `k` (`hψπ` and `𝒟.π_surjective`)
  have hteich : teichmullerRootSet ℓ 𝒟T.R ⊆ (ψa.range.toSubring : Set 𝒟T.R) := by
    refine teichmullerRootSet_subset_of_isClosed 𝒟T.isAdic 𝒟T.π hlR
      ψa.range.toSubring (by simpa using hCclosed) ?_
    intro c
    obtain ⟨r, hr⟩ := 𝒟.π_surjective c
    refine ⟨ψ r, ⟨r, rfl⟩, ?_⟩
    rw [← hr, ← hψπ]
    rfl
  -- (6) transport the range to `T.T`; it contains `adjoin_heckeT`'s generators
  set D : Subalgebra ℤ_[ℓ] T.T := ψa.range.map e.toAlgHom with hD
  have hgen : ({x : T.T | ∃ n : ℕ, 0 < n ∧ x ^ ℓ ^ n = x} ∪
      T.heckeT '' {w | w ∉ T.bad}) ⊆ (D : Set T.T) := by
    rintro x (hx | ⟨w, hw, rfl⟩)
    · have hy : e.symm x ∈ teichmullerRootSet ℓ 𝒟T.R :=
        map_mem_teichmullerRootSet e.symm.toAlgHom.toRingHom hx
      refine ⟨e.symm x, hteich hy, ?_⟩
      simp
    · -- the Hecke operator at a good place is a Frobenius trace of `𝒟T.ρ`
      set gw : Γ F := Field.absoluteGaloisGroup.map (algebraMap F (w.adicCompletion F))
        (Field.AbsoluteGaloisGroup.adicArithFrob w) with hgw
      have hcf : ((𝒟T.ρ gw).charpoly).map e.toAlgHom.toRingHom = T.ρT.charFrob w := he gw
      have hcoeff : e ((𝒟T.ρ gw).charpoly.coeff 1) = (T.ρT.charFrob w).coeff 1 := by
        rw [← hcf, Polynomial.coeff_map]
        rfl
      have hψc : (𝒟T.ρ gw).charpoly.coeff 1 = ψ ((𝒟.ρ gw).charpoly.coeff 1) := by
        rw [← hψρ gw, Polynomial.coeff_map]
      refine ⟨ψ (-((𝒟.ρ gw).charpoly.coeff 1)), ⟨-((𝒟.ρ gw).charpoly.coeff 1), rfl⟩, ?_⟩
      have hneg : e (ψ ((𝒟.ρ gw).charpoly.coeff 1)) = -T.heckeT w := by
        rw [← hψc, hcoeff, T.charFrobT w hw]
      show e (ψ (-((𝒟.ρ gw).charpoly.coeff 1))) = T.heckeT w
      rw [map_neg, map_neg, hneg, neg_neg]
  -- (7) `adjoin_heckeT` is an honest `Algebra.adjoin`, so no closure is needed
  have hDtop : D = ⊤ := by
    refine top_le_iff.mp ?_
    rw [← T.adjoin_heckeT]
    exact Algebra.adjoin_le hgen
  intro y
  have hy : e y ∈ D := hDtop ▸ Algebra.mem_top
  rw [hD] at hy
  obtain ⟨z, hz, hez⟩ := hy
  obtain ⟨r, hr⟩ := hz
  refine ⟨r, ?_⟩
  have hey : e (ψ r) = e y := by rw [hr]; exact hez
  exact e.injective hey

/-- **`R_F ↪ T_F`: the classifying map is INJECTIVE** (LEAF — new 2026-07-26;
the `F`-level twin of `Modularity/Patching.lean`'s
`injective_ringHom_of_isWeaklyUniversal`, and the mathematical heart of the
whole module).

This is Taylor–Wiles–Kisin patching over a totally real field. Auxiliary sets
`Q_n` of Taylor–Wiles primes of `F` (places `w` with `N w ≡ 1 mod ℓ ^ n` and
`ρbar(Frob_w)` having distinct eigenvalues, produced by Chebotarev from
`hirrF`, which needs `ℓ > 2` — hence `hℓ5`); the augmented deformation rings
and the auxiliary Hilbert modular Hecke modules at level `Q_n`; patching to a
power-series situation where a commutative-algebra dimension count forces
`R_∞ = T_∞`, which descends to `R_F = T_F`. Total realness of `F` is what
makes the Selmer / dual-Selmer count come out (the archimedean local terms of
the Greenberg–Wiles formula), and `IsGalois ℚ F` is what lets Brauer induction
descend the base change.

`h𝒟t` IS used here, and load-bearing: patching identifies `ψ` with THE
classifying map, which requires the source to be genuinely universal rather
than merely weakly so — see `isUniversal_of_isWeaklyUniversal_isTraceGenerated`
above and the faithfulness audit at the head of this section, where
`𝒟₀.R⟦X⟧` is a weakly universal datum admitting a compatible non-injective
map to the very same target.

WHAT IS AVAILABLE TO PORT: `Modularity/Patching.lean` carries the entire
`ℚ`-level development — `IsTaylorWilesPrimeSet`, `exists_taylorWilesPrimeSet`,
`TaylorWilesSystem`, `PatchedModule` and its `injective`, plus the
Auslander–Buchsbaum and power-series plumbing — in about 8900 lines, of which
the commutative algebra (everything from `exists_add_notMem_of_forall_not_le`
to `free_of_isRegular_mvPowerSeries`) is base-field-independent and should be
hoisted rather than duplicated. What is genuinely `F`-specific is the
production of Taylor–Wiles primes (places of `F`, not rational primes) and the
Hecke modules of Hilbert modular forms at the augmented levels.

References: Taylor–Wiles, *Ring-theoretic properties of certain Hecke
algebras*, Ann. of Math. 141 (1995); Fujiwara, *Deformation rings and Hecke
algebras in the totally real case*; Skinner–Wiles, *Base change and a problem
of Serre*, Duke 107 (2001); Kisin, *Moduli of finite flat group schemes, and
modularity*, Ann. of Math. 170 (2009); Barnet-Lamb–Gee–Geraghty–Taylor,
*Potential automorphy and change of weight*, §§1–2. -/
theorem injective_classifyingMap_hilbertHeckeDatum
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ5 : 5 ≤ ℓ)
    (F : Type u) [Field F] [NumberField F]
    {k : Type u} [Field k] [TopologicalSpace k]
    {V : Type v} [AddCommGroup V] [Module k V] [Module.Finite k V]
    [Module.Free k V]
    {ρbar : GaloisRep ℚ k V}
    (htr : NumberField.IsTotallyReal F) (hgal : IsGalois ℚ F)
    (hirrF : (ρbar.map (algebraMap ℚ F)).IsIrreducible)
    (𝒟 𝒟T : HilbertDeformationDatum ℓ F ρbar)
    (T : HilbertHeckeAlgebra ℓ F ρbar) (e : 𝒟T.R ≃ₐ[ℤ_[ℓ]] T.T)
    (h𝒟w : 𝒟.IsWeaklyUniversal) (h𝒟t : 𝒟.IsTraceGenerated)
    (ψ : 𝒟.R →+* 𝒟T.R)
    (hψalg : ψ.comp (algebraMap ℤ_[ℓ] 𝒟.R) = algebraMap ℤ_[ℓ] 𝒟T.R)
    (hψπ : 𝒟T.π.comp ψ = 𝒟.π)
    (hψρ : ∀ g : Γ F, ((𝒟.ρ g).charpoly).map ψ = (𝒟T.ρ g).charpoly) :
    Function.Injective ψ :=
  sorry

/-- **`R_F` IS a Hilbert Hecke algebra** (PROVEN 2026-07-26 over the three
leaves above, after the FAITHFULNESS REPAIR recorded below; the
arithmetic half of item 4, Taylor–Wiles–Kisin patching in the Hilbert
modular setting).

For a residually irreducible, residually modular `ρbar|_{G_F}` over a
totally real `F`, the `F`-level universal deformation ring carries — is —
the Hecke algebra of the matching weight and level: there is a
`HilbertHeckeAlgebra` `T` and a weakly universal, trace-generated
`F`-level datum `𝒟T` whose coefficient ring is `T.T`.

THE TWO HALVES, exactly as in `Modularity/Patching.lean` at the `ℚ`
level. `R_F ↠ T_F` is surjective because `T_F` is generated by Hecke
operators (`adjoin_heckeT`), which are the Frobenius traces of the
Galois representation `ρ_T : G_F → GL₂(T_F)` that Carayol's theorem
attaches to the Hecke eigensystem (`residualT` is the residual half of
that datum); and it is injective by the Taylor–Wiles patching argument,
which uses `Module.Finite ℤ_[ℓ] T` and the numerical coincidence supplied
by auxiliary sets of Taylor–Wiles primes. Total realness of `F` is what
makes the Selmer / dual-Selmer count come out, and `IsGalois ℚ F` is what
lets Brauer induction descend the base change.

WHY THE CONCLUSION IS PHRASED AT A DATUM `𝒟T` OF THE MACHINE'S OWN
CHOOSING, and not as `Nonempty (𝒟.R ≃ₐ T₀.T)` for the given `T₀`:
`HilbertHeckeAlgebra` pins the residual eigensystem but NOT the level, and
level raising produces Hecke algebras with the same residual eigensystem
and different rings. `T₀` is the residual-modularity INPUT; the level of
the `T` in the conclusion is the one matching the deformation condition,
which the machine constructs. Any attempt to strengthen this to a
specific `T` is a FALSE statement.

WHY `𝒟T` CARRIES `IsWeaklyUniversal ∧ IsTraceGenerated` rather than an
isomorphism to a GIVEN `𝒟`: that is what makes the leaf's consumer
(`exists_heckeAlgebra_algEquiv_of_isWeaklyUniversal` below) PROVEN glue
rather than a second copy of the leaf — genuine universality is rigid, so
the given `𝒟` and the constructed `𝒟T` have canonically isomorphic rings.
It is also the honest form: the theorem in the literature is that the
universal ring is Hecke, not that some particular presentation of it is.

References: Wiles, *Modular elliptic curves and Fermat's Last Theorem*,
§2; Taylor–Wiles, *Ring-theoretic properties of certain Hecke algebras*;
Kisin, *Moduli of finite flat group schemes, and modularity*;
Barnet-Lamb–Gee–Geraghty–Taylor, *Potential automorphy and change of
weight*, §§1–2; Carayol, *Formes modulaires et représentations
galoisiennes à valeurs dans un anneau local complet*.

## THE 2026-07-26 FAITHFULNESS REPAIR OF THIS LEAF

As first written the statement carried no `𝒟₀`, and it was **FALSE for two
independent reasons**, both of which are repairs already made elsewhere in
this module and not inherited here.

1. **The deformation category may be EMPTY.** The conclusion produces a
   `𝒟T : HilbertDeformationDatum ℓ F ρbar`, so it asserts in particular that
   the category is inhabited; nothing in the old hypotheses made it so. The
   Hecke input `T₀` does not: `HilbertHeckeAlgebra` pins no topology on `T`
   beyond `IsTopologicalRing`, whereas `HilbertDeformationDatum` demands the
   MAXIMAL-ADIC one together with `IsAdicComplete`, and continuity of `ρT` for
   a coarser topology says nothing about continuity for the adic one. This is
   verbatim the defect that `exists_isWeaklyUniversal_hilbertDeformationDatum`
   was repaired for on the same day, and the repair is the same: a hypothesis
   `𝒟₀ : HilbertDeformationDatum ℓ F ρbar`. It costs the consumer below
   NOTHING — that consumer already has such a datum in hand as its own `𝒟`.

2. **The residue fields need not match.** See the FAITHFULNESS AUDIT in the
   docstring of `HilbertHeckeAlgebra`: `𝒟T.R` has residue field exactly `k`,
   while the old `adjoin_heckeT` forced the residue field of `T` to be the
   trace field of `ρbar|_{G_F}`, so the asserted isomorphism was impossible
   whenever `k` properly contains that trace field (`ρbar = ρ₀ ⊗ 𝔽_{ℓ²}` for
   an `𝔽_ℓ`-rational modular `ρ₀`, with every hypothesis satisfied). That
   repair was made in `HilbertHeckeAlgebra` — Teichmüller roots into
   `adjoin_heckeT`, `πT_surjective` added — so this statement is unchanged by
   it, and it now asks for something possible.

Neither repair weakens what the leaf claims arithmetically: `𝒟₀` is the
Schlessinger-style "the residual object is given" input that every
representability theorem has, and the Hecke-side repair only replaces the
`ℤ_[ℓ]`-Hecke algebra by its unramified base change to `W(k)`, which is the
ring the deformation-theoretic `R = T` theorem was always about.

3. **The residual field binders, added at merge on 2026-07-26.** `k` carries
   `[Finite k]`, `[DiscreteTopology k]` and `[Algebra ℤ_[ℓ] k]`, inherited
   from the two callees below — `[Finite k]` came with the proof of
   `isHilbertResidualRigidityClause`, the other two with the machine node's
   second faithfulness repair. This node is the only place in the module that
   still lacked them; the downstream consumer
   `exists_finiteIndex_isIntegral_charpolyCoeff_of_isHardlyRamified` already
   assumed all three, so nothing outside changes. -/
theorem exists_heckeDatum_isWeaklyUniversal_isTraceGenerated
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ5 : 5 ≤ ℓ)
    (F : Type u) [Field F] [NumberField F]
    {k : Type u} [Field k] [Finite k] [TopologicalSpace k]
    [DiscreteTopology k] [Algebra ℤ_[ℓ] k]
    {V : Type v} [AddCommGroup V] [Module k V] [Module.Finite k V]
    [Module.Free k V]
    {ρbar : GaloisRep ℚ k V}
    (htr : NumberField.IsTotallyReal F) (hgal : IsGalois ℚ F)
    (hirrF : (ρbar.map (algebraMap ℚ F)).IsIrreducible)
    (𝒟₀ : HilbertDeformationDatum ℓ F ρbar)
    (T₀ : HilbertHeckeAlgebra ℓ F ρbar) :
    ∃ (T : HilbertHeckeAlgebra ℓ F ρbar) (𝒟T : HilbertDeformationDatum ℓ F ρbar),
      𝒟T.IsWeaklyUniversal ∧ 𝒟T.IsTraceGenerated ∧
        Nonempty (𝒟T.R ≃ₐ[ℤ_[ℓ]] T.T) := by
  -- (1) the `F`-level universal ring, made trace-generated. Both steps are
  -- already cut leaves of this module; `𝒟₀` is what makes the first one apply.
  obtain ⟨𝒟₁, h𝒟₁⟩ :=
    exists_isWeaklyUniversal_hilbertDeformationDatum ℓ hℓ5 F hirrF 𝒟₀
  obtain ⟨𝒟, h𝒟w, h𝒟t⟩ :=
    exists_isWeaklyUniversal_isTraceGenerated_hilbertDeformationDatum ℓ hℓ5 F
      (natCast_eq_zero_of_finite_algebra ℓ k) hirrF 𝒟₁ h𝒟₁
  -- (2) the Hecke algebra of the matching level, AS AN OBJECT of the `F`-level
  -- deformation category (automorphic leaf).
  obtain ⟨T, 𝒟T, e, he⟩ :=
    exists_hilbertHeckeDatum_of_hilbertHeckeAlgebra ℓ hℓ5 F htr hgal hirrF 𝒟₀ T₀
  -- (3) the classifying map `R_F → T_F`, from weak universality of `𝒟`.
  obtain ⟨ψ, hψalg, hψπ, hψρ⟩ := h𝒟w 𝒟T
  -- (4) it is bijective — the two halves of `R = T`.
  have hsurj : Function.Surjective ψ :=
    surjective_classifyingMap_hilbertHeckeDatum ℓ F hirrF 𝒟 𝒟T T e he h𝒟w h𝒟t ψ
      hψalg hψπ hψρ
  have hinj : Function.Injective ψ :=
    injective_classifyingMap_hilbertHeckeDatum ℓ hℓ5 F htr hgal hirrF 𝒟 𝒟T T e
      h𝒟w h𝒟t ψ hψalg hψπ hψρ
  -- (5) assemble: `R_F ≃ 𝒟T.R ≃ T.T`, and `𝒟` is the datum the conclusion wants.
  refine ⟨T, 𝒟, h𝒟w, h𝒟t, ⟨AlgEquiv.trans ?_ e⟩⟩
  refine AlgEquiv.ofRingEquiv (f := RingEquiv.ofBijective ψ ⟨hinj, hsurj⟩) ?_
  intro c
  show ψ (algebraMap ℤ_[ℓ] 𝒟.R c) = algebraMap ℤ_[ℓ] 𝒟T.R c
  rw [← RingHom.comp_apply, hψalg]

/-- **`R_F = T_F`** (PROVEN 2026-07-26 over
`exists_heckeDatum_isWeaklyUniversal_isTraceGenerated` and the formal
Carayol rigidity above; item 4 of the audit's missing-machinery list —
the modularity lifting theorem over a totally real field).

Taylor–Wiles–Kisin patching in the Hilbert modular setting: for a
residually irreducible, residually modular `ρbar|_{G_F}` over a totally
real `F`, the map from the `F`-level universal deformation ring to the
Hecke algebra classifying the modular deformations is an ISOMORPHISM of
`ℤ_ℓ`-algebras.

Two halves, exactly as in `Modularity/Patching.lean` at the `ℚ`-level:
`R_F ↠ T_F` is surjective because `T_F` is generated by Hecke operators,
which are the traces of the deformation attached to the Hecke-valued
representation (`adjoin_heckeT` and `residualT` are the two fields that
make this work); and it is injective by the Taylor–Wiles patching
argument, which uses the finiteness of `T_F` and the numerical
coincidence supplied by auxiliary sets of Taylor–Wiles primes. Total
realness of `F` is what makes the Selmer / dual-Selmer count come out,
and `IsGalois ℚ F` is what lets Brauer induction descend the base change.

**THE EXISTENTIAL SHAPE IS DELIBERATE, and the obvious alternative is
FALSE.** The hypothesis `T₀` is what records residual modularity of
`ρbar|_{G_F}` — it is the INPUT of the modularity lifting theorem — and
the Hecke algebra `T` produced in the conclusion is the one of the level
and weight matching the deformation condition of `𝒟`, which the machine
constructs. Stating instead `Nonempty (𝒟.R ≃ₐ[ℤ_[ℓ]] T₀.T)` for the
GIVEN `T₀` would be false as written: `HilbertHeckeAlgebra` pins the
residual eigensystem but not the level, and level raising produces
Hecke algebras with the same residual eigensystem and different rings.
The existential form is the honest one and loses nothing downstream,
since the consumer only wants `Module.Finite ℤ_[ℓ] 𝒟.R`.

**THE `IsTraceGenerated` HYPOTHESIS IS REQUIRED — WITHOUT IT THIS
STATEMENT IS FALSE.** See the FAITHFULNESS AUDIT at the head of this
section: `𝒟₀.R⟦X⟧` is weakly universal and is not module-finite over
`ℤ_ℓ`, hence is isomorphic to no `T.T`. The hypothesis was added
2026-07-26, mirroring `Deformation.lean`'s own repair of
`moduleFinite_of_isWeaklyUniversal_isTraceGenerated` on the same day.
The side condition `hlk` (`char k = ℓ`) is what makes `ℓ` a nonunit in
the coefficient rings, which the Teichmüller half of the rigidity
argument needs; it is automatic at every intended instantiation.

The proof is now glue: the leaf produces a weakly universal,
trace-generated datum `𝒟T` whose ring IS a Hecke algebra; trace
generation upgrades both `𝒟` and `𝒟T` to genuinely universal, and
universal data are rigid, so `𝒟.R ≃ₐ 𝒟T.R ≃ₐ T.T`.

The only structural consequence used downstream is
`moduleFinite_hilbertDeformation_of_isWeaklyUniversal` below —
`Module.Finite ℤ_[ℓ] R_F`. The statement is nevertheless kept as the full
isomorphism, because that is the theorem in the literature and because a
future consumer needing the Hecke eigenvalues (rather than only their
integrality) must not have to re-derive it. -/
theorem exists_heckeAlgebra_algEquiv_of_isWeaklyUniversal
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ5 : 5 ≤ ℓ)
    (F : Type u) [Field F] [NumberField F]
    {k : Type u} [Field k] [Finite k] [TopologicalSpace k]
    [DiscreteTopology k] [Algebra ℤ_[ℓ] k]
    {V : Type v} [AddCommGroup V] [Module k V] [Module.Finite k V]
    [Module.Free k V]
    {ρbar : GaloisRep ℚ k V} (hlk : ((ℓ : ℕ) : k) = 0)
    (htr : NumberField.IsTotallyReal F) (hgal : IsGalois ℚ F)
    (hirrF : (ρbar.map (algebraMap ℚ F)).IsIrreducible)
    (𝒟 : HilbertDeformationDatum ℓ F ρbar) (h𝒟 : 𝒟.IsWeaklyUniversal)
    (ht𝒟 : 𝒟.IsTraceGenerated)
    (T₀ : HilbertHeckeAlgebra ℓ F ρbar) :
    ∃ T : HilbertHeckeAlgebra ℓ F ρbar, Nonempty (𝒟.R ≃ₐ[ℤ_[ℓ]] T.T) := by
  obtain ⟨T, 𝒟T, hwT, htT, ⟨e⟩⟩ :=
    exists_heckeDatum_isWeaklyUniversal_isTraceGenerated ℓ hℓ5 F htr hgal hirrF
      𝒟 T₀
  obtain ⟨φ, hφ⟩ :=
    HilbertDeformationDatum.exists_ringEquiv_of_isUniversal 𝒟 𝒟T
      (HilbertDeformationDatum.isUniversal_of_isWeaklyUniversal_isTraceGenerated
        hlk 𝒟 h𝒟 ht𝒟)
      (HilbertDeformationDatum.isUniversal_of_isWeaklyUniversal_isTraceGenerated
        hlk 𝒟T hwT htT)
  exact ⟨T, ⟨(AlgEquiv.ofRingEquiv (f := φ) hφ).trans e⟩⟩

/-- **`Module.Finite ℤ_[ℓ] R_F`** (PROVEN over `R_F = T_F`): the `F`-level
universal deformation ring is a finite `ℤ_ℓ`-module, because it is
isomorphic to the Hecke algebra, which is one.

This is the single consequence of the whole Hilbert-modular development
that the assembly below consumes, and it is why the route is not
circular: the finiteness is imported from the automorphic side over `F`,
where modularity is a theorem, and never from `ℚ`, where it is what
pillar α is proving.

`IsTraceGenerated` (and the `char k = ℓ` side condition) added 2026-07-26
— WITHOUT THEM THIS STATEMENT IS FALSE, by the faithfulness audit at the
head of this section. This is the exact shape `Deformation.lean` already
carries at the `ℚ` level as
`moduleFinite_of_isWeaklyUniversal_isTraceGenerated`. -/
theorem moduleFinite_hilbertDeformation_of_isWeaklyUniversal
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ5 : 5 ≤ ℓ)
    (F : Type u) [Field F] [NumberField F]
    {k : Type u} [Field k] [Finite k] [TopologicalSpace k]
    [DiscreteTopology k] [Algebra ℤ_[ℓ] k]
    {V : Type v} [AddCommGroup V] [Module k V] [Module.Finite k V]
    [Module.Free k V]
    {ρbar : GaloisRep ℚ k V} (hlk : ((ℓ : ℕ) : k) = 0)
    (htr : NumberField.IsTotallyReal F) (hgal : IsGalois ℚ F)
    (hirrF : (ρbar.map (algebraMap ℚ F)).IsIrreducible)
    (𝒟 : HilbertDeformationDatum ℓ F ρbar) (h𝒟 : 𝒟.IsWeaklyUniversal)
    (ht𝒟 : 𝒟.IsTraceGenerated)
    (T₀ : HilbertHeckeAlgebra ℓ F ρbar) :
    Module.Finite ℤ_[ℓ] 𝒟.R := by
  obtain ⟨T, ⟨e⟩⟩ :=
    exists_heckeAlgebra_algEquiv_of_isWeaklyUniversal ℓ hℓ5 F hlk htr hgal hirrF
      𝒟 h𝒟 ht𝒟 T₀
  exact Module.Finite.equiv e.symm.toLinearEquiv

/-! ### The assembly: integrality of the traces on a finite-index subgroup -/

/-- **The Hilbert-modular input of pillar α, assembled** (PROVEN over the
six leaves above): for a hardly ramified deformation `ρ` of an
irreducible hardly ramified `ρbar` at `ℓ ≥ 5`, there is a FINITE-INDEX
subgroup `H ≤ G_ℚ` — namely `G_F` for the totally real field `F` of
potential modularity — on which the Frobenius-free traces of `ρ` are
integral over `ℤ_ℓ`.

THE ARGUMENT, which is the literature's and is the reason the leaf of
`Deformation.lean` was shaped the way it is:

1. Potential modularity (`nonempty_potentialHeckeDatum_of_five_le`)
   supplies the totally real `F`, with `ρbar|_{G_F}` still irreducible and
   modular — the Hecke algebra `T_F`, module-finite over `ℤ_ℓ`.
2. The `F`-level universal deformation ring `R_F` exists
   (`exists_isWeaklyUniversal_hilbertDeformationDatum`); Carayol trace
   descent (`exists_isWeaklyUniversal_isTraceGenerated_hilbertDeformationDatum`)
   replaces it by one that is also TRACE-GENERATED, which is what makes
   it rigid; and it is then module-finite over `ℤ_ℓ` by `R_F = T_F`
   (`moduleFinite_hilbertDeformation_of_isWeaklyUniversal`). Step 2's
   trace-descent hop was inserted 2026-07-26: without trace generation
   the finiteness claim is FALSE — see the faithfulness audit in the
   `R_F = T_F` section above.
3. `ρ|_{G_F}` is an object of the `F`-level category
   (`isHilbertHardlyRamified_map_of_isHardlyRamified` for the local
   conditions; the residual clause is `hresid` restricted along
   `G_F ≤ G_ℚ`, which is `GaloisRep.map_apply`), so weak universality
   gives a `ℤ_ℓ`-algebra map `f : R_F → R` with
   `(ρ_F σ).charpoly.map f = (ρ (σ|_ℚ)).charpoly` for every `σ ∈ G_F`.
4. Hence every trace `(ρ g).charpoly.coeff 1`, `g ∈ G_F`, is `f` of an
   element of the module-finite `ℤ_ℓ`-algebra `R_F`, so it is integral
   over `ℤ_ℓ` (`IsIntegral.of_finite`, transported by
   `IsIntegral.map_of_comp_eq`).
5. `H = galoisSubgroup F` has finite index because `[F : ℚ] < ∞`.

Note what is NOT used: neither weak universality NOR trace generation of
the `ℚ`-level ring appears anywhere. That is correct, and is a feature of
the route — potential modularity applies to any hardly ramified
deformation, universal or not. -/
theorem exists_finiteIndex_isIntegral_charpolyCoeff_of_isHardlyRamified
    (ℓ : ℕ) [Fact ℓ.Prime] {hℓOdd : Odd ℓ} (hℓ5 : 5 ≤ ℓ)
    {k : Type u} [Field k] [Finite k] [TopologicalSpace k]
    [DiscreteTopology k] [Algebra ℤ_[ℓ] k]
    {V : Type v} [AddCommGroup V] [Module k V] [Module.Finite k V]
    [Module.Free k V]
    {hdim : Module.rank k V = 2}
    {ρbar : GaloisRep ℚ k V}
    (hbar : IsHardlyRamified hℓOdd hdim ρbar) (hirr : ρbar.IsIrreducible)
    {R : Type u} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    [IsLocalRing R] [Algebra ℤ_[ℓ] R] [IsNoetherianRing R]
    (hadic : IsAdic (IsLocalRing.maximalIdeal R))
    (hcompl : IsAdicComplete (IsLocalRing.maximalIdeal R) R)
    (ρ : FramedGaloisRep ℚ R (Fin 2))
    (hρ : IsHardlyRamified hℓOdd (rank_finTwoPi R) ρ)
    (π : R →+* k) (hπs : Function.Surjective π)
    (hresid : ∀ g : Γ ℚ, ((ρ g).charpoly).map π = (ρbar g).charpoly) :
    ∃ H : Subgroup (Γ ℚ), H.FiniteIndex ∧
      ∀ g ∈ H, IsIntegral ℤ_[ℓ] ((ρ g).charpoly.coeff 1) := by
  -- (1) potential modularity: the totally real field `F` and `T_F`
  obtain ⟨P⟩ := nonempty_potentialHeckeDatum_of_five_le ℓ hℓ5 hbar hirr
  -- (2) `ρ|_{G_F}` as an object of the `F`-level category. It is built FIRST
  -- because it is also what makes that category nonempty, which is the
  -- hypothesis `exists_isWeaklyUniversal_hilbertDeformationDatum` needs (see
  -- the faithfulness repair recorded on that leaf).
  let 𝒟' : HilbertDeformationDatum ℓ P.F ρbar :=
    { R := R
      isAdic := hadic
      isAdicComplete := hcompl
      ρ := ρ.map (algebraMap ℚ P.F)
      isHilbertHardlyRamified :=
        isHilbertHardlyRamified_map_of_isHardlyRamified ℓ (hℓOdd := hℓOdd) P.F ρ hρ
      π := π
      π_surjective := hπs
      resid := fun g => by
        rw [GaloisRep.map_apply, GaloisRep.map_apply]
        exact hresid _ }
  -- (3) the `F`-level universal deformation ring `R_F`, made trace-generated.
  -- `𝒟'` is passed as the nonemptiness witness the repaired leaf requires, and
  -- the weakly-universal datum it returns is then upgraded to a trace-generated
  -- one, which is what step (4) below needs.
  obtain ⟨𝒟₀, h𝒟₀⟩ :=
    exists_isWeaklyUniversal_hilbertDeformationDatum ℓ hℓ5 P.F P.irreducibleF 𝒟'
  obtain ⟨𝒟, h𝒟, ht𝒟⟩ :=
    exists_isWeaklyUniversal_isTraceGenerated_hilbertDeformationDatum ℓ hℓ5 P.F
      (natCast_eq_zero_of_finite_algebra ℓ k) P.irreducibleF 𝒟₀ h𝒟₀
  obtain ⟨f, hfalg, -, hfρ⟩ := h𝒟 𝒟'
  -- (4) `R_F` is module-finite over `ℤ_ℓ`, by `R_F = T_F`
  haveI : Module.Finite ℤ_[ℓ] 𝒟.R :=
    moduleFinite_hilbertDeformation_of_isWeaklyUniversal ℓ hℓ5 P.F
      (natCast_eq_zero_of_finite_algebra ℓ k) P.totallyReal P.galoisF
      P.irreducibleF 𝒟 h𝒟 ht𝒟 P.hecke
  -- (5) `H = G_F`
  refine ⟨galoisSubgroup P.F, finiteIndex_galoisSubgroup P.F, ?_⟩
  intro g hg
  obtain ⟨σ, rfl⟩ := exists_map_eq_of_mem_galoisSubgroup P.F hg
  have hcp : ((𝒟.ρ σ).charpoly).map f =
      (ρ (Field.absoluteGaloisGroup.map (algebraMap ℚ P.F) σ)).charpoly := hfρ σ
  have hcoeff :
      (ρ (Field.absoluteGaloisGroup.map (algebraMap ℚ P.F) σ)).charpoly.coeff 1
        = f ((𝒟.ρ σ).charpoly.coeff 1) := by
    rw [← hcp, Polynomial.coeff_map]
  rw [hcoeff]
  refine IsIntegral.map_of_comp_eq (RingHom.id ℤ_[ℓ]) f ?_
    (IsIntegral.of_finite ℤ_[ℓ] ((𝒟.ρ σ).charpoly.coeff 1))
  rw [RingHom.comp_id, hfalg]

end GaloisRepresentation
