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
   with NO remaining local leaf. Its determinant and unramifiedness clauses
   are PROVEN glue; BOTH of the two sharper local halves it was cut over
   are now closed (2026-07-26):

   * the tame-at-`2` half `exists_padicTwoEmbedding_of_mem` is PROVEN, and
     its last leaf `map_mem_inertia_Z2bar_of_mem_localInertiaGroup` — the
     agreement of the `IntegralClosure 𝒪_v` and `Z2bar` spellings of local
     inertia at `2` — is PROVEN too (2026-07-26), over
     `isIntegral_padicInt_of_norm_le_one` (`Z2bar` IS the integral closure
     of `ℤ_[2]`) and the transport hom `z2barMap`; and
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

   The FIRST of those clauses is PROVEN (2026-07-26), through
   `hasFlatProlongationAt_of_pi_surjection_of_numberField` — Raynaud
   closure over a VARIABLE number field, itself PROVEN 2026-07-26 by
   hoisting `Deformations/RepresentationTheory/FlatPointsGroup.lean` from
   `ℚ` to a variable number field — via the proven transfers
   `isHilbertTameAtTwo_baseChange`, `isFlatAt_baseChange_of_numberField`,
   `isHilbertHardlyRamified_conj` and
   `isHilbertHardlyRamified_baseChange`.

   `isHilbertFiniteFramesClause` (Schlessinger's H3) is no longer a leaf
   either: it was DECOMPOSED 2026-07-26 along the Hermite–Minkowski cut
   and is now PROVEN over the two bookkeeping lemmas
   `finite_setOf_framedGaloisRep_isUnramifiedAt` and
   `finite_setOf_subgroup_hilbertInertiaAt_le`, above Hermite's theorem
   for `F`, `finite_setOf_intermediateField_hilbertInertiaAt_le` — which
   is itself PROVEN (2026-07-26) over the TWO arithmetic leaves
   `discr_factorization_le_of_finrank_le` (the discriminant exponent
   from the degree, base-free) and
   `not_dvd_discr_of_hilbertInertiaTrivialAt` (the `F`-level
   inertia-to-discriminant transport).

   `isHilbertProLimitClause` is PROVEN too, and since 2026-07-26 it is
   proven OUTRIGHT — the last residual leaf
   `isHilbertTameAtTwo_of_forall_isOpen_quotient` is closed. Its
   determinant and unramifiedness clauses are `𝔪`-adic separation, its
   flatness clause is a re-indexing of the level data, and the tame
   quotient at the places over `2` — the one genuine limit statement — is
   the `ℚ`-level Mittag-Leffler argument transposed, over the pure-algebra
   machinery restated in this module (`false_of_three_quotient_chars`,
   `exists_unimodular_mem_iInf_of_isAdicComplete`, …) because
   `Deformation.lean` is DOWNSTREAM. That transposition needed one
   hypothesis the clause did not carry: `isHilbertProLimitClause` now takes
   `Odd ℓ`, which is what makes `2` a unit and gives the `±1`-rigidity of
   the level characters. Every consumer already has `5 ≤ ℓ`, so no
   signature outside that theorem and its leaf changed; see the leaf's
   docstring for the full `ℓ = 2` analysis (including why the flatness
   clause supplies no substitute rigidity there).

   The machine itself was in turn PROVEN (2026-07-26) as the ASSEMBLY of a
   three-way cut mirroring `Deformation.lean`'s: the profinite
   CONSTRUCTION `exists_universalFrame_profinite_hilbert_of_clauses`
   (LEAF), the upstream FINITENESS criterion
   `ProfiniteLocalNoetherian.isNoetherianRing_isAdic_of_profinite_of_finite_ringHom`
   (PROVEN, Mazur's `Φ_ℓ`), and the LIMIT passage
   `HilbertDeformationDatum.isWeaklyUniversal_of_finiteFrames` (PROVEN
   2026-07-26), leaving the CONSTRUCTION as the cut's only open node.
   That proof also carried a SECOND FAITHFULNESS REPAIR: the residual
   field `k` of both nodes now carries `[Finite k]`,
   `[DiscreteTopology k]` and `[Algebra ℤ_[ℓ] k]`, which the `ℚ`-level
   twin assumes throughout and which the consumer of this module already
   supplies. See the repair paragraph on the machine node.


   **SECOND FAITHFULNESS REPAIR, 2026-07-26**: `hℓ5` alone is NOT enough
   over a general `F` — `isHilbertTameAtTwo_of_fibreProduct` with `hℓ5` and
   nothing else was REFUTED at `ℓ = 5`, `F = ℚ(μ₅)` (machine-verified
   counterexample in the block comment above that theorem). The sharp
   hypothesis is `ℓ ∤ N(w)² − 1` at each `w ∣ 2`; it propagates through
   `isHilbertFibreProductClause`,
   `exists_isWeaklyUniversal_hilbertDeformationDatum`,
   `exists_heckeDatum_isWeaklyUniversal_isTraceGenerated`,
   `exists_heckeAlgebra_algEquiv_of_isWeaklyUniversal` and
   `moduleFinite_hilbertDeformation_of_isWeaklyUniversal`, and is DISCHARGED
   at the top by the new field `PotentialHeckeDatum.residueCardTwo`
   (`N(w) = 2` for every `w ∣ 2`), which is free in Taylor's argument.
   `isHilbertTameAtTwo_of_fibreProduct` is now PROVEN, over the single new
   arithmetic leaf `exists_cyclotomicCharacter_adicCompletion_eq_residueCard`
   (`χ_ℓ(Frob_w) = N(w)`) and the linear-algebra brick
   `exists_unit_smul_of_vecMul_eq_row`.
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
   A THIRD repair, 2026-07-26, PINS THE TOPOLOGY: `isAdic` and
   `isAdicComplete` are now fields, because `IsHilbertHardlyRamified` is a
   continuity condition and the deformation category demands the
   maximal-adic topology. See the INTERFACE REPAIR section of its docstring.
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
   and the two arithmetic strata of the Carayol package.  BOTH are now
   PROVEN, by two owners working concurrently:
   `exists_isLocalRing_hilbertTraceSubring` (Lemme 1 — the trace subring is
   again a coefficient ring; the content is NOETHERIANITY) as soft glue over
   the single arithmetic leaf `fg_comap_maximalIdeal_hilbertTraceSubring`,
   and `exists_framedGaloisRep_hilbertTraceSubring` (Théorème 1 — the
   conjugation of `𝒟.ρ` into `GL₂(R')`) over a three-way cut mirroring the
   `ℚ` level, leaving open the Rouquier–Nyssen descent
   `exists_framedGaloisRep_baseChange_hilbertTraceSubring`.
   The tame-at-`2` descent
   `isHilbertTameAtTwo_of_baseChange_hilbertTraceSubring` was REFUTED as
   originally cut and PROVEN 2026-07-26 in repaired form: it is FALSE
   without a ring retraction of the trace-subring inclusion (explicit
   witness over `F = ℚ(ζ₇)⁺` at `ℓ = 7` in its FALSITY AUDIT), and with one
   it is formal. The retraction is the new leaf
   `exists_ringHom_retraction_hilbertTraceSubring`, discharged from
   `IsWeaklyUniversal` and hence invisible outside the Carayol section.
   On the flat side the Raynaud sub-object closure
   `hasFlatProlongationAt_of_injection_of_numberField` was PROVEN
   2026-07-26 once `FlatPointsGroup.lean`'s base-field hoist landed, so
   nothing on that side is open. The `ℚ` level's THIRD leaf of the outer
   cut, the
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
-- `maximalIdeal_map_eq_of_le_fixedField_localInertiaGroup` (Neukirch II.9.11,
-- the LOCAL half of the embedding-prime transport), consumed by
-- `exists_prime_over_inertia_eq_bot_of_hilbertInertiaTrivialAt` below.  The
-- module is already in this one's transitive cone, but only through a NON-
-- public import, so the name is not in scope without this line (Lean's
-- module system does not re-export a bare `import`).
public import Fermat.FLT.Deformations.RepresentationTheory.LocalInertiaFixedField
public import Mathlib.Topology.Algebra.Ring.Ideal
public import Mathlib.Topology.Compactness.Compact
-- the convolution-monoid bookkeeping of the flat-prolongation package
-- (`liftEquiv_convOne`/`liftEquiv_convMul`/`liftEquiv_comp`,
-- `vendored_one_eq_convOne`, `vendored_mul_eq_convMul`), reused by the
-- base-change points comparison `extPointsEquiv` below
public import Fermat.FLT.Deformations.RepresentationTheory.FlatProlongation
public import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
-- `NumberField.discr`, `NumberField.discr_ne_zero` and Hermite's theorem
-- `NumberField.finite_of_discr_bdd`, consumed by the Hermite–Minkowski cut
-- `finite_setOf_intermediateField_hilbertInertiaAt_le` below (and by the two
-- arithmetic leaves it rests on, whose STATEMENTS mention `discr` — hence
-- `public`)
public import Mathlib.NumberTheory.NumberField.Discriminant.Basic
public import Mathlib.NumberTheory.NumberField.Discriminant.Different
-- `differentIdeal_exponent_le` (the Serre bound `d_Q ≤ e − 1 + e·v_q(e)`) and,
-- re-exported through it, `ModThree.lean`'s tame-plus-wild assembly
-- `IsHardlyRamified.discr_factorization_le_of_forall_differentIdeal_pow_dvd`.
-- Together these PROVE `discr_factorization_le_of_finrank_le` below, which was
-- a leaf until 2026-07-26; both are stated over an abstract
-- `(K : Type*) [Field K] [NumberField K]`, so the base-free statement needs no
-- generalization work, only the import.
--
-- CIRCULARITY GUARD (verified 2026-07-26 by import-closure computation, not by
-- inspection): `HermiteMinkowski.lean`'s 118-module project closure does NOT
-- contain this module, so the import is acyclic. Its own guard already
-- establishes that its closure avoids `Deformation.lean`, `Lift.lean`,
-- `Family.lean` and `Modularity/*`, i.e. it cannot close the forbidden
-- Khare–Wintenberger cycle.
--
-- CONE-GROWTH AUDIT (same date, and it is why the previous ROUTE AUDIT's
-- objection does not apply): this module has exactly TWO project consumers,
-- `Deformation.lean` and `Modularity/Patching.lean`, and BOTH already import
-- `HermiteMinkowski.lean` directly. So this import adds ZERO modules to any
-- downstream consumer's cone; it only makes THIS module rebuild when the
-- Hermite–Minkowski cluster moves.
public import Fermat.FLT.GaloisRepresentation.HardlyRamified.HermiteMinkowski
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
public import Mathlib.NumberTheory.Padics.RingHoms
public import Fermat.FLT.GaloisRepresentation.HardlyRamified.LevelLimit
-- the limit passage `HilbertDeformationDatum.isWeaklyUniversal_of_finiteFrames`:
-- Kőnig's lemma (`nonempty_sections_of_finite_inverse_system`), the transition
-- maps `R ⧸ Iᵐ →+* R ⧸ Iⁿ` (`Ideal.Quotient.factorPow`), and the universal
-- property of adic completeness for ring maps (`IsAdicComplete.liftRingHom`).
public import Mathlib.CategoryTheory.CofilteredSystem
public import Mathlib.RingTheory.Ideal.Quotient.PowTransition
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import Mathlib.RingTheory.AdicCompletion.RingHom
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
-- `Modularity.PatchedModule` and `Modularity.PatchedModule.injective`: the
-- BASE-FIELD-INDEPENDENT core of Taylor–Wiles patching. This is what
-- `injective_classifyingMap_hilbertHeckeDatum` below is assembled over, and
-- the reason it is a HOISTED module rather than a local copy is recorded in
-- that module's header: the material lived in `Modularity/Patching.lean`,
-- which is DOWNSTREAM of this file (it imports `HardlyRamified/Deformation.lean`,
-- which `public import`s this module), so the `ℚ`-level file cannot be imported
-- here and duplicating 990 lines of commutative algebra was the alternative.
public import Fermat.FLT.Modularity.PatchingCore
-- `Nat.ModEq` (the `≡ … [MOD …]` notation) and `Ideal.Quotient`, for the
-- Taylor–Wiles congruence `N w ≡ 1 mod ℓ ^ n` on places of `F` in
-- `IsHilbertTaylorWilesPrimeSet` below.
public import Mathlib.Data.Nat.ModEq
public import Mathlib.RingTheory.Ideal.Quotient.Operations
-- proof-only: `ProfiniteLocal.compactSpace_of_isAdic_of_finite_quotient`, which
-- makes the coefficient ring of a `HilbertDeformationDatum` PROFINITE and hence
-- its closed trace subring compact — the hypothesis of
-- `ProfiniteLocalNoetherian.isAdic_isAdicComplete_of_isOpen_of_fg` in
-- `exists_isLocalRing_hilbertTraceSubring` below. `ProfiniteLocal.lean` imports
-- only mathlib, so it is well outside the circularity guard.
import Fermat.FLT.GaloisRepresentation.HardlyRamified.ProfiniteLocal
-- `CompleteLocalNoetherian.isNoetherianRing_of_isAdicComplete_of_fg` (Stacks
-- 05GH), the "complete + `𝔪` finitely generated ⟹ Noetherian" step of
-- `exists_isLocalRing_hilbertTraceSubring`. `ProfiniteLocalNoetherian.lean`
-- reaches that module only through a PRIVATE `import`, which is not
-- re-exported, so a `public import` here is Lean's own remedy.
public import Fermat.FLT.GaloisRepresentation.HardlyRamified.CompleteLocalNoetherian
-- proof-only: the representation-free Raynaud-closure carrier
-- `GaloisRepresentation.Modularity.IsFlatPointsGroupAt` with its product and
-- quotient halves (`.pi`, `.of_surjective`) and the repackaging
-- `GaloisRep.hasFlatProlongationAt_iff_isFlatPointsGroupAt`, which together
-- discharge `hasFlatProlongationAt_of_pi_surjection_of_numberField` below.
--
-- CIRCULARITY GUARD: this is SAFE and costs the guard nothing.
-- `FlatPointsGroup.lean` sits in `Deformations/RepresentationTheory/` and its
-- `Fermat`-side import closure (38 modules, through
-- `FlatProlongation.lean` and `KnownIn1980s/EllipticCurves/Flat.lean`)
-- contains NOTHING from `HardlyRamified/`, `Family.lean`, `Lift.lean`,
-- `Deformation.lean` or `Modularity/*` — so no cycle is created. And the sole
-- consumer of this module, `Deformation.lean`, ALREADY imports
-- `FlatPointsGroup.lean` itself (for the `K = ℚ` instance
-- `hasFlatProlongationAt_of_pi_surjection`), so this line adds not one module
-- to any DOWNSTREAM import cone; the only cost is this module's own
-- elaboration.
import Fermat.FLT.Deformations.RepresentationTheory.FlatPointsGroup

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

The route mapped out by this leaf's previous owner is now EXECUTED IN FULL,
including the one identification that owner flagged as "genuinely missing";
nothing in this subsection is open. Four things happen below:

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
4. `map_mem_inertia_Z2bar_of_mem_localInertiaGroup` (PROVEN) — the two
   spellings of local inertia at `2` agree across that identification, over
   `isIntegral_padicInt_of_norm_le_one` / `isIntegral_padicInt_of_mem_Z2bar`
   (`Z2bar` IS the integral closure of `ℤ_[2]`), `padicIntMap`,
   `isIntegral_map_of_mem_Z2bar` and the transport hom `z2barMap`.

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

/-- **`Z2bar` is the integral closure of `ℤ_[2]` in `ℚ_[2]ᵃˡᵍ`, elementwise**
(PROVEN), stated at a general prime: an element of the algebraic closure of
`ℚ_[p]` of norm `≤ 1` is integral over `ℤ_[p]`.

THIS IS THE STEP THAT DEFEATED THE PREVIOUS OWNER OF
`map_mem_inertia_Z2bar_of_mem_localInertiaGroup`, and the escape is worth
recording because it is *neither* of the two escapes that owner mapped out.

`AbsoluteGaloisGroup.lean`'s `isIntegral_of_spectralNorm_le_one` is stated
under `attribute [local instance] Valued.toNormedField`, so at `K := ℚ_[2]`
its `spectralNorm` is taken with respect to a `NormedField ℚ_[2]` different
from `Padic.instNormedField` (the one `Z2bar` and `PadicAlgCl` use). The two
are propositionally but not definitionally equal and unification between
them DIVERGES — a `whnf` timeout that survives `maxHeartbeats 2000000`,
i.e. a defeq problem, not a resource problem.

The escape is not to repair that lemma's instance mismatch but to bypass
the lemma: its mathematical content at a base field that already IS a
`NormedField` is just mathlib's `spectralValue_le_one_iff`, which lives in a
plain `[NormedDivisionRing R]` section and therefore never mentions
`Valued` at all. Unfolded:

* `‖z‖ = spectralNorm ℚ_[p] (ℚ_[p]ᵃˡᵍ) z = spectralValue (minpoly ℚ_[p] z)`
  by `rfl` (`PadicAlgCl.normedField` IS `spectralNorm.normedField`), so
  `hz` is *literally* the hypothesis of `spectralValue_le_one_iff`;
* that lemma turns `‖z‖ ≤ 1` into "every coefficient of `minpoly ℚ_[p] z`
  has norm `≤ 1`", i.e. lies in `ℤ_[p]` — which is by definition the
  subtype of `ℚ_[p]` cut out by `‖·‖ ≤ 1`, so the range condition of
  `Polynomial.lifts_iff_coeff_lifts` is discharged by `⟨⟨_, h⟩, rfl⟩`;
* `Polynomial.lifts_and_degree_eq_and_monic` produces the monic
  `P : ℤ_[p][X]` witnessing integrality.

No `Valued ℚ_[p] ℝ≥0` instance, no `RankOne`, no heartbeat bump: the whole
lemma elaborates in seconds. -/
theorem isIntegral_padicInt_of_norm_le_one {p : ℕ} [Fact p.Prime]
    {z : ℚ_[p]ᵃˡᵍ} (hz : ‖z‖ ≤ 1) : IsIntegral ℤ_[p] z := by
  have halg : IsIntegral ℚ_[p] z := Algebra.IsIntegral.isIntegral z
  have hmonic : (minpoly ℚ_[p] z).Monic := minpoly.monic halg
  have hsv : spectralValue (minpoly ℚ_[p] z) ≤ 1 := hz
  have hcoeff := (spectralValue_le_one_iff hmonic).mp hsv
  have hlift : minpoly ℚ_[p] z ∈ Polynomial.lifts (algebraMap ℤ_[p] ℚ_[p]) := by
    refine (Polynomial.lifts_iff_coeff_lifts _).mpr fun i => ?_
    exact ⟨⟨(minpoly ℚ_[p] z).coeff i, hcoeff i⟩, rfl⟩
  obtain ⟨P, hP, _, hPmonic⟩ := Polynomial.lifts_and_degree_eq_and_monic hlift hmonic
  refine ⟨P, hPmonic, ?_⟩
  rw [← Polynomial.aeval_def, ← Polynomial.aeval_map_algebraMap ℚ_[p], hP, minpoly.aeval]

/-- **Every element of `Z2bar` is integral over `ℤ_[2]`** (PROVEN):
membership in `Z2bar = Valued.v.valuationSubring` is `Valued.v z ≤ 1`, which
for `PadicAlgCl 2` is `‖z‖₊ ≤ 1` by `rfl`. -/
theorem isIntegral_padicInt_of_mem_Z2bar (z : Z2bar) : IsIntegral ℤ_[2] (z : ℚ_[2]ᵃˡᵍ) := by
  apply isIntegral_padicInt_of_norm_le_one
  have hz := z.2
  rw [Valuation.mem_valuationSubring_iff] at hz
  exact_mod_cast hz

/-- **`e` restricted to the rings of integers**, `ℤ_[2] →+* 𝒪_v` (PROVEN):
this is exactly what the hypothesis `he` of
`map_mem_inertia_Z2bar_of_mem_localInertiaGroup` says, packaged as a ring
hom. The analogue of `CompletionTransport.lean`'s `intMap`. -/
noncomputable def padicIntMap (v : HeightOneSpectrum (𝓞 ℚ)) (e : ℚ_[2] ≃+* v.adicCompletion ℚ)
    (he : ∀ x : ℤ_[2], e (x : ℚ_[2]) ∈ v.adicCompletionIntegers ℚ) :
    ℤ_[2] →+* ↥(v.adicCompletionIntegers ℚ) :=
  (e.toRingHom.comp (algebraMap ℤ_[2] ℚ_[2])).codRestrict
    (v.adicCompletionIntegers ℚ).toSubring he

/-- **The image of `Z2bar` under `AlgebraicClosure.map e` is integral over
`𝒪_v`** (PROVEN): an element of `Z2bar` is integral over `ℤ_[2]`, `e` carries
`ℤ_[2]` into `𝒪_v`, and `IsIntegral.map_of_comp_eq` transports integrality
along the square. The analogue of `CompletionTransport.lean`'s
`isIntegral_algebraicClosureMap`, with `Z2bar` in the source slot. -/
theorem isIntegral_map_of_mem_Z2bar (v : HeightOneSpectrum (𝓞 ℚ))
    (e : ℚ_[2] ≃+* v.adicCompletion ℚ)
    (he : ∀ x : ℤ_[2], e (x : ℚ_[2]) ∈ v.adicCompletionIntegers ℚ) (z : Z2bar) :
    IsIntegral ↥(v.adicCompletionIntegers ℚ)
      (AlgebraicClosure.map e.toRingHom (z : ℚ_[2]ᵃˡᵍ)) := by
  refine IsIntegral.map_of_comp_eq (padicIntMap v e he) (AlgebraicClosure.map e.toRingHom) ?_
    (isIntegral_padicInt_of_mem_Z2bar z)
  ext y
  show algebraMap ↥(v.adicCompletionIntegers ℚ) ((v.adicCompletion ℚ)ᵃˡᵍ) (padicIntMap v e he y)
      = AlgebraicClosure.map e.toRingHom (algebraMap ℤ_[2] (ℚ_[2]ᵃˡᵍ) y)
  rw [IsScalarTower.algebraMap_apply ℤ_[2] ℚ_[2] (ℚ_[2]ᵃˡᵍ), AlgebraicClosure.map_algebraMap,
    IsScalarTower.algebraMap_apply ↥(v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ)
      ((v.adicCompletion ℚ)ᵃˡᵍ)]
  rfl

/-- **`AlgebraicClosure.map e` as a ring hom of integer rings**
`Z2bar →+* IntegralClosure 𝒪_v ((v.adicCompletion ℚ)ᵃˡᵍ)` (PROVEN). The
analogue of `CompletionTransport.lean`'s `icMap`, with `Z2bar` in the source
slot instead of an `IntegralClosure`. -/
noncomputable def z2barMap (v : HeightOneSpectrum (𝓞 ℚ)) (e : ℚ_[2] ≃+* v.adicCompletion ℚ)
    (he : ∀ x : ℤ_[2], e (x : ℚ_[2]) ∈ v.adicCompletionIntegers ℚ) :
    Z2bar →+* IntegralClosure ↥(v.adicCompletionIntegers ℚ) ((v.adicCompletion ℚ)ᵃˡᵍ) where
  toFun z := ⟨AlgebraicClosure.map e.toRingHom (z : ℚ_[2]ᵃˡᵍ), isIntegral_map_of_mem_Z2bar v e he z⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' _ _ := Subtype.ext (map_mul _ _ _)
  map_zero' := Subtype.ext (map_zero _)
  map_add' _ _ := Subtype.ext (map_add _ _ _)

/-- **The two spellings of local inertia at `2` agree** (PROVEN, 2026-07-26 —
this was the identification that the previous owner of
`exists_padicTwoEmbedding_of_mem` flagged as "WHAT IS GENUINELY MISSING",
and it was the last open piece of that route).

`localInertiaGroup v` (`AbsoluteGaloisGroup.lean`) is the inertia of
`IsLocalRing.maximalIdeal (IntegralClosure 𝒪_v ((v.adicCompletion ℚ)ᵃˡᵍ))`,
while `IsHardlyRamified.isTameAtTwo` (`Defs.lean`) uses the inertia of
`IsLocalRing.maximalIdeal Z2bar` with
`Z2bar = Valued.v.valuationSubring (ℚ_[2]ᵃˡᵍ)`. The claim is that the
topological isomorphism `e : ℚ_[2] ≅ ℚ_v` of the previous lemma carries the
one to the other.

THE ROUTE, now EXECUTED — it is the template of
`CompletionTransport.lean`'s `icMap` / `map_mem_localInertiaGroup`, run
with `Z2bar` in the source slot instead of an `IntegralClosure`:

* `Z2bar` IS the integral closure of `ℤ_[2]` in `ℚ_[2]ᵃˡᵍ`
  (`isIntegral_padicInt_of_mem_Z2bar`, above); the previous owner's
  measured obstruction on that step — `isIntegral_of_spectralNorm_le_one`
  diverging at `K := ℚ_[2]` on two non-defeq `NormedField ℚ_[2]` instances —
  is recorded in that lemma's docstring together with the escape actually
  taken, which is to use mathlib's `spectralValue_le_one_iff` (a
  `NormedDivisionRing`-only lemma that never mentions `Valued`) instead of
  repairing the instance mismatch;
* `he` says `e` carries `ℤ_[2]` into `𝒪_v`, so
  `IsIntegral.map_of_comp_eq` along `AlgebraicClosure.map e` turns that
  into `IsIntegral 𝒪_v (AlgebraicClosure.map e z)`
  (`isIntegral_map_of_mem_Z2bar`), i.e. gives the ring hom
  `z2barMap : Z2bar →+* IntegralClosure 𝒪_v ((v.adicCompletion ℚ)ᵃˡᵍ)`,
  exactly as `isIntegral_algebraicClosureMap` / `icMap` do downstream of a
  map of completions;
* `Field.absoluteGaloisGroup.lift_map` makes that hom equivariant for
  `Field.absoluteGaloisGroup.map e` upstairs and `κ` downstairs, so `hκ`
  applies to the image;
* the reflection of `mem_maximalIdeal_of_icMap` — a ring hom of LOCAL rings
  sends units to units, so a preimage of a non-unit is a non-unit — brings
  the conclusion back to `IsLocalRing.maximalIdeal Z2bar`.

FAITHFULNESS: the conclusion is an inertia-only containment about a VALUE
(`e`, pinned by `he` and the two continuity clauses), never an existence of
a coordinate and never a `Γ`-wide rationality claim, so it is on the true
side of this development's `𝒪ᵥ` descent rule. `_hcont` / `_hcont'` are
underscored because the executed route does not consume them: only the
INCLUSION `e (ℤ_[2]) ⊆ 𝒪_v` is needed, never the reverse inclusion (which
IS where continuity would be required — it forces `v ∣ 2`, since `2^n → 0`
in `ℚ_[2]` must go to `0` in `ℚ_v`). They are kept because without SOME
pinning of `e` beyond `he` the statement would quantify over arbitrary
abstract embeddings, and the automatic continuity that would justify that is
itself a theorem nobody here has. -/
theorem map_mem_inertia_Z2bar_of_mem_localInertiaGroup
    (v : HeightOneSpectrum (𝓞 ℚ)) (e : ℚ_[2] ≃+* v.adicCompletion ℚ)
    (he : ∀ x : ℤ_[2], e (x : ℚ_[2]) ∈ v.adicCompletionIntegers ℚ)
    (_hcont : Continuous e) (_hcont' : Continuous e.symm)
    {κ : Γ (v.adicCompletion ℚ)} (hκ : κ ∈ localInertiaGroup v) :
    Field.absoluteGaloisGroup.map e.toRingHom κ ∈
      AddSubgroup.inertia
        ((IsLocalRing.maximalIdeal Z2bar).toAddSubgroup : AddSubgroup Z2bar) (Γ ℚ_[2]) := by
  intro z
  have hkey : z2barMap v e he (Field.absoluteGaloisGroup.map e.toRingHom κ • z - z)
      ∈ IsLocalRing.maximalIdeal
        (IntegralClosure ↥(v.adicCompletionIntegers ℚ) ((v.adicCompletion ℚ)ᵃˡᵍ)) := by
    have h1 : z2barMap v e he (Field.absoluteGaloisGroup.map e.toRingHom κ • z - z)
        = κ • z2barMap v e he z - z2barMap v e he z := by
      rw [map_sub]
      congr 1
      apply Subtype.ext
      exact Field.absoluteGaloisGroup.lift_map e.toRingHom κ (z : ℚ_[2]ᵃˡᵍ)
    rw [h1]
    exact hκ (z2barMap v e he z)
  rw [IsLocalRing.mem_maximalIdeal] at hkey
  show Field.absoluteGaloisGroup.map e.toRingHom κ • z - z ∈ IsLocalRing.maximalIdeal Z2bar
  rw [IsLocalRing.mem_maximalIdeal]
  exact fun hu => hkey (hu.map (z2barMap v e he))

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
on the clause definitions below.

NOTE (2026-07-26): only the TAME residue is still stated here.
`isHilbertFlatAt_of_fibreProduct` was PROVEN and moved down to just above
`isHilbertFibreProductClause`, because its proof consumes
`hasFlatProlongationAt_of_pi_surjection_of_numberField`, which is declared
below this point; see the section note there. -/

/-- **Two unimodular left eigenvectors of a `2 × 2` matrix over a local ring
are proportional as soon as `det m − d d'` is a unit** (PROVEN; pure
commutative algebra, the uniqueness engine of
`isHilbertTameAtTwo_of_fibreProduct` below).

This is a VERBATIM re-proof of `Deformation.lean`'s
`exists_unit_smul_of_vecMul_eq`, under a different name. The duplication is
forced by this module's CIRCULARITY GUARD: `Deformation.lean` imports this
file, so nothing there is reachable from here, and a same-named declaration
in the shared `GaloisRepresentation` namespace would collide at that
import. Do NOT "deduplicate" by importing `Deformation.lean`.

`r` and `r'` are rows with `r m = d r` and `r' m = d' r'`, each UNIMODULAR
(`hx`, `hx'`: some `A`-combination of the entries is `1`, i.e. each is the
coordinate vector of a SURJECTIVE functional). The `2 × 2` identity

  `(r₀ r'₁ − r₁ r'₀) · (det m − d d') = 0`

— a `linear_combination` of the four eigen-equations — says that if the two
rows were independent then `m` would be diagonalised by them and `det m`
would be `d d'`. With `det m − d d'` a unit the cross determinant vanishes,
and over a LOCAL ring unimodularity makes one entry of `r` invertible,
which turns the vanishing into `r' = u · r` with `u` a unit. -/
theorem exists_unit_smul_of_vecMul_eq_row {A : Type*} [CommRing A]
    [IsLocalRing A]
    (m : Matrix (Fin 2) (Fin 2) A) (r r' : Fin 2 → A) (d d' : A)
    (hr : ∀ j, ∑ i, r i * m i j = d * r j)
    (hr' : ∀ j, ∑ i, r' i * m i j = d' * r' j)
    (hx : ∃ x : Fin 2 → A, ∑ i, r i * x i = 1)
    (hx' : ∃ x : Fin 2 → A, ∑ i, r' i * x i = 1)
    (hunit : IsUnit (m.det - d * d')) :
    ∃ u : A, IsUnit u ∧ ∀ i, r' i = u * r i := by
  obtain ⟨x, hx⟩ := hx
  obtain ⟨x', hx'⟩ := hx'
  have e00 := hr 0
  have e01 := hr 1
  have e10 := hr' 0
  have e11 := hr' 1
  rw [Fin.sum_univ_two] at e00 e01 e10 e11 hx hx'
  rw [Matrix.det_fin_two] at hunit
  have hcross : (r 0 * r' 1 - r 1 * r' 0) *
      (m 0 0 * m 1 1 - m 0 1 * m 1 0 - d * d') = 0 := by
    linear_combination (r' 0 * m 0 1 + r' 1 * m 1 1) * e00 -
      (r' 0 * m 0 0 + r' 1 * m 1 0) * e01 - (d * r 1) * e10 + (d * r 0) * e11
  have hzero : r 0 * r' 1 - r 1 * r' 0 = 0 := by
    obtain ⟨v, hv⟩ := hunit
    have h1 : (r 0 * r' 1 - r 1 * r' 0) * ((v : A) * ((v⁻¹ : Aˣ) : A)) = 0 := by
      rw [hv, ← mul_assoc, hcross, zero_mul]
    simpa using h1
  have hcases : IsUnit (r 0) ∨ IsUnit (r 1) := by
    have h1 : IsUnit (r 0 * x 0 + r 1 * x 1) := by rw [hx]; exact isUnit_one
    exact (IsLocalRing.isUnit_or_isUnit_of_isUnit_add h1).imp
      isUnit_of_mul_isUnit_left isUnit_of_mul_isUnit_left
  rcases hcases with h | h
  · obtain ⟨s, hs⟩ := h.exists_right_inv
    have key0 : r' 0 = r' 0 * s * r 0 := by linear_combination (-(r' 0)) * hs
    have key1 : r' 1 = r' 0 * s * r 1 := by
      linear_combination (-(r' 1)) * hs + s * hzero
    have key : ∀ i, r' i = r' 0 * s * r i := by
      intro i; fin_cases i
      · exact key0
      · exact key1
    refine ⟨r' 0 * s, IsUnit.of_mul_eq_one (r 0 * x' 0 + r 1 * x' 1) ?_, key⟩
    rw [show r' 0 * s * (r 0 * x' 0 + r 1 * x' 1) =
      r' 0 * s * r 0 * x' 0 + r' 0 * s * r 1 * x' 1 by ring, ← key0, ← key1]
    exact hx'
  · obtain ⟨s, hs⟩ := h.exists_right_inv
    have key1 : r' 1 = r' 1 * s * r 1 := by linear_combination (-(r' 1)) * hs
    have key0 : r' 0 = r' 1 * s * r 0 := by
      linear_combination (-(r' 0)) * hs - s * hzero
    have key : ∀ i, r' i = r' 1 * s * r i := by
      intro i; fin_cases i
      · exact key0
      · exact key1
    refine ⟨r' 1 * s, IsUnit.of_mul_eq_one (r 0 * x' 0 + r 1 * x' 1) ?_, key⟩
    rw [show r' 1 * s * (r 0 * x' 0 + r 1 * x' 1) =
      r' 1 * s * r 0 * x' 0 + r' 1 * s * r 1 * x' 1 by ring, ← key0, ← key1]
    exact hx'

/-- **The arithmetic Frobenius at `w`, read in `Γ ℚ`, raises every
`ℓⁿ`-th root of unity to its `N(w)`-th power** (PROVEN 2026-07-26; the
roots-of-unity input of
`exists_cyclotomicCharacter_adicCompletion_eq_residueCard` below).

Let `w ∤ ℓ` be a place of the number field `F`. Push the arithmetic
Frobenius `Frob_w ∈ Γ F_w` down the tower `Γ F_w → Γ F → Γ ℚ` and let it
act on `μ_{ℓⁿ} ⊆ ℚᵃˡᵍ`: the result is `t ↦ t^{N(w)}`, with the exponent
read mod `ℓⁿ` because `t^{ℓⁿ} = 1`.

The mathematics is mathlib's `AlgHom.IsArithFrobAt.apply_of_pow_eq_one`
applied to `Field.AbsoluteGaloisGroup.isArithFrobAt_adicArithFrob`: an
`ℓⁿ`-th root of unity is integral over `𝒪_{F_w}` and `ℓⁿ` avoids the
maximal ideal upstairs precisely because `w ∤ ℓ` (`hwℓ`), so the
Frobenius specification applies and raises it to the power
`#(𝒪_{F_w}/𝔪) = N(w)`
(`IsDedekindDomain.HeightOneSpectrum.natCard_under_maximalIdeal`). The
descent down the two steps of the tower is `Field.absoluteGaloisGroup.lift_map`
against injectivity of `AlgebraicClosure.map`, one step at a time — no
`map_comp` for `Field.absoluteGaloisGroup.map` exists, since `map` depends
on an arbitrarily chosen embedding of algebraic closures, and descending
stepwise avoids needing one.

PROVENANCE: this is a verbatim port of the PROVEN
`GaloisRepresentation.Modularity.adicArithFrob_rootsOfUnity_pow_base` of
`Modularity/KhareWintenberger.lean`. That module is DOWNSTREAM of this one
(it imports `HardlyRamified/Deformation.lean`, which `public import`s this
file), so the lemma cannot be imported here and the proof is duplicated
deliberately; the name is deliberately DIFFERENT from the downstream one so
that the two never shadow each other. If the two are ever unified, the
right move is to hoist this one into `GaloisRepTransport.lean` — every
ingredient it uses is already in that module's cone. -/
theorem adicArithFrob_rootsOfUnity_pow_residueCard
    {ℓ : ℕ} [hℓ : Fact ℓ.Prime] (F : Type u) [Field F] [NumberField F]
    (w : HeightOneSpectrum (𝓞 F))
    (hwℓ : ((ℓ : ℕ) : 𝓞 F) ∉ w.asIdeal) (n : ℕ) :
    ∀ t ∈ rootsOfUnity (ℓ ^ n) (ℚ ᵃˡᵍ),
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
  have htL : ((t : (ℚ ᵃˡᵍ)ˣ) : ℚ ᵃˡᵍ) ^ (ℓ ^ n) = 1 := by
    have h1 := (mem_rootsOfUnity _ _).mp ht
    calc ((t : (ℚ ᵃˡᵍ)ˣ) : ℚ ᵃˡᵍ) ^ (ℓ ^ n)
        = ((t ^ (ℓ ^ n) : (ℚ ᵃˡᵍ)ˣ) : ℚ ᵃˡᵍ) := by push_cast; rfl
      _ = 1 := by rw [h1]; rfl
  set u : AlgebraicClosure F :=
    AlgebraicClosure.map g ((t : (ℚ ᵃˡᵍ)ˣ) : ℚ ᵃˡᵍ) with hudef
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
          (HeightOneSpectrum.completionIdeal F w).under (𝓞 F) := Ideal.LiesOver.over
      rw [hover, Ideal.under_def, Ideal.mem_comap]
      show algebraMap (𝓞 F) (w.adicCompletionIntegers F) ((ℓ : ℕ) : 𝓞 F) ∈ _
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
      ((t : (ℚ ᵃˡᵍ)ˣ) : ℚ ᵃˡᵍ) =
      ((t : (ℚ ᵃˡᵍ)ˣ) : ℚ ᵃˡᵍ) ^ Ideal.absNorm w.asIdeal := by
    apply (AlgebraicClosure.map g).injective
    rw [Field.absoluteGaloisGroup.lift_map g
      (Field.absoluteGaloisGroup.map h (Field.AbsoluteGaloisGroup.adicArithFrob w))
      ((t : (ℚ ᵃˡᵍ)ˣ) : ℚ ᵃˡᵍ), map_pow]
    exact hstepF
  show (Field.absoluteGaloisGroup.map g
      (Field.absoluteGaloisGroup.map h (Field.AbsoluteGaloisGroup.adicArithFrob w)))
      ((t : (ℚ ᵃˡᵍ)ˣ) : ℚ ᵃˡᵍ) = _
  rw [hmain]
  -- the exponent-mod juggle: `t^Nw = t^(Nw mod ℓⁿ)` since `t^{ℓⁿ} = 1`
  haveI : NeZero (ℓ ^ n) := ⟨pow_ne_zero _ hℓ.out.pos.ne'⟩
  have hval : ((Ideal.absNorm w.asIdeal : ZMod (ℓ ^ n))).val =
      Ideal.absNorm w.asIdeal % ℓ ^ n := ZMod.val_natCast _ _
  conv_lhs => rw [show Ideal.absNorm w.asIdeal =
    ℓ ^ n * (Ideal.absNorm w.asIdeal / ℓ ^ n) + Ideal.absNorm w.asIdeal % ℓ ^ n from
    (Nat.div_add_mod _ (ℓ ^ n)).symm]
  rw [pow_add, pow_mul, htL, one_pow, one_mul, hval]

/-- **A Frobenius at `w` inside `Γ F_w`, with cyclotomic value `N(w)`**
(PROVEN 2026-07-26; the `F`-level twin of `Deformation.lean`'s PROVEN
`exists_cyclotomicCharacter_padicTwo_eq_two`, and the ARITHMETIC input of
the gluing argument below).

For `w ∤ ℓ` the tower `F_w(μ_{ℓⁿ})/F_w` is UNRAMIFIED and its Frobenius
acts on `ℓⁿ`-th roots of unity by `ζ ↦ ζ^{N(w)}`, where
`N(w) = #(𝒪_F/w)`. So the `ℓ`-adic cyclotomic character of `Γ ℚ` — which
is what `IsHilbertHardlyRamified.det` pins the determinant to, read through
`Γ F_w → Γ F → Γ ℚ` — takes the value `N(w)` on the image of a Frobenius
at `w`. `hw` is load-bearing exactly as `hodd` is over `ℚ`: at `w ∣ ℓ` the
character is ramified and the statement is false, since `N(w)` is then a
power of `ℓ` and hence not a unit of `ℤ_ℓ`.

Over `ℚ` at `w = (2)` this is `χ_ℓ(Frob_2) = 2`, which is the `ℚ`-level
leaf; the route taken there — `Chebotarev.lean`'s
`cyclotomicCharacter_globalFrob` plus a transport from the adic completion
to mathlib's `Padic` — is not available here, because `Chebotarev.lean`
lies outside this module's deliberately minimal import surface and states
its Frobenius over `ℚ` only. What is needed here is the same statement for
a general number field: the unramifiedness of `F_w(μ_{ℓⁿ})/F_w` and the
value of the arithmetic Frobenius on roots of unity.

DISCHARGE (2026-07-26). The witness is `Field.AbsoluteGaloisGroup.adicArithFrob w`
itself, and the value computation is the immediately preceding
`adicArithFrob_rootsOfUnity_pow_residueCard` — which does supply exactly the
general-number-field statement asked for above — fed to
`modularCyclotomicCharacter.unique` level by level and reassembled with
`PadicInt.ext_of_toZModPow`. The residue cardinality is converted between
its two shapes by `Ideal.absNorm_apply` / `Submodule.cardQuot_apply`:
`Ideal.absNorm w.asIdeal = Nat.card (𝓞 F ⧸ w)`.

`#print axioms` on the completed proof returns
`[propext, Classical.choice, Quot.sound]`.

References: Neukirch, *Algebraic Number Theory*, Ch. II §7 and Ch. V;
Serre, *Abelian ℓ-adic representations*, Ch. I §1.2. -/
theorem exists_cyclotomicCharacter_adicCompletion_eq_residueCard (ℓ : ℕ)
    [Fact ℓ.Prime] (F : Type u) [Field F] [NumberField F]
    (w : HeightOneSpectrum (𝓞 F)) (hw : ((ℓ : ℕ) : 𝓞 F) ∉ w.asIdeal) :
    ∃ g : Γ (w.adicCompletion F),
      ((cyclotomicCharacter (ℚ ᵃˡᵍ) ℓ
          (Field.absoluteGaloisGroup.map (algebraMap ℚ F)
            (Field.absoluteGaloisGroup.map
              (algebraMap F (w.adicCompletion F)) g)).toRingEquiv : ℤ_[ℓ]ˣ) :
        ℤ_[ℓ]) = ((Nat.card (𝓞 F ⧸ w.asIdeal) : ℕ) : ℤ_[ℓ]) := by
  refine ⟨Field.AbsoluteGaloisGroup.adicArithFrob w, ?_⟩
  have hnorm : Ideal.absNorm w.asIdeal = Nat.card (𝓞 F ⧸ w.asIdeal) := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  rw [← hnorm, ← PadicInt.ext_of_toZModPow]
  intro n
  rw [map_natCast, cyclotomicCharacter.toZModPow]
  exact (modularCyclotomicCharacter.unique
    (hn := HasEnoughRootsOfUnity.natCard_rootsOfUnity (ℚ ᵃˡᵍ) (ℓ ^ n))
    _ _ (adicArithFrob_rootsOfUnity_pow_residueCard F w hw n)).symm

/-
**REFUTED AS FIRST STATED, 2026-07-26: `isHilbertTameAtTwo_of_fibreProduct`
WITH `hℓ5 : 5 ≤ ℓ` ALONE.**

The statement below stood here in a form whose only arithmetic hypothesis
was `5 ≤ ℓ`, on the reasoning — inherited from the `ℚ`-level twin, where it
is correct — that `ℓ ≥ 5` makes the determinant test element
`N(w) − (±1)` a unit. **Over a general number field that inference is
false**, because `N(w) = 2^{f(w|2)}` is not `2`, and the counterexample
below is machine-verified.

THE COUNTEREXAMPLE (verified exhaustively over the 125-element ring `B`).

Take `ℓ = 5` and `F = ℚ(μ₅)`. Then:

* `2` is INERT in `F` (`ord₅(2) = 4 = [F : ℚ]`), so `F` has a single place
  `w ∣ 2`, with `N(w) = 16 ≡ 1 (mod 5)`. In particular `χ̄_ℓ|_{Γ F} = 1`
  identically, since `F ⊇ μ_ℓ` — the degeneracy `N(w)² ≡ 1 (mod ℓ)` holds
  in its most extreme form.
* `ord₂₅(2) = 20 = φ(25)`, so `2` is inert in `ℚ(μ₂₅)` too, i.e. `w` is
  inert in the degree-`5` extension `ℚ(μ₂₅)/F`. Hence the homomorphism
  `c : Γ F → 𝔽₅` defined by `χ_{25}(g) = 1 + 5·c(g)` is CONTINUOUS,
  nontrivial, and — this is the point — `c|_{G_w} ≠ 0`.

Now take the square-zero extensions

  `A₀ = 𝔽₅`,  `A₁ = 𝔽₅[ε₁]`,  `A₂ = 𝔽₅[ε₂]`,
  `B  = 𝔽₅[ε₁, ε₂]/(ε₁, ε₂)²`,

all discrete, so that `B = A₁ ×_{A₀} A₂` with `p₁` killing `ε₂` and `p₂`
killing `ε₁`; `f₂` is surjective, `hemb` and `hcart` are immediate. Let

  `ρ(g) = !![1, ε₂·c(g); ε₁·c(g), 1]`.

Every hypothesis of the statement as first written holds:

* `ρ` is a homomorphism (`c` is additive and `ε₁ε₂ = 0`) and continuous
  (`c` factors through a finite quotient, `B` is discrete);
* `hdet` holds: `det ρ(g) = 1 − ε₁ε₂c(g)² = 1`, and `χ̄_ℓ|_{Γ F} = 1`;
* `h₁` holds: over `A₁` the row `(1, 0)` is a left eigenvector with
  eigenvalue `1`, so `δ₁ = 1` — unramified and quadratic;
* `h₂` holds: over `A₂` the row `(0, 1)` is a left eigenvector with
  eigenvalue `1`, so `δ₂ = 1` — unramified and quadratic;
* `5 ≤ ℓ` holds.

**The conclusion FAILS: over `B` there is no unimodular `ρ|_{G_w}`-stable
row at all.** By hand: a unimodular row may be normalised to `(1, r₁)` or
to `(r₀, 1)` with `r₀` nilpotent. In the first case the eigen-equations
force `ε₂c(g) = b₀²·ε₁c(g)` where `b₀` is the residue of `r₁`, impossible
for `g` with `c(g) ≠ 0` since `ε₁` and `ε₂` are `𝔽₅`-independent; in the
second they force `ε₁c(g) = 0`, i.e. `c|_{G_w} = 0`. Machine check
(2026-07-26): an exhaustive search over all `125² = 15625` pairs
`(r₀, r₁) ∈ B²` found `2500` unimodular stable rows over each of `A₁` and
`A₂`, and **`0`** over `B`.

WHY `hℓ5` CANNOT SEE THIS. `hℓ5` is the `ℚ`-level shadow of the real
condition. Uniqueness of the line fails exactly when the two Jordan–Hölder
characters `δ̄` and `χ̄δ̄` of `ρ̄|_{G_w}` are BOTH unramified quadratic, i.e.
exactly when `χ̄²|_{G_w} = 1`, i.e. exactly when

  `N(w)² ≡ 1 (mod ℓ)`.

Over `ℚ` the only place over `2` has `N(w) = 2`, so this reads `ℓ ∣ 3`,
i.e. `ℓ = 3`, and `5 ≤ ℓ` is an exact restatement of its negation. Over a
general `F` it reads `ℓ ∣ 2^{2f(w|2)} − 1`, which `5 ≤ ℓ` does not exclude
— `ℓ = 5` violates it at `f = 2` (`4² − 1 = 15`) and at `f = 4`
(`16² − 1 = 255`), and `F = ℚ(μ₅)` above realises the second, `2` being
inert there of residue degree `4`.

**A TOTALLY REAL witness, needed one level up** (added 2026-07-26 by the
owner of `nonempty_potentialHeckeDatum_of_five_le`). `ℚ(μ₅)` refutes this
leaf, whose `F` is an arbitrary number field, but it CANNOT be used to show
that `PotentialHeckeDatum.residueCardTwo` is independent of that structure's
other fields, because `ℚ(μ₅)` is CM and so fails `totallyReal`. The witness
that does that job is `F = ℚ(√5)`: totally real (signature `[2, 0]`,
discriminant `5`), Galois over `ℚ`, with `2` INERT — one place `w ∣ 2`,
`e = 1`, `f = 2`, `N(w) = 4`, `N(w)² − 1 = 15`, and `5 ∣ 15`. Machine-checked
in PARI/GP.

THE REPAIR, PERFORMED 2026-07-26. The hypothesis `hqw` below is the sharp
condition just derived, and it SUBSUMES the `ℚ`-level `hℓ5` (at `F = ℚ`,
`N(w) = 2` and `hqw` says `ℓ ∤ 3`). `hℓ5` is nevertheless kept, because the
`2` in `hu2` — used to split `e² = 1` into `e = ±1` over the local ring
`A₀` — needs `ℓ` odd, and because every consumer already carries it.

CONSEQUENCE FOR THE CUT, WHICH IS NOT REPAIRED HERE AND MUST NOT BE
FORGOTTEN. `hqw` propagates: `isHilbertFibreProductClause` now carries it
for every `w ∣ 2`, and so does `exists_isWeaklyUniversal_hilbertDeformationDatum`.
At the top of the module the field `F` is not free — it is the totally real
field PRODUCED by potential modularity — so the condition has to be
IMPOSED THERE, and it is: `PotentialHeckeDatum.residueCardTwo` asks that
every place of `F` over `2` have residue field `𝔽₂`. That is free in
Taylor's argument (Moret–Bailly's theorem lets one prescribe the local
behaviour of `F` at any finite set of places, in particular demand that `2`
split completely), and it makes `N(w)² − 1 = 3`, so `hqw` follows from
`5 ≤ ℓ` again. Anyone weakening `PotentialHeckeDatum.residueCardTwo` must
re-derive `hqw` some other way, or this leaf becomes false again.
-/

/-- **The tame quadratic quotient at a place over `2` glues along a fibre
product** (PROVEN 2026-07-26 over the arithmetic leaf
`exists_cyclotomicCharacter_adicCompletion_eq_residueCard` and the
linear-algebra brick `exists_unit_smul_of_vecMul_eq_row` above;
Conrad–Diamond–Taylor — the second arithmetic residue of Schlessinger's
H1/H2 over `F`, and the `F`-level twin of `Deformation.lean`'s
`isTameAtTwo_of_fibreProduct`).

**THIS STATEMENT CARRIES `hqw`, AND MUST.** `hqw` says `ℓ ∤ N(w)² − 1`,
i.e. `χ̄_ℓ²|_{G_w} ≠ 1`. Without it the statement is FALSE — refuted
2026-07-26 at `ℓ = 5`, `F = ℚ(μ₅)`, with a machine-verified counterexample
recorded in the block comment immediately above. `hℓ5 : 5 ≤ ℓ` alone does
NOT suffice over a general number field, however it may look next to the
`ℚ`-level twin: there `N(w) = 2` and `hqw` degenerates to `ℓ ≠ 3`.

WHY IT IS NOT FORMAL. The tame clause is an EXISTENTIAL — SOME surjection
`p` and SOME unramified quadratic `δ`. So `h₁` and `h₂` hand you a line
over `A₁` and a line over `A₂` with no compatibility whatever over `A₀`,
while a line over the fibre product is exactly a compatible PAIR of lines.
Everything turns on a uniqueness statement forcing the two given choices to
agree over `A₀`, and that uniqueness is what `hdet` and `hqw` buy:

* `χ_ℓ` is unramified on `G_{F_w}` with `χ_ℓ(Frob_w) = N(w) = 2^{f(w|2)}`,
  because `w ∤ ℓ`; so the two Jordan–Hölder characters of `ρ̄|_{G_w}`,
  namely `χ̄δ̄` and `δ̄`, differ by `χ̄|_{G_w}`;
* those two characters can COINCIDE as candidates for the clause only when
  `χ̄²|_{G_w} = 1`, i.e. when `N(w)² ≡ 1 mod ℓ`, which `hqw` excludes;
* with `hqw` the test element `det ρ(Frob_w) − δ₁(Frob_w)δ₂(Frob_w)`,
  which is `N(w) ∓ 1`, is a unit of `A₀`, and
  `exists_unit_smul_of_vecMul_eq_row` forces the two rows proportional over
  `A₀`; then `hf₂` rescales one of them and `hcart` glues them entrywise.

HOW IT IS PROVEN HERE, following the `ℚ`-level proof step for step, at the
level of ROWS rather than of Jordan–Hölder factors so that no
semisimplification or residual reduction is needed.

1. `hqw` makes `N(w) − 1` and `N(w) + 1` units in the local `ℤ_ℓ`-algebra
   `A₀`; `hℓ5` makes `2` one.
2. Each of `h₁`, `h₂` is a SURJECTIVE functional, i.e. a UNIMODULAR row
   `rᵢ = (πᵢ e₀, πᵢ e₁)`, and the equivariance clause says exactly that
   this row is a LEFT EIGENVECTOR of the matrix of `ρ(g₀)` with eigenvalue
   `δᵢ(g₀)`, for `g₀` the Frobenius at `w` supplied by the arithmetic leaf.
3. `hdet` at `g₀` gives `det ρ(g₀) = N(w)`, and the quadratic clause gives
   `δ₁(g₀)δ₂(g₀) = ±1`, so the test element is `N(w) − 1` or `N(w) + 1`
   — a unit by (1).
4. Lifting the resulting unit through the SURJECTION `f₂` and rescaling
   `π₂` by its inverse makes the two rows literally EQUAL over `A₀`, so
   `hcart` glues them entrywise into a row over `B`; the glued functional
   is surjective because `p₁` is a surjection of local rings.
5. The character is then `ε g := π (ρ(g) x₀)` for any `π x₀ = 1`: it is
   multiplicative, unramified and quadratic because `hemb` makes `B` inject
   into `A₁ × A₂` and each of those statements is an identity of VALUES,
   which descends along an injection.

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
    (hqw : ¬ ((ℓ : ℤ) ∣ ((Nat.card (𝓞 F ⧸ w.asIdeal) : ℤ) ^ 2 - 1)))
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
      ∀ g : Γ (w.adicCompletion F), δ g * δ g = 1 := by
  classical
  set q : ℕ := Nat.card (𝓞 F ⧸ w.asIdeal) with hqdef
  -- STEP 1. `N(w) ∓ 1` and `2` are units in `A₀`.
  have hunitZ : ∀ m : ℤ, ¬ ((ℓ : ℤ) ∣ m) → IsUnit ((m : A₀)) := by
    intro m hm
    have h : IsUnit ((m : ℤ_[ℓ])) := by
      by_contra hcon
      rw [PadicInt.not_isUnit_iff, PadicInt.norm_intCast_lt_one_iff] at hcon
      exact hm hcon
    have h2 := h.map (algebraMap ℤ_[ℓ] A₀)
    rwa [map_intCast] at h2
  have hfacq : ((q : ℤ) ^ 2 - 1) = ((q : ℤ) - 1) * ((q : ℤ) + 1) := by ring
  have hqm : IsUnit (((q : ℤ) - 1 : ℤ) : A₀) :=
    hunitZ _ fun h => hqw (by rw [hfacq]; exact h.mul_right _)
  have hqp : IsUnit (((q : ℤ) + 1 : ℤ) : A₀) :=
    hunitZ _ fun h => hqw (by rw [hfacq]; exact h.mul_left _)
  have hu2 : IsUnit ((2 : ℕ) : A₀) := by
    have hp : ℓ.Prime := Fact.out
    have h : IsUnit ((2 : ℕ) : ℤ_[ℓ]) := PadicInt.isUnit_iff.mpr
      (PadicInt.norm_natCast_eq_one_iff.mpr
        ((Nat.coprime_primes hp Nat.prime_two).mpr (by omega)))
    have h2 := h.map (algebraMap ℤ_[ℓ] A₀)
    rwa [map_natCast] at h2
  -- STEP 2. `w` does not lie over `ℓ`, so the arithmetic leaf applies.
  have hwl : ((ℓ : ℕ) : 𝓞 F) ∉ w.asIdeal := by
    intro hmem
    have hp : ℓ.Prime := Fact.out
    have hgcd : Int.gcd 2 (ℓ : ℤ) = 1 := by
      have : Nat.Coprime 2 ℓ := (Nat.coprime_primes Nat.prime_two hp).mpr (by omega)
      simpa [Int.gcd] using this
    obtain ⟨a, b, hab⟩ := Int.isCoprime_iff_gcd_eq_one.mpr hgcd
    have hone : (1 : 𝓞 F) ∈ w.asIdeal := by
      have hsum := w.asIdeal.add_mem (w.asIdeal.mul_mem_left ((a : ℤ) : 𝓞 F) hw)
        (w.asIdeal.mul_mem_left ((b : ℤ) : 𝓞 F) hmem)
      have hcast : ((a : 𝓞 F) * ((2 : ℕ) : 𝓞 F) + (b : 𝓞 F) * ((ℓ : ℕ) : 𝓞 F))
          = 1 := by
        have := congrArg (fun z : ℤ => (z : 𝓞 F)) hab
        push_cast at this ⊢
        exact this
      rwa [hcast] at hsum
    exact w.isPrime.ne_top (Ideal.eq_top_iff_one _ |>.mpr hone)
  obtain ⟨g₀, hg₀⟩ :=
    exists_cyclotomicCharacter_adicCompletion_eq_residueCard ℓ F w hwl
  -- STEP 3. Unpack the two given lines and put them in row form.
  obtain ⟨π₁, hπ₁surj, δ₁, hδ₁eq, hδ₁ker, hδ₁sq⟩ := h₁
  obtain ⟨π₂, hπ₂surj, δ₂, hδ₂eq, hδ₂ker, hδ₂sq⟩ := h₂
  have hinj : ∀ b b' : B, p₁ b = p₁ b' → p₂ b = p₂ b' → b = b' := by
    intro b b' hb₁ hb₂
    exact hemb.injective (by simp only [Prod.mk.injEq]; exact ⟨hb₁, hb₂⟩)
  have hπ₁val : ∀ v : Fin 2 → A₁, π₁ v = ∑ i, π₁ (Pi.single i 1) * v i := by
    intro v
    conv_lhs => rw [pi_eq_sum_univ' v]
    rw [map_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [map_smul, smul_eq_mul, mul_comm]
  have hπ₂val : ∀ v : Fin 2 → A₂, π₂ v = ∑ i, π₂ (Pi.single i 1) * v i := by
    intro v
    conv_lhs => rw [pi_eq_sum_univ' v]
    rw [map_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [map_smul, smul_eq_mul, mul_comm]
  have hδ₁val : ∀ (g : Γ (w.adicCompletion F)) (x : A₁), δ₁ g x = δ₁ g 1 * x := by
    intro g x
    conv_lhs => rw [show x = x • (1 : A₁) by rw [smul_eq_mul, mul_one]]
    rw [map_smul, smul_eq_mul, mul_comm]
  have hδ₂val : ∀ (g : Γ (w.adicCompletion F)) (x : A₂), δ₂ g x = δ₂ g 1 * x := by
    intro g x
    conv_lhs => rw [show x = x • (1 : A₂) by rw [smul_eq_mul, mul_one]]
    rw [map_smul, smul_eq_mul, mul_comm]
  have htr₁ : ∀ (g : Γ (w.adicCompletion F)) (v : Fin 2 → B),
      (fun i => p₁ (ρ.toLocal w g v i)) =
      (framePushforward p₁ hp₁ ρ).toLocal w g (fun i => p₁ (v i)) := by
    intro g v
    funext i
    rw [GaloisRep.toLocal_apply, GaloisRep.toLocal_apply]
    exact (framePushforward_apply_map p₁ hp₁ ρ _ v i).symm
  have htr₂ : ∀ (g : Γ (w.adicCompletion F)) (v : Fin 2 → B),
      (fun i => p₂ (ρ.toLocal w g v i)) =
      (framePushforward p₂ hp₂ ρ).toLocal w g (fun i => p₂ (v i)) := by
    intro g v
    funext i
    rw [GaloisRep.toLocal_apply, GaloisRep.toLocal_apply]
    exact (framePushforward_apply_map p₂ hp₂ ρ _ v i).symm
  have hrel₁ : ∀ (g : Γ (w.adicCompletion F)) (v : Fin 2 → B),
      π₁ (fun i => p₁ (ρ.toLocal w g v i)) = δ₁ g 1 * π₁ (fun i => p₁ (v i)) := by
    intro g v
    rw [htr₁ g v, hδ₁eq g (fun i => p₁ (v i)), hδ₁val]
  have hrel₂ : ∀ (g : Γ (w.adicCompletion F)) (v : Fin 2 → B),
      π₂ (fun i => p₂ (ρ.toLocal w g v i)) = δ₂ g 1 * π₂ (fun i => p₂ (v i)) := by
    intro g v
    rw [htr₂ g v, hδ₂eq g (fun i => p₂ (v i)), hδ₂val]
  have hsq₁ : ∀ g, δ₁ g 1 * δ₁ g 1 = 1 := by
    intro g
    have h := hδ₁sq g
    have h2 : (δ₁ g * δ₁ g) (1 : A₁) = (1 : Module.End A₁ A₁) 1 := by rw [h]
    rwa [Module.End.mul_apply, Module.End.one_apply, hδ₁val] at h2
  have hsq₂ : ∀ g, δ₂ g 1 * δ₂ g 1 = 1 := by
    intro g
    have h := hδ₂sq g
    have h2 : (δ₂ g * δ₂ g) (1 : A₂) = (1 : Module.End A₂ A₂) 1 := by rw [h]
    rwa [Module.End.mul_apply, Module.End.one_apply, hδ₂val] at h2
  -- STEP 4. The matrix of `ρ` at the Frobenius, and its determinant.
  set φ₀ : B →+* A₀ := f₁.comp p₁ with hφ₀def
  have hφ₀' : ∀ b : B, φ₀ b = f₂ (p₂ b) := by
    intro b
    rw [hφ₀def]
    exact congrArg (fun G : B →+* A₀ => G b) hcomm
  set M : Matrix (Fin 2) (Fin 2) B :=
    LinearMap.toMatrix' (ρ.toLocal w g₀) with hMdef
  have hdetM : M.det = ((q : ℕ) : B) := by
    rw [hMdef, LinearMap.det_toMatrix', GaloisRep.toLocal_apply,
      ← GaloisRep.det_apply, hdet, hg₀, map_natCast]
  have hsingle₁ : ∀ j : Fin 2,
      (fun i => p₁ ((Pi.single j (1 : B) : Fin 2 → B) i)) =
      (Pi.single j (1 : A₁) : Fin 2 → A₁) := by
    intro j
    funext i
    by_cases hij : i = j <;> simp [hij]
  have hsingle₂ : ∀ j : Fin 2,
      (fun i => p₂ ((Pi.single j (1 : B) : Fin 2 → B) i)) =
      (Pi.single j (1 : A₂) : Fin 2 → A₂) := by
    intro j
    funext i
    by_cases hij : i = j <;> simp [hij]
  have hrow₁ : ∀ j, ∑ i, f₁ (π₁ (Pi.single i 1)) * (M.map φ₀) i j =
      f₁ (δ₁ g₀ 1) * f₁ (π₁ (Pi.single j 1)) := by
    intro j
    have h := hrel₁ g₀ (Pi.single j 1)
    rw [hsingle₁ j] at h
    rw [hπ₁val] at h
    have h2 := congrArg f₁ h
    simp only [map_sum, map_mul] at h2
    exact h2
  have hrow₂ : ∀ j, ∑ i, f₂ (π₂ (Pi.single i 1)) * (M.map φ₀) i j =
      f₂ (δ₂ g₀ 1) * f₂ (π₂ (Pi.single j 1)) := by
    intro j
    have h := hrel₂ g₀ (Pi.single j 1)
    rw [hsingle₂ j] at h
    rw [hπ₂val] at h
    have h2 := congrArg f₂ h
    simp only [map_sum, map_mul] at h2
    simp only [Matrix.map_apply, hφ₀']
    exact h2
  obtain ⟨w₁, hw₁⟩ := hπ₁surj 1
  obtain ⟨w₂, hw₂⟩ := hπ₂surj 1
  have huni₁ : ∑ i, f₁ (π₁ (Pi.single i 1)) * f₁ (w₁ i) = 1 := by
    have h := congrArg f₁ (hπ₁val w₁)
    rw [hw₁, map_one] at h
    simp only [map_sum, map_mul] at h
    exact h.symm
  have huni₂ : ∑ i, f₂ (π₂ (Pi.single i 1)) * f₂ (w₂ i) = 1 := by
    have h := congrArg f₂ (hπ₂val w₂)
    rw [hw₂, map_one] at h
    simp only [map_sum, map_mul] at h
    exact h.symm
  -- STEP 5. The eigenvalue product is `±1`, so the test element is a unit.
  have hprod : (f₁ (δ₁ g₀ 1) * f₂ (δ₂ g₀ 1)) * (f₁ (δ₁ g₀ 1) * f₂ (δ₂ g₀ 1)) = 1 := by
    have e1 := congrArg f₁ (hsq₁ g₀)
    have e2 := congrArg f₂ (hsq₂ g₀)
    rw [map_mul, map_one f₁] at e1
    rw [map_mul, map_one f₂] at e2
    calc (f₁ (δ₁ g₀ 1) * f₂ (δ₂ g₀ 1)) * (f₁ (δ₁ g₀ 1) * f₂ (δ₂ g₀ 1))
        = (f₁ (δ₁ g₀ 1) * f₁ (δ₁ g₀ 1)) * (f₂ (δ₂ g₀ 1) * f₂ (δ₂ g₀ 1)) := by ring
      _ = 1 := by rw [e1, e2, one_mul]
  have hpm : f₁ (δ₁ g₀ 1) * f₂ (δ₂ g₀ 1) = 1 ∨ f₁ (δ₁ g₀ 1) * f₂ (δ₂ g₀ 1) = -1 := by
    set e := f₁ (δ₁ g₀ 1) * f₂ (δ₂ g₀ 1) with hedef
    have hfac : (e - 1) * (e + 1) = 0 := by linear_combination hprod
    have hsum : IsUnit ((1 + e) + (1 - e)) := by
      have h : (1 + e) + (1 - e) = ((2 : ℕ) : A₀) := by push_cast; ring
      rw [h]; exact hu2
    rcases IsLocalRing.isUnit_or_isUnit_of_isUnit_add hsum with h | h
    · left
      obtain ⟨t, ht⟩ := h.exists_right_inv
      have h0 : e - 1 = 0 := by
        have h1 : (e - 1) * ((1 + e) * t) = 0 := by
          rw [show (e - 1) * ((1 + e) * t) = ((e - 1) * (e + 1)) * t by ring,
            hfac, zero_mul]
        rwa [ht, mul_one] at h1
      exact sub_eq_zero.mp h0
    · right
      obtain ⟨t, ht⟩ := h.exists_right_inv
      have h0 : e + 1 = 0 := by
        have h1 : (e + 1) * ((1 - e) * t) = 0 := by
          rw [show (e + 1) * ((1 - e) * t) = (-((e - 1) * (e + 1))) * t by ring,
            hfac, neg_zero, zero_mul]
        rwa [ht, mul_one] at h1
      exact eq_neg_of_add_eq_zero_left h0
  have hunitdet : IsUnit ((M.map φ₀).det - f₁ (δ₁ g₀ 1) * f₂ (δ₂ g₀ 1)) := by
    have hdet0 : (M.map φ₀).det = ((q : ℕ) : A₀) := by
      show (φ₀.mapMatrix M).det = _
      rw [← RingHom.map_det, hdetM, map_natCast]
    rw [hdet0]
    rcases hpm with h | h
    · rw [h, show ((q : ℕ) : A₀) - 1 = (((q : ℤ) - 1 : ℤ) : A₀) by push_cast; ring]
      exact hqm
    · rw [h, show ((q : ℕ) : A₀) - (-1) = (((q : ℤ) + 1 : ℤ) : A₀) by push_cast; ring]
      exact hqp
  -- STEP 6. The two rows agree over `A₀` after rescaling, and glue over `B`.
  obtain ⟨u, huunit, hu⟩ := exists_unit_smul_of_vecMul_eq_row (M.map φ₀)
    (fun i => f₁ (π₁ (Pi.single i 1))) (fun i => f₂ (π₂ (Pi.single i 1)))
    (f₁ (δ₁ g₀ 1)) (f₂ (δ₂ g₀ 1)) hrow₁ hrow₂ ⟨_, huni₁⟩ ⟨_, huni₂⟩ hunitdet
  obtain ⟨ū, hū⟩ := hf₂ u
  haveI : IsLocalHom f₂ := IsLocalHom.of_surjective f₂ hf₂
  have hūunit : IsUnit ū := IsLocalHom.map_nonunit ū (by rw [hū]; exact huunit)
  obtain ⟨s, hs⟩ := hūunit.exists_right_inv
  have hfs : f₂ s * u = 1 := by
    have h := congrArg f₂ hs
    rw [map_mul, map_one, hū] at h
    rw [mul_comm]; exact h
  have hcompat : ∀ i, f₁ (π₁ (Pi.single i 1)) = f₂ (s * π₂ (Pi.single i 1)) := by
    intro i
    rw [map_mul, hu i, ← mul_assoc, hfs, one_mul]
  choose rB hrB₁ hrB₂ using fun i =>
    hcart (π₁ (Pi.single i 1)) (s * π₂ (Pi.single i 1)) (hcompat i)
  set π : (Fin 2 → B) →ₗ[B] B :=
    ∑ i, (rB i) • (LinearMap.proj i : (Fin 2 → B) →ₗ[B] B) with hπdef
  have hπval : ∀ v : Fin 2 → B, π v = ∑ i, rB i * v i := by
    intro v
    rw [hπdef]
    simp [smul_eq_mul]
  have hpush₁ : ∀ v : Fin 2 → B, p₁ (π v) = π₁ (fun i => p₁ (v i)) := by
    intro v
    rw [hπval, hπ₁val, map_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [map_mul, hrB₁]
  have hpush₂ : ∀ v : Fin 2 → B, p₂ (π v) = s * π₂ (fun i => p₂ (v i)) := by
    intro v
    rw [hπval, hπ₂val, map_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [map_mul, hrB₂, mul_assoc]
  have hp₁surj : Function.Surjective p₁ := by
    intro a₁
    obtain ⟨a₂, ha₂⟩ := hf₂ (f₁ a₁)
    obtain ⟨b, hb₁, _⟩ := hcart a₁ a₂ ha₂.symm
    exact ⟨b, hb₁⟩
  haveI : IsLocalHom p₁ := IsLocalHom.of_surjective p₁ hp₁surj
  have hrBunit : ∃ i, IsUnit (rB i) := by
    have h1 : IsUnit (π₁ (Pi.single 0 1) * w₁ 0 + π₁ (Pi.single 1 1) * w₁ 1) := by
      have h := hπ₁val w₁
      rw [hw₁, Fin.sum_univ_two] at h
      rw [← h]; exact isUnit_one
    rcases IsLocalRing.isUnit_or_isUnit_of_isUnit_add h1 with h | h
    · exact ⟨0, IsLocalHom.map_nonunit (f := p₁) _
        (by rw [hrB₁]; exact isUnit_of_mul_isUnit_left h)⟩
    · exact ⟨1, IsLocalHom.map_nonunit (f := p₁) _
        (by rw [hrB₁]; exact isUnit_of_mul_isUnit_left h)⟩
  obtain ⟨i₀, hi₀⟩ := hrBunit
  obtain ⟨t₀, ht₀⟩ := hi₀.exists_right_inv
  have hπsurj : Function.Surjective π := by
    intro c
    refine ⟨Pi.single i₀ (t₀ * c), ?_⟩
    rw [hπval, Finset.sum_eq_single i₀]
    · rw [Pi.single_eq_same, ← mul_assoc, ht₀, one_mul]
    · intro j _ hj; rw [Pi.single_eq_of_ne hj, mul_zero]
    · intro h; exact absurd (Finset.mem_univ i₀) h
  obtain ⟨x₀, hx₀⟩ := hπsurj 1
  -- STEP 7. The glued character.
  set ε : Γ (w.adicCompletion F) → B := fun g => π (ρ.toLocal w g x₀) with hεdef
  have hone₁ : π₁ (fun i => p₁ (x₀ i)) = 1 := by
    rw [← hpush₁, hx₀, map_one]
  have hone₂ : s * π₂ (fun i => p₂ (x₀ i)) = 1 := by
    rw [← hpush₂, hx₀, map_one]
  have hp₁ε : ∀ g, p₁ (ε g) = δ₁ g 1 := by
    intro g
    rw [hεdef]
    show p₁ (π (ρ.toLocal w g x₀)) = δ₁ g 1
    rw [hpush₁, hrel₁ g x₀, hone₁, mul_one]
  have hp₂ε : ∀ g, p₂ (ε g) = δ₂ g 1 := by
    intro g
    rw [hεdef]
    show p₂ (π (ρ.toLocal w g x₀)) = δ₂ g 1
    rw [hpush₂, hrel₂ g x₀, show s * (δ₂ g 1 * π₂ (fun i => p₂ (x₀ i))) =
      δ₂ g 1 * (s * π₂ (fun i => p₂ (x₀ i))) by ring, hone₂, mul_one]
  have hequiv : ∀ (g : Γ (w.adicCompletion F)) (v : Fin 2 → B),
      π (ρ.toLocal w g v) = ε g * π v := by
    intro g v
    refine hinj _ _ ?_ ?_
    · rw [hpush₁, hrel₁ g v, map_mul, hp₁ε, hpush₁]
    · rw [hpush₂, hrel₂ g v, map_mul, hp₂ε, hpush₂]; ring
  have hεone : ε 1 = 1 := by
    rw [hεdef]
    show π (ρ.toLocal w 1 x₀) = 1
    rw [map_one]
    exact hx₀
  have hεmul : ∀ g h, ε (g * h) = ε g * ε h := by
    intro g h
    have hcomp : (ρ.toLocal w) (g * h) x₀ =
        (ρ.toLocal w) g ((ρ.toLocal w) h x₀) := by
      rw [map_mul]; rfl
    rw [hεdef]
    show π ((ρ.toLocal w) (g * h) x₀) =
      π ((ρ.toLocal w) g x₀) * π ((ρ.toLocal w) h x₀)
    rw [hcomp, hequiv g _]
  letI := moduleTopology B (Module.End B (Fin 2 → B))
  letI := moduleTopology B (Module.End B B)
  haveI : ContinuousAdd (Module.End B B) := ModuleTopology.continuousAdd B _
  haveI : ContinuousSMul B (Module.End B B) := ModuleTopology.continuousSMul B _
  have hεcont : Continuous ε := by
    have h1 : ε = fun g => (π ∘ₗ (LinearMap.applyₗ x₀ :
        Module.End B (Fin 2 → B) →ₗ[B] (Fin 2 → B)))
        ((ρ.toLocal w) g) := rfl
    rw [h1]
    exact (IsModuleTopology.continuous_of_linearMap _).comp
      (ρ.toLocal w).continuous_toFun
  set δ : GaloisRep (w.adicCompletion F) B B :=
    { toFun := fun g => ε g • (1 : Module.End B B)
      map_one' := by rw [hεone, one_smul]
      map_mul' := fun g h => by
        refine LinearMap.ext fun c => ?_
        simp only [hεmul, LinearMap.smul_apply, Module.End.one_apply,
          Module.End.mul_apply, smul_eq_mul]
        ring
      continuous_toFun := hεcont.smul continuous_const } with hδdef
  have hδapp : ∀ (g : Γ (w.adicCompletion F)) (c : B), δ g c = ε g * c := by
    intro g c
    show (ε g • (1 : Module.End B B)) c = ε g * c
    rw [LinearMap.smul_apply, Module.End.one_apply, smul_eq_mul]
  refine ⟨π, hπsurj, δ, ?_, ?_, ?_⟩
  · intro g v
    rw [hequiv g v, hδapp]
  · intro σ hσ
    have h1 : δ₁ σ 1 = 1 := by
      have h2 : δ₁ σ = 1 := hδ₁ker hσ
      rw [h2]; rfl
    have h2 : δ₂ σ 1 = 1 := by
      have h3 : δ₂ σ = 1 := hδ₂ker hσ
      rw [h3]; rfl
    have hε1 : ε σ = 1 := by
      refine hinj _ _ ?_ ?_
      · rw [hp₁ε, h1, map_one]
      · rw [hp₂ε, h2, map_one]
    show δ σ = 1
    rw [hδdef]
    show ε σ • (1 : Module.End B B) = 1
    rw [hε1, one_smul]
  · intro g'
    have hεsq : ε g' * ε g' = 1 := by
      refine hinj _ _ ?_ ?_
      · rw [map_mul, hp₁ε, hsq₁, map_one]
      · rw [map_mul, hp₂ε, hsq₂, map_one]
    refine LinearMap.ext fun c => ?_
    show (δ g') ((δ g') c) = c
    rw [hδapp, hδapp, ← mul_assoc, hεsq, one_mul]

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

`isHilbertBaseChangeClause` is now PROVEN (2026-07-26), through
`hasFlatProlongationAt_of_pi_surjection_of_numberField` below — which is
itself PROVEN as of the same day, so this whole clause is now sorry-free.
The cut is `Deformation.lean`'s `ℚ`-level cut of
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

**PROVEN 2026-07-26, BY THE HOIST THE PREVIOUS OWNER SCOUTED** — and the
sorry count went down by one while the COPY COUNT went down too. The
route, recorded because the reasoning is reusable:

At `K = ℚ` this is `Deformation.lean`'s PROVEN
`hasFlatProlongationAt_of_pi_surjection`, which lives DOWNSTREAM of this
module and so is unreachable from here. That proof is four lines: it
passes to the representation-free carrier
`GaloisRepresentation.Modularity.IsFlatPointsGroupAt` and applies
`IsFlatPointsGroupAt.pi` and `IsFlatPointsGroupAt.of_surjective`, both
PROVEN, in `Deformations/RepresentationTheory/FlatPointsGroup.lean`.

That whole file — 1950 sorry-free lines — mentioned `ℚ` exactly EIGHT
times, all of them inside `variable (v : HeightOneSpectrum (𝓞 ℚ))` and the
four `local notation`s `Kᵥ`/`𝒪ᵥ`/`Γᵥ`/`Ωᵥ` derived from it, plus one
`CharZero (adicCompletion ℚ v)` instance step. Nothing in its mathematics
was about `ℚ`: every argument is about the local field `K_w` and the DVR
`𝒪_w`. So that `variable` line was HOISTED to
`{K : Type u} [Field K] [NumberField K]`, together with the fifteen
`Type`-valued binders for the Hopf algebras, which had to move from
`Type 0` to `Type u` (`HasFlatProlongationAt` itself already quantifies
its witness over `Type uK`, so this only restores the alignment; over a
base field in `Type u` with `u > 0` a `Type 0` binder would have made the
witnesses' existentials vacuous, since a field in `Type u` does not embed
in a `Type 0` algebra). The whole file then re-elaborated CLEAN in 32 s
with no other change, and the `ℚ` statement is now literally an instance
of the general one, so `Deformation.lean`'s `ℚ`-level theorem is
unchanged and no second copy of the argument exists.

The one concern the previous owner raised — that importing
`FlatPointsGroup.lean` here widens this module's deliberately minimal
import surface, since it pulls `KnownIn1980s/EllipticCurves/Flat.lean` —
was CHECKED and is not a cost to anyone but this file's own elaboration:
`FlatPointsGroup.lean`'s `Fermat`-side import closure is 38 modules and
contains nothing from `HardlyRamified/`, `Family.lean`, `Lift.lean`,
`Deformation.lean` or `Modularity/*`, so the circularity guard is intact;
and `Deformation.lean` — the SOLE consumer of this module — already
imports `FlatPointsGroup.lean` directly, so no downstream cone grows by a
single module. See the import comment at the head of this file.

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
    ρ₂.HasFlatProlongationAt w := by
  -- pass to the representation-free point-group carrier
  have h₁ : Modularity.IsFlatPointsGroupAt w (ρ₁.toLocal w).Space :=
    (Modularity.GaloisRep.hasFlatProlongationAt_iff_isFlatPointsGroupAt ρ₁).mp h
  -- products: the finite power is the point group of the tensor power of the
  -- witness Hopf algebra
  have hpow : Modularity.IsFlatPointsGroupAt w
      (∀ _ : Fin n, (ρ₁.toLocal w).Space) :=
    Modularity.IsFlatPointsGroupAt.pi fun _ => h₁
  -- quotients: schematic closure over the DVR along the equivariant surjection
  exact (Modularity.GaloisRep.hasFlatProlongationAt_iff_isFlatPointsGroupAt ρ₂).mpr
    (hpow.of_surjective π hsurj hequiv)

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
/-- **Functoriality of the `F`-level condition** (PROVEN 2026-07-26, through
the now also PROVEN `hasFlatProlongationAt_of_pi_surjection_of_numberField`).

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

/-! #### Raynaud closure, sub-of-a-product form, over an ARBITRARY number
field

WHY THIS SITS HERE, AT THE BOTTOM OF THE FILE, RATHER THAN BESIDE ITS
SIBLING RESIDUE. `isHilbertFlatAt_of_fibreProduct` below needs BOTH Raynaud
closure properties at a place of a general number field: sub-of-a-product
AND quotient. The quotient one already exists in this module as
`hasFlatProlongationAt_of_pi_surjection_of_numberField` (above; another
owner's leaf, in flight as of 2026-07-26) — so the flatness residue and its
new sub-of-a-product leaf were MOVED DOWN past it rather than a second
quotient leaf being stated. That duplicate was written first and deleted:
declaration order was the only thing forcing it, and a redundant sorried
leaf is exactly what generates phantom dispatches here.

WHAT DISCHARGED THE LEAF BELOW — the same thing that discharged its
quotient sibling, so read that leaf's docstring too. DONE 2026-07-26; the
prediction recorded here held exactly, and the record is kept because the
reasoning is reusable.
`Deformations/RepresentationTheory/FlatPointsGroup.lean` already carried
the closure properties of "the geometric-point group of a finite flat
`𝒪ᵥ`-group scheme with étale generic fibre" — `IsFlatPointsGroupAt.prod`,
`.pi`, `.of_injective`, `.of_surjective` — all four PROVEN there.
They were, however, available only at a place of `ℚ`: that file's
`RaynaudClosure` section opened with

    variable (v : HeightOneSpectrum (NumberField.RingOfIntegers ℚ))

and `IsFlatPointsGroupAt` itself is defined inside it. So `Deformation.lean`
could consume them, while THIS module — whose places `w` run over an
arbitrary totally real `F` — could not.

**This was therefore not new mathematics and was not attacked as such.**
That `variable` line was HOISTED to a general
`{K : Type u} [Field K] [NumberField K]`, which closed this leaf AND
`hasFlatProlongationAt_of_pi_surjection_of_numberField` together, each by a
two-line consumption — nothing in those proofs used `K = ℚ`, only the
complete DVR `𝒪ᵥ`, its fraction field `Kᵥ`, an algebraic closure `Ωᵥ` and
the action of `Γ Kᵥ`, all of which `FlatProlongation.lean` — imported here
— already carried over a variable `{K : Type uKf} [Field K] [NumberField K]`.
The same change also retired `Deformation.lean`'s
`hasFlatProlongationAt_of_prod_injection` (the `K = ℚ` instance of the leaf
below), which is now PROVEN by the identical three-line assembly against
the same hoisted lemmas. It was proven in place rather than redirected to
this module: both forms cost the same three lines over
`FlatPointsGroup.lean`, and proving it in place keeps `Deformation.lean`'s
proof independent of declaration ORDER in this file — the very hazard the
note at the head of this section is about.

The name differs from `Deformation.lean`'s deliberately: that module
`public import`s this one into the SAME namespace, so a matching name is a
"has already been declared" outage. -/

/-- **Raynaud closure, sub-of-a-product form, over an arbitrary number
field** (PROVEN 2026-07-26): a `Γ Kᵥ`-equivariant additive SUBOBJECT of
the product of two flat point-groups at `w` is again one.

Mathematically: `ρ₁` and `ρ₂` have finite flat prolongations `G₁`, `G₂`
over the complete DVR `𝒪_{K_w}`; the product group scheme `G₁ × G₂`
prolongs the product of the two local spaces; and the SCHEMATIC CLOSURE of
the subgroup cut out by `ι` inside `G₁ × G₂` is a finite flat closed
subgroup scheme over the DVR with the prescribed generic fibre. Existence
of the schematic closure is unconditional over a DVR — it needs no
Raynaud uniqueness and hence no bound on the ramification index `e`
against `ℓ − 1`, which is why this form of the statement has no hypothesis
relating `ℓ` to `w`.

DISCHARGED BY: `Modularity.IsFlatPointsGroupAt.prod` followed by
`.of_injective`, both now stated over a variable number field; see the
section note above. At `K = ℚ` this is verbatim `Deformation.lean`'s
`hasFlatProlongationAt_of_prod_injection`, which is PROVEN by the same
three-line assembly against the same two hoisted lemmas.

References: Raynaud, *Schémas en groupes de type `(p,…,p)`*, Bull. SMF 102
(1974), §3; Conrad, *Finite group schemes over bases with low
ramification*, Compositio 119 (1999), §1 (schematic closure). -/
theorem hasFlatProlongationAt_of_prod_injection_over_numberField
    {K : Type*} [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K))
    {A₁ : Type*} [CommRing A₁] [TopologicalSpace A₁]
    {M₁ : Type*} [AddCommGroup M₁] [Module A₁ M₁]
    {A₂ : Type*} [CommRing A₂] [TopologicalSpace A₂]
    {M₂ : Type*} [AddCommGroup M₂] [Module A₂ M₂]
    {A₃ : Type*} [CommRing A₃] [TopologicalSpace A₃]
    {M₃ : Type*} [AddCommGroup M₃] [Module A₃ M₃]
    {ρ₁ : GaloisRep K A₁ M₁} {ρ₂ : GaloisRep K A₂ M₂} {ρ₃ : GaloisRep K A₃ M₃}
    (h₁ : ρ₁.HasFlatProlongationAt w) (h₂ : ρ₂.HasFlatProlongationAt w)
    (ι : (ρ₃.toLocal w).Space →+
      ((ρ₁.toLocal w).Space × (ρ₂.toLocal w).Space))
    (hinj : Function.Injective ι)
    (hequiv : ∀ (g : Γ (w.adicCompletion K)) (x : (ρ₃.toLocal w).Space),
      ι (g • x) = g • ι x) :
    ρ₃.HasFlatProlongationAt w := by
  -- pass both flat prolongations to the representation-free point-group carrier
  have hp₁ : Modularity.IsFlatPointsGroupAt w (ρ₁.toLocal w).Space :=
    (Modularity.GaloisRep.hasFlatProlongationAt_iff_isFlatPointsGroupAt ρ₁).mp h₁
  have hp₂ : Modularity.IsFlatPointsGroupAt w (ρ₂.toLocal w).Space :=
    (Modularity.GaloisRep.hasFlatProlongationAt_iff_isFlatPointsGroupAt ρ₂).mp h₂
  -- binary products: the product group scheme is represented by the tensor
  -- product of the two witness Hopf algebras
  have hprod : Modularity.IsFlatPointsGroupAt w
      ((ρ₁.toLocal w).Space × (ρ₂.toLocal w).Space) := hp₁.prod hp₂
  -- subobjects: schematic closure over the DVR along the equivariant injection
  exact (Modularity.GaloisRep.hasFlatProlongationAt_iff_isFlatPointsGroupAt ρ₃).mpr
    (hprod.of_injective ι hinj hequiv)

/-- **A finite topological ring has a MINIMUM open ideal**, so every
neighbourhood of `0` contains an OPEN IDEAL (PROVEN 2026-07-26,
elementary).

`⋂₀ {W | IsOpen W ∧ 0 ∈ W}`, the intersection of ALL open neighbourhoods
of `0`, is open because a finite type has only finitely many subsets
(`Set.toFinite`, then `Set.Finite.isOpen_sInter`); it is an ideal because
for fixed `a` the maps `x ↦ a + x` and `x ↦ a * x` are continuous, so
they pull an open neighbourhood of `a + 0` resp. of `0` back to one of
`0`; and it is contained in every open neighbourhood of `0` by
construction.

This is the ideal-theoretic substitute for "the topology is adic", which
a finite topological ring carries but is not PRESENTED with. It is what
lets `isHilbertFlatAt_of_fibreProduct` below — and, downstream, its
`F = ℚ` twin `Deformation.lean`'s `isFlatAt_of_fibreProduct` — convert two
open neighbourhoods of `0` in the factors of a fibre product into two open
IDEALS at which the flatness hypotheses can actually be evaluated.

HOME NOTE (2026-07-26). This lemma previously existed TWICE: as a
standalone in `Deformation.lean` and, because that module `public import`s
THIS one into the SAME namespace — so a matching top-level name here was a
"has already been declared" outage, not a duplicate-name warning — as a
local `have hshrink` inside `isHilbertFlatAt_of_fibreProduct`. The
duplication was resolved in the prescribed direction: the lemma was moved
UP to here, the local `have` was deleted, and the downstream standalone was
deleted so that `Deformation.lean` inherits this one through its
`public import`. Nothing about the statement is arithmetic — it is pure
topological-ring algebra over an arbitrary finite `R` — so this module,
being the upstream one, is its correct home. -/
lemma exists_isOpen_ideal_subset_of_finite {R : Type*} [CommRing R]
    [TopologicalSpace R] [IsTopologicalRing R] [Finite R]
    {U : Set R} (hU : IsOpen U) (h0 : (0 : R) ∈ U) :
    ∃ J : Ideal R, IsOpen (J : Set R) ∧ (J : Set R) ⊆ U := by
  classical
  have hshift : ∀ (a : R) (V : Set R), IsOpen V → a ∈ V →
      ∀ x ∈ ⋂₀ {W : Set R | IsOpen W ∧ (0 : R) ∈ W}, a + x ∈ V := by
    intro a V hV ha x hx
    exact hx ((fun y : R => a + y) ⁻¹' V)
      ⟨hV.preimage (continuous_const_add a), by simpa using ha⟩
  have hmul : ∀ (c : R) (V : Set R), IsOpen V → (0 : R) ∈ V →
      ∀ x ∈ ⋂₀ {W : Set R | IsOpen W ∧ (0 : R) ∈ W}, c * x ∈ V := by
    intro c V hV h0V x hx
    exact hx ((fun y : R => c * y) ⁻¹' V)
      ⟨hV.preimage (continuous_const_mul c), by simpa using h0V⟩
  refine ⟨{ carrier := ⋂₀ {W : Set R | IsOpen W ∧ (0 : R) ∈ W}
            add_mem' := ?_
            zero_mem' := ?_
            smul_mem' := ?_ }, ?_, ?_⟩
  · intro a b ha hb V hV
    exact hshift a V hV.1 (ha V hV) b hb
  · intro V hV
    exact hV.2
  · intro c x hx V hV
    simpa [smul_eq_mul] using hmul c V hV.1 hV.2 x hx
  · exact (Set.toFinite _).isOpen_sInter fun V hV => hV.1
  · exact fun x hx => hx U ⟨hU, h0⟩

open scoped TensorProduct in
/-- **Flatness at a place over `ℓ` glues along a fibre product** (PROVEN
2026-07-26 over exactly two Raynaud closure leaves — the sub-of-a-product
one immediately above, and the already-present quotient one
`hasFlatProlongationAt_of_pi_surjection_of_numberField`, consumed at
`n = 1`. Ramakrishna's half of Schlessinger's H1/H2 over `F`, and the
`F`-level twin of `Deformation.lean`'s `isFlatAt_of_fibreProduct`).

THIS DECLARATION WAS MOVED here from beside its sibling residue
`isHilbertTameAtTwo_of_fibreProduct` so that it could consume the existing
quotient leaf instead of restating it; see the section note above.

`B` is the fibre product `A₁ ×_{A₀} A₂` of finite local `ℤ_ℓ`-algebras
along a SURJECTION `f₂`, presented by its universal property rather than as
a construction: `hcart` says every compatible pair comes from `B`, and
`hemb` says `B` carries the induced topology and injects, so `B` really is
the fibre product AS A TOPOLOGICAL RING.

THE OBSTRUCTION AND HOW IT IS AVOIDED. `GaloisRep.IsFlatAt w` quantifies
over the OPEN IDEALS `I` of the coefficient ring and asks that
`ρ ⊗ (B ⧸ I)` be the geometric points of a finite flat group scheme over
`𝒪_{F_w}`. The open ideals of `B` are NOT in general pullbacks of open
ideals of `A₁` and `A₂`: the induced
`B ⧸ I → (A₁ ⧸ p₁(I)A₁) × (A₂ ⧸ p₂(I)A₂)` need not be injective, so `h₁`
and `h₂` cannot simply be evaluated at the ideal one is handed and the
prolongation of `ρ ⊗ B ⧸ I` cannot be cut out of the two given ones
directly. The historical route from here is Ramakrishna's, via Raynaud
UNIQUENESS of prolongations. It is NOT the route taken; the route is the
one `Deformation.lean`'s `isFlatAt_of_fibreProduct` takes at `F = ℚ`,
transcribed:

* `I` need not be a pullback, but it CONTAINS one. `hemb` gives an open
  `W ⊆ A₁ × A₂` with `(p₁, p₂)⁻¹ W = I`; shrink `W` to a box `U₁ × U₂`
  around `(0,0)` and shrink each `Uᵢ` to an OPEN IDEAL `Jᵢ` using that a
  FINITE topological ring has a minimum open ideal
  (`exists_isOpen_ideal_subset_of_finite`, immediately above; it was a local
  `have hshrink` here until 2026-07-26, when it was hoisted out of this
  proof and the rival copy in the DOWNSTREAM `Deformation.lean` was deleted
  in its favour — see its HOME NOTE). Then `K := p₁⁻¹ J₁ ⊓ p₂⁻¹ J₂` is an
  open ideal of `B` with
  `K ≤ I`.
* By CONSTRUCTION of `K` the pair map `B ⧸ K → (A₁ ⧸ J₁) × (A₂ ⧸ J₂)` IS
  injective, and tensoring with the standard frame — via
  `TensorProduct.piScalarRight` on both sides, which turns the comparison
  into the two entrywise identities `pᵢ(b) • φᵢ(c) = φᵢ(b • c)` — makes
  `(B ⧸ K) ⊗_B B²` an equivariant SUBOBJECT of
  `((A₁ ⧸ J₁) ⊗_{A₁} A₁²) × ((A₂ ⧸ J₂) ⊗_{A₂} A₂²)`, whose two factors
  are flat by `h₁` at `J₁` and `h₂` at `J₂`. Equivariance of the two
  components is exactly `framePushforward_apply_map`, which says
  `framePushforward pᵢ` acts entrywise on vectors in the image of `pᵢ`.
  `hasFlatProlongationAt_of_prod_injection_over_numberField` then gives
  flatness at `K`.
* `K ≤ I` makes `ρ ⊗ B ⧸ I` an equivariant QUOTIENT of `ρ ⊗ B ⧸ K`
  (`Submodule.mapQ` then `LinearMap.rTensor`), so
  `hasFlatProlongationAt_of_pi_surjection_of_numberField` at `n = 1`
  descends flatness from `K` to the given `I`.

FAITHFULNESS, AND SIX UNUSED HYPOTHESES — A FINDING, NOT AN OVERSIGHT.
The statement asks for the EXISTENCE of a prolongation over `𝒪_{F_w}`
produced from two given ones, not for a descent of existence from `𝒪^nr`,
so the `𝒪ᵥ` descent rule does not bite. Nothing here needs `F` totally
real or `F/ℚ` Galois.

The proof consumes only `hp₁`, `hp₂`, `hemb` (only its `IsInducing` half),
the finiteness of `A₁` and `A₂`, and `h₁`, `h₂`. It uses NEITHER the
cartesian property (`_hcart`, `_hcomm`, `_f₁`, `_f₂`, `_hf₂`) NOR
`_hw : ℓ ∈ w`, so all six are underscore-prefixed. This reproduces exactly
the audit recorded on the `ℚ`-level twin, and for the same reason: the
sub-of-a-product route never MATCHES two prolongations over `A₀` — it
prolongs ONE object, the subobject cut out inside a product, and existence
by schematic closure is unconditional over a DVR. The previous docstring's
claim that `hf₂` is spent "so that the quotient really is common" is
therefore REFUTED for this route (it was correct only for the uniqueness
route), as is the reading of `hw` as load-bearing: `hw` records WHERE the
clause is asserted, and the gluing itself is uniform in the place. The six
are kept in the signature because the sibling
`isHilbertTameAtTwo_of_fibreProduct` and the consumer
`isHilbertFibreProductClause` pass them POSITIONALLY, and because a
reviewer should be able to see what the Schlessinger cut supplied.

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
    (_f₁ : A₁ →+* A₀) (_f₂ : A₂ →+* A₀) (_hf₂ : Function.Surjective _f₂)
    (p₁ : B →+* A₁) (p₂ : B →+* A₂) (hp₁ : Continuous p₁) (hp₂ : Continuous p₂)
    (_hcomm : _f₁.comp p₁ = _f₂.comp p₂)
    (hemb : Topology.IsEmbedding fun b : B => (p₁ b, p₂ b))
    (_hcart : ∀ (a₁ : A₁) (a₂ : A₂), _f₁ a₁ = _f₂ a₂ →
      ∃ b : B, p₁ b = a₁ ∧ p₂ b = a₂)
    {ρ : FramedGaloisRep F B (Fin 2)}
    (w : HeightOneSpectrum (𝓞 F)) (_hw : ((ℓ : ℕ) : 𝓞 F) ∈ w.asIdeal)
    (h₁ : (framePushforward p₁ hp₁ ρ).IsFlatAt w)
    (h₂ : (framePushforward p₂ hp₂ ρ).IsFlatAt w) :
    ρ.IsFlatAt w := by
  classical
  constructor
  intro I hI
  -- STEP 1: open ideals of the two factors whose joint preimage sits inside `I`
  obtain ⟨W, hWopen, hWpre⟩ := hemb.toIsInducing.isOpen_iff.mp hI
  have h0W : ((0 : A₁), (0 : A₂)) ∈ W := by
    have h0I : (0 : B) ∈ (fun b : B => (p₁ b, p₂ b)) ⁻¹' W := by
      rw [hWpre]; exact I.zero_mem
    simpa using h0I
  obtain ⟨U₁, U₂, hU₁, hU₂, h0₁, h0₂, hUW⟩ := isOpen_prod_iff.mp hWopen 0 0 h0W
  obtain ⟨J₁, hJ₁open, hJ₁U⟩ := exists_isOpen_ideal_subset_of_finite hU₁ h0₁
  obtain ⟨J₂, hJ₂open, hJ₂U⟩ := exists_isOpen_ideal_subset_of_finite hU₂ h0₂
  set K : Ideal B := (J₁.comap p₁) ⊓ (J₂.comap p₂)
  have hKmem : ∀ b : B, b ∈ K ↔ (p₁ b ∈ J₁ ∧ p₂ b ∈ J₂) := fun b => Submodule.mem_inf
  have hKle : K ≤ I := by
    intro b hb
    have hb' := (hKmem b).mp hb
    have hmem : b ∈ (fun b : B => (p₁ b, p₂ b)) ⁻¹' W :=
      hUW ⟨hJ₁U hb'.1, hJ₂U hb'.2⟩
    rw [hWpre] at hmem
    exact hmem
  -- STEP 2: the two coefficient maps out of `B ⧸ K`
  have hφ₁mem : ∀ a ∈ K, ((Ideal.Quotient.mk J₁).comp p₁) a = 0 := fun a ha =>
    Ideal.Quotient.eq_zero_iff_mem.mpr ((hKmem a).mp ha).1
  have hφ₂mem : ∀ a ∈ K, ((Ideal.Quotient.mk J₂).comp p₂) a = 0 := fun a ha =>
    Ideal.Quotient.eq_zero_iff_mem.mpr ((hKmem a).mp ha).2
  let φ₁ : (B ⧸ K) →+* (A₁ ⧸ J₁) :=
    Ideal.Quotient.lift K ((Ideal.Quotient.mk J₁).comp p₁) hφ₁mem
  let φ₂ : (B ⧸ K) →+* (A₂ ⧸ J₂) :=
    Ideal.Quotient.lift K ((Ideal.Quotient.mk J₂).comp p₂) hφ₂mem
  have hφ₁mk : ∀ b : B, φ₁ (Ideal.Quotient.mk K b) = Ideal.Quotient.mk J₁ (p₁ b) :=
    fun _ => rfl
  have hφ₂mk : ∀ b : B, φ₂ (Ideal.Quotient.mk K b) = Ideal.Quotient.mk J₂ (p₂ b) :=
    fun _ => rfl
  have hpairinj : ∀ s t : B ⧸ K, φ₁ s = φ₁ t → φ₂ s = φ₂ t → s = t := by
    intro s t hs ht
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective s
    obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective t
    rw [hφ₁mk, hφ₁mk] at hs
    rw [hφ₂mk, hφ₂mk] at ht
    refine Ideal.Quotient.eq.mpr ((hKmem (b - c)).mpr ⟨?_, ?_⟩)
    · rw [map_sub]; exact Ideal.Quotient.eq.mp hs
    · rw [map_sub]; exact Ideal.Quotient.eq.mp ht
  -- STEP 3: the equivariant injection into the product of the two factors
  let F₁ : (B ⧸ K) →+ ((Fin 2 → B) →+ ((A₁ ⧸ J₁) ⊗[A₁] (Fin 2 → A₁))) :=
    { toFun := fun c =>
        { toFun := fun v => φ₁ c ⊗ₜ[A₁] (fun j => p₁ (v j))
          map_zero' := by
            have hz : (fun j => p₁ ((0 : Fin 2 → B) j)) = (0 : Fin 2 → A₁) := by
              funext j; simp
            rw [hz, TensorProduct.tmul_zero]
          map_add' := fun v u => by
            have hv : (fun j => p₁ ((v + u) j))
                = (fun j => p₁ (v j)) + (fun j => p₁ (u j)) := by
              funext j; simp
            rw [hv, TensorProduct.tmul_add] }
      map_zero' := by ext v; simp
      map_add' := fun c d => by ext v; simp [TensorProduct.add_tmul] }
  let F₂ : (B ⧸ K) →+ ((Fin 2 → B) →+ ((A₂ ⧸ J₂) ⊗[A₂] (Fin 2 → A₂))) :=
    { toFun := fun c =>
        { toFun := fun v => φ₂ c ⊗ₜ[A₂] (fun j => p₂ (v j))
          map_zero' := by
            have hz : (fun j => p₂ ((0 : Fin 2 → B) j)) = (0 : Fin 2 → A₂) := by
              funext j; simp
            rw [hz, TensorProduct.tmul_zero]
          map_add' := fun v u => by
            have hv : (fun j => p₂ ((v + u) j))
                = (fun j => p₂ (v j)) + (fun j => p₂ (u j)) := by
              funext j; simp
            rw [hv, TensorProduct.tmul_add] }
      map_zero' := by ext v; simp
      map_add' := fun c d => by ext v; simp [TensorProduct.add_tmul] }
  have hbal₁ : ∀ (b : B) (c : B ⧸ K) (v : Fin 2 → B),
      F₁ (b • c) v = F₁ c (b • v) := by
    intro b c v
    show φ₁ (b • c) ⊗ₜ[A₁] (fun j => p₁ (v j))
      = φ₁ c ⊗ₜ[A₁] (fun j => p₁ ((b • v) j))
    have hrhs : (fun j => p₁ ((b • v) j)) = p₁ b • (fun j => p₁ (v j)) := by
      funext j
      show p₁ (b * v j) = p₁ b * p₁ (v j)
      exact map_mul _ _ _
    have hlhs : φ₁ (b • c) = p₁ b • φ₁ c := by
      rw [Algebra.smul_def, Algebra.smul_def, map_mul]
      rfl
    rw [hrhs, hlhs, ← TensorProduct.smul_tmul]
  have hbal₂ : ∀ (b : B) (c : B ⧸ K) (v : Fin 2 → B),
      F₂ (b • c) v = F₂ c (b • v) := by
    intro b c v
    show φ₂ (b • c) ⊗ₜ[A₂] (fun j => p₂ (v j))
      = φ₂ c ⊗ₜ[A₂] (fun j => p₂ ((b • v) j))
    have hrhs : (fun j => p₂ ((b • v) j)) = p₂ b • (fun j => p₂ (v j)) := by
      funext j
      show p₂ (b * v j) = p₂ b * p₂ (v j)
      exact map_mul _ _ _
    have hlhs : φ₂ (b • c) = p₂ b • φ₂ c := by
      rw [Algebra.smul_def, Algebra.smul_def, map_mul]
      rfl
    rw [hrhs, hlhs, ← TensorProduct.smul_tmul]
  let ι₁ : ((B ⧸ K) ⊗[B] (Fin 2 → B)) →+ ((A₁ ⧸ J₁) ⊗[A₁] (Fin 2 → A₁)) :=
    TensorProduct.liftAddHom F₁ hbal₁
  let ι₂ : ((B ⧸ K) ⊗[B] (Fin 2 → B)) →+ ((A₂ ⧸ J₂) ⊗[A₂] (Fin 2 → A₂)) :=
    TensorProduct.liftAddHom F₂ hbal₂
  have hι₁tmul : ∀ (c : B ⧸ K) (v : Fin 2 → B),
      ι₁ (c ⊗ₜ[B] v) = φ₁ c ⊗ₜ[A₁] (fun j => p₁ (v j)) := fun _ _ => rfl
  have hι₂tmul : ∀ (c : B ⧸ K) (v : Fin 2 → B),
      ι₂ (c ⊗ₜ[B] v) = φ₂ c ⊗ₜ[A₂] (fun j => p₂ (v j)) := fun _ _ => rfl
  -- injectivity, through the free-module identification
  have hcomp₁ : ∀ (x : (B ⧸ K) ⊗[B] (Fin 2 → B)) (j : Fin 2),
      TensorProduct.piScalarRight A₁ (A₁ ⧸ J₁) (A₁ ⧸ J₁) (Fin 2) (ι₁ x) j
        = φ₁ (TensorProduct.piScalarRight B (B ⧸ K) (B ⧸ K) (Fin 2) x j) := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => intro j; simp
    | add a b ha hb => intro j; simp only [map_add, Pi.add_apply, ha j, hb j, map_add]
    | tmul c v =>
      intro j
      rw [hι₁tmul, TensorProduct.piScalarRight_apply,
        TensorProduct.piScalarRightHom_tmul, TensorProduct.piScalarRight_apply,
        TensorProduct.piScalarRightHom_tmul]
      show p₁ (v j) • φ₁ c = φ₁ (v j • c)
      rw [Algebra.smul_def, Algebra.smul_def, map_mul]
      rfl
  have hcomp₂ : ∀ (x : (B ⧸ K) ⊗[B] (Fin 2 → B)) (j : Fin 2),
      TensorProduct.piScalarRight A₂ (A₂ ⧸ J₂) (A₂ ⧸ J₂) (Fin 2) (ι₂ x) j
        = φ₂ (TensorProduct.piScalarRight B (B ⧸ K) (B ⧸ K) (Fin 2) x j) := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => intro j; simp
    | add a b ha hb => intro j; simp only [map_add, Pi.add_apply, ha j, hb j, map_add]
    | tmul c v =>
      intro j
      rw [hι₂tmul, TensorProduct.piScalarRight_apply,
        TensorProduct.piScalarRightHom_tmul, TensorProduct.piScalarRight_apply,
        TensorProduct.piScalarRightHom_tmul]
      show p₂ (v j) • φ₂ c = φ₂ (v j • c)
      rw [Algebra.smul_def, Algebra.smul_def, map_mul]
      rfl
  have hinj : Function.Injective (ι₁.prod ι₂) := by
    intro x y hxy
    have hx1 : ι₁ x = ι₁ y := congrArg Prod.fst hxy
    have hx2 : ι₂ x = ι₂ y := congrArg Prod.snd hxy
    apply (TensorProduct.piScalarRight B (B ⧸ K) (B ⧸ K) (Fin 2)).injective
    funext j
    refine hpairinj _ _ ?_ ?_
    · rw [← hcomp₁ x j, ← hcomp₁ y j, hx1]
    · rw [← hcomp₂ x j, ← hcomp₂ y j, hx2]
  -- equivariance of the two components
  have hkey₁ : ∀ (g : Γ F) (x : (B ⧸ K) ⊗[B] (Fin 2 → B)),
      ι₁ ((ρ.baseChange (B ⧸ K)) g x)
        = ((framePushforward p₁ hp₁ ρ).baseChange (A₁ ⧸ J₁)) g (ι₁ x) := by
    intro g x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add a b ha hb => simp only [map_add, ha, hb]
    | tmul c v =>
      rw [GaloisRep.baseChange_tmul, hι₁tmul, hι₁tmul, GaloisRep.baseChange_tmul]
      congr 1
      funext i
      exact (framePushforward_apply_map p₁ hp₁ ρ g v i).symm
  have hkey₂ : ∀ (g : Γ F) (x : (B ⧸ K) ⊗[B] (Fin 2 → B)),
      ι₂ ((ρ.baseChange (B ⧸ K)) g x)
        = ((framePushforward p₂ hp₂ ρ).baseChange (A₂ ⧸ J₂)) g (ι₂ x) := by
    intro g x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add a b ha hb => simp only [map_add, ha, hb]
    | tmul c v =>
      rw [GaloisRep.baseChange_tmul, hι₂tmul, hι₂tmul, GaloisRep.baseChange_tmul]
      congr 1
      funext i
      exact (framePushforward_apply_map p₂ hp₂ ρ g v i).symm
  -- STEP 4: the Raynaud sub-of-a-product leaf, applied at `K`
  let ι : (((ρ.baseChange (B ⧸ K)).toLocal w).Space) →+
      ((((framePushforward p₁ hp₁ ρ).baseChange (A₁ ⧸ J₁)).toLocal w).Space ×
        (((framePushforward p₂ hp₂ ρ).baseChange (A₂ ⧸ J₂)).toLocal w).Space) :=
    ι₁.prod ι₂
  have hflatK : (ρ.baseChange (B ⧸ K)).HasFlatProlongationAt w := by
    refine hasFlatProlongationAt_of_prod_injection_over_numberField w
      (h₁.cond J₁ hJ₁open) (h₂.cond J₂ hJ₂open) ι hinj ?_
    intro g x
    show (ι₁.prod ι₂) (((ρ.baseChange (B ⧸ K)).toLocal w) g x)
      = ((((framePushforward p₁ hp₁ ρ).baseChange (A₁ ⧸ J₁)).toLocal w) g (ι₁ x),
         (((framePushforward p₂ hp₂ ρ).baseChange (A₂ ⧸ J₂)).toLocal w) g (ι₂ x))
    rw [GaloisRep.toLocal_apply, GaloisRep.toLocal_apply, GaloisRep.toLocal_apply]
    exact Prod.ext (hkey₁ _ x) (hkey₂ _ x)
  -- STEP 5: descend from `B ⧸ K` to the given open ideal `I`
  let fKI : (B ⧸ K) →ₗ[B] (B ⧸ I) := Submodule.mapQ K I LinearMap.id hKle
  have hfKIsurj : Function.Surjective fKI := by
    intro z
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective z
    exact ⟨Ideal.Quotient.mk K b, rfl⟩
  let π₀ : ((B ⧸ K) ⊗[B] (Fin 2 → B)) →ₗ[B] ((B ⧸ I) ⊗[B] (Fin 2 → B)) :=
    LinearMap.rTensor (Fin 2 → B) fKI
  have hπ₀surj : Function.Surjective π₀ := LinearMap.rTensor_surjective _ hfKIsurj
  have hπ₀equiv : ∀ (g : Γ F) (x : (B ⧸ K) ⊗[B] (Fin 2 → B)),
      π₀ ((ρ.baseChange (B ⧸ K)) g x) = (ρ.baseChange (B ⧸ I)) g (π₀ x) := by
    intro g x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add a b ha hb => simp only [map_add, ha, hb]
    | tmul c v =>
      rw [GaloisRep.baseChange_tmul]
      show fKI c ⊗ₜ[B] (ρ g v) = (ρ.baseChange (B ⧸ I)) g (fKI c ⊗ₜ[B] v)
      rw [GaloisRep.baseChange_tmul]
  let π : (Fin 1 → ((ρ.baseChange (B ⧸ K)).toLocal w).Space) →+
      (((ρ.baseChange (B ⧸ I)).toLocal w).Space) :=
    { toFun := fun x => π₀ (x 0)
      map_zero' := map_zero π₀
      map_add' := fun x y => map_add π₀ (x 0) (y 0) }
  refine hasFlatProlongationAt_of_pi_surjection_of_numberField w 1 hflatK π ?_ ?_
  · intro z
    obtain ⟨y, hy⟩ := hπ₀surj z
    exact ⟨fun _ => y, hy⟩
  · intro g x
    show π₀ (((ρ.baseChange (B ⧸ K)).toLocal w) g (x 0))
      = ((ρ.baseChange (B ⧸ I)).toLocal w) g (π₀ (x 0))
    rw [GaloisRep.toLocal_apply, GaloisRep.toLocal_apply]
    exact hπ₀equiv _ (x 0)

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
    (F : Type u) [Field F] [NumberField F]
    (hw2 : ∀ w : HeightOneSpectrum (𝓞 F), ((2 : ℕ) : 𝓞 F) ∈ w.asIdeal →
      ¬ ((ℓ : ℤ) ∣ ((Nat.card (𝓞 F ⧸ w.asIdeal) : ℤ) ^ 2 - 1))) :
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
      hemb hcart hdet w hw (hw2 w hw) (h₁.isTameAtTwo w hw) (h₂.isTameAtTwo w hw)

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
* ALL the arithmetic is isolated in Hermite's theorem for `F`,
  `finite_setOf_intermediateField_hilbertInertiaAt_le` — finitely many
  finite Galois extensions of `F` of bounded degree unramified outside
  the places over `2ℓ` — which is itself PROVEN (2026-07-26) over
  exactly TWO arithmetic leaves:
  `discr_factorization_le_of_finrank_le`, the base-free bound on the
  exponent of a rational prime in `|d_L|` in terms of `[L : ℚ]` alone
  (`Modularity/Patching.lean` proves the same statement with the ambient
  pinned; the hoist has only to move that proof), and
  `not_dvd_discr_of_hilbertInertiaTrivialAt`, the `F`-level
  inertia-to-discriminant transport (the `F`-level twin of
  `MazurTorsion.lean`'s `isUnramifiedAt_of_inertia_le_fixingSubgroup`,
  followed by ramification in the tower `ℚ ⊆ F ⊆ K`).
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

/-- **The discriminant exponent from the degree alone** (LEAF — the
first of the two arithmetic inputs of Hermite–Minkowski over `F`): for a
number field `L` with `[L : ℚ] ≤ n` and ANY natural number `q`, the
exponent of `q` in `|d_L|` is at most `(n + 1)·n`.

Stated BASE-FREE — over an abstract number field `L`, with no ambient
algebraic closure and with a bound uniform in `q` — because that is the
form the eventual module split needs.
`HardlyRamified/HermiteMinkowski.lean`'s
`exists_discr_factorization_le_of_finrank_le` is the SAME statement with
the ambient pinned to `IntermediateField ℚ ℚᵃˡᵍ` and the (identical)
bound `(n + 1)·n` hidden behind an existential; nothing in its proof uses
the ambient. (It lived in `Modularity/Patching.lean` when this docstring
was first written; the hoist is what made the proof below available.)

**ROUTE AUDIT SUPERSEDED 2026-07-26 — THE HOIST HAS HAPPENED AND THIS IS
NOW PROVEN.** The previous version of this docstring recorded the route as
unavailable, for three reasons that were all correct WHEN WRITTEN and are
all now stale. What changed: `differentIdeal_exponent_le` and its wild
chain no longer live in `Modularity/Patching.lean` at all. They were
hoisted into `HardlyRamified/HermiteMinkowski.lean`, a module that is
upstream of both `Patching.lean` and this one — which is exactly the
repair the old audit named as "the hoist that WOULD retire this leaf
properly". Point by point:

* **The circularity objection is void.** The route no longer goes through
  `Modularity/Patching.lean`. `HermiteMinkowski.lean`'s 118-module project
  closure does not contain this module (verified by closure computation),
  so the import is acyclic.
* **The "does not stand alone" objection is void.** Both inputs are
  imported, not copied: `differentIdeal_exponent_le` (the Serre bound
  `d_Q ≤ e − 1 + e·v_q(e)`) from `HermiteMinkowski.lean`, and
  `ModThree.lean`'s tame-plus-wild assembly
  `IsHardlyRamified.discr_factorization_le_of_forall_differentIdeal_pow_dvd`
  re-exported through it. Nothing is duplicated here.
* **The cone-growth objection is void, and this is the load-bearing
  correction.** It assumed the growth would be paid by the downstream
  tree. It is not: this module has exactly TWO project consumers,
  `Deformation.lean` and `Modularity/Patching.lean`, and BOTH already
  import `HermiteMinkowski.lean` directly. The import therefore adds ZERO
  modules to any consumer's cone. Only this module's own rebuild trigger
  widens.

**Both inputs are already stated base-free**, over an abstract
`(K : Type*) [Field K] [NumberField K]` — so the old docstring's claim
that "nothing in its proof uses the ambient" is literally true of the
Lean statements, and the port below is the `IntermediateField ℚ ℚᵃˡᵍ`
proof of `HermiteMinkowski.lean`'s `exists_discr_factorization_le_of_finrank_le`
with the ambient binder deleted and the `hq : q.Prime` hypothesis moved
inside as a case split (for non-prime `q` the left-hand side is `0`,
since `Nat.factorization` is supported on primes).

**AXIOM STATUS, stated precisely because it is not a clean close.** This
declaration is no longer a DIRECT sorry, but it is still TRANSITIVELY
sorried: `#print axioms` reports `sorryAx`. The taint has exactly one
source, traced by auditing each input separately —
`differentIdeal_exponent_le_wild_of_residueDegreeGtOne`
(`HermiteMinkowski.lean`, the single open leaf of that cluster).
`ModThree.lean`'s assembly is CLEAN
(`[propext, Classical.choice, Quot.sound]`). So what this change buys is
not a closed cone but the removal of a DUPLICATED ~1100-line obligation:
the bound is now charged once, to the sharp local leaf that already owns
it, instead of twice.

MATHEMATICAL CONTENT (Serre, *Corps Locaux* III §6 Prop. 13, and the norm
bookkeeping). For a prime `Q` of `𝓞 L` over `q` with ramification index
`e` the different exponent satisfies `d_Q ≤ e − 1 + e·v_q(e)`; here
`e ≤ [L : ℚ] ≤ n` (`Ideal.ramificationIdx_le_finrank`, through the
fundamental identity) and `v_q(e) < e ≤ n` (`Nat.factorization_lt`), so
`d_Q ≤ (n + 1)·e`. Pushing this through
`N(𝔡_{L/ℚ}) = |d_L|` and `Σ_Q e_Q·f_Q = [L : ℚ]`
(`ModThree.lean`'s PROVEN
`discr_factorization_le_of_forall_differentIdeal_pow_dvd`, which is
already stated base-free in exactly this shape) gives
`v_q(|d_L|) ≤ (n + 1)·[L : ℚ] ≤ (n + 1)·n`. For `q` not prime, or `q`
unramified in `L`, the left-hand side is `0`.

BOTH-WAYS AUDIT. A plain universally quantified inequality about number
fields: classically true outright as cited, with no representation
theory and no vacuity — for `n = 0` the hypothesis `[L : ℚ] ≤ 0` is
unsatisfiable, but for every `n ≥ 1` there are number fields meeting it
and the inequality is the real content. NOT vacuous. -/
theorem discr_factorization_le_of_finrank_le (n : ℕ) (L : Type*) [Field L]
    [NumberField L] (hrank : Module.finrank ℚ L ≤ n) (q : ℕ) :
    (NumberField.discr L).natAbs.factorization q ≤ (n + 1) * n := by
  by_cases hq : q.Prime
  · have hqZ : Prime ((q : ℕ) : ℤ) := Nat.prime_iff_prime_int.mp hq
    have hspan0 : (Ideal.span {((q : ℕ) : ℤ)} : Ideal ℤ) ≠ ⊥ := by
      simp only [Ne, Ideal.span_singleton_eq_bot]
      exact_mod_cast hq.ne_zero
    haveI hspanMax : (Ideal.span {((q : ℕ) : ℤ)} : Ideal ℤ).IsMaximal :=
      (((Ideal.span_singleton_prime (by exact_mod_cast hq.ne_zero)).mpr
        hqZ).isMaximal hspan0)
    -- the uniform per-prime different-exponent bound `d_Q ≤ (n + 1)·e_Q`
    have key : ∀ Q : Ideal (NumberField.RingOfIntegers L), Q.IsPrime →
        ((q : NumberField.RingOfIntegers L) ∈ Q) → ∀ d : ℕ,
        Q ^ d ∣ differentIdeal ℤ (NumberField.RingOfIntegers L) →
        1 * d ≤ (n + 1) * Ideal.ramificationIdx' (Ideal.span {(q : ℤ)}) Q := by
      intro Q hQ hmem d hd
      haveI := hQ
      haveI hlies : Q.LiesOver (Ideal.span {((q : ℕ) : ℤ)}) :=
        (Ideal.liesOver_span_iff hQ.ne_top hqZ).mpr (by exact_mod_cast hmem)
      have he0 : Ideal.ramificationIdx' (Ideal.span {((q : ℕ) : ℤ)}) Q ≠ 0 :=
        Ideal.IsDedekindDomain.ramificationIdx'_ne_zero_of_liesOver Q hspan0
      have hen : Ideal.ramificationIdx' (Ideal.span {((q : ℕ) : ℤ)}) Q ≤ n :=
        le_trans (Ideal.ramificationIdx_le_finrank
          (S := NumberField.RingOfIntegers L) (K := ℚ) (L := L) Q) hrank
      have hv : (Ideal.ramificationIdx' (Ideal.span {((q : ℕ) : ℤ)}) Q).factorization q
          ≤ n := le_of_lt (lt_of_lt_of_le (Nat.factorization_lt q he0) hen)
      have hser := differentIdeal_exponent_le L q hq Q hQ hmem d hd
      calc 1 * d = d := one_mul d
        _ ≤ Ideal.ramificationIdx' (Ideal.span {(q : ℤ)}) Q - 1 +
            Ideal.ramificationIdx' (Ideal.span {(q : ℤ)}) Q *
              (Ideal.ramificationIdx' (Ideal.span {(q : ℤ)}) Q).factorization q := hser
        _ ≤ Ideal.ramificationIdx' (Ideal.span {(q : ℤ)}) Q +
            Ideal.ramificationIdx' (Ideal.span {(q : ℤ)}) Q * n :=
          Nat.add_le_add (Nat.sub_le _ _) (Nat.mul_le_mul_left _ hv)
        _ = (n + 1) * Ideal.ramificationIdx' (Ideal.span {(q : ℤ)}) Q := by ring
    have hmain := IsHardlyRamified.discr_factorization_le_of_forall_differentIdeal_pow_dvd
      L q hq 1 (n + 1) key
    calc (NumberField.discr L).natAbs.factorization q
        = 1 * (NumberField.discr L).natAbs.factorization q := (one_mul _).symm
      _ ≤ (n + 1) * Module.finrank ℚ L := hmain
      _ ≤ (n + 1) * n := Nat.mul_le_mul_left _ hrank
  · -- `Nat.factorization` is supported on primes, so the bound is trivial
    rw [Nat.factorization_eq_zero_of_not_prime _ hq]
    exact Nat.zero_le _

/-- **The embedding prime over `w` has trivial ideal-inertia** (PROVEN
2026-07-26; step (a) of the two-step proof of
`isUnramifiedAt_of_hilbertInertiaTrivialAt` below, and the `F`-level twin of
`FreyCurve/MazurTorsion.lean`'s
`exists_prime_over_inertia_eq_bot_of_le_fixingSubgroup`, which is written
over `ℚ` and over `hq.toHeightOneSpectrumRingOfIntegersRat` and is NOT
importable here — `MazurTorsion.lean` would grow this module's cone from 32
to 91 modules and `Deformation.lean` re-exports this one).

ROUTE, and it is the ℚ-level one transported wholesale. Choose the
embedding `ι = AlgebraicClosure.map (algebraMap F F_w)` and set
`M = F_w(ι(K)) ⊆ (F_w)ᵃˡᵍ`, a FINITE extension of `F_w` because `K/F` is
finitely generated by algebraic elements. The inertia hypothesis places `M`
inside `IntermediateField.fixedField (localInertiaGroup w)`, so the LOCAL
node `maximalIdeal_map_eq_of_le_fixedField_localInertiaGroup`
(`Deformations/RepresentationTheory/LocalInertiaFixedField.lean`, Neukirch
II.9.11) gives `𝔪(𝒪_w) · 𝒪_M = 𝔪(𝒪_M)`. Pulling `𝔪(𝒪_M)` back along the
induced `φ : 𝓞 K → 𝒪_M` produces `Q₀`, and:

* `Q₀` lies over `w` because `φ` extends the structure map of `𝒪_w`
  (`hcomm` in the proof) and the contraction of `𝔪(𝒪_M)` to `𝒪_w` is
  `𝔪(𝒪_w)`, whose contraction to `𝓞 F` is `w.asIdeal` — that last step is
  mathlib-adjacent, supplied by this project's instance
  `(v.completionIdeal K).LiesOver v.asIdeal`.
* `e(Q₀ | w) = 1`: otherwise `w.asIdeal · 𝓞 K ≤ Q₀ ^ 2`
  (`Ideal.ramificationIdx'_ne_one_iff`), so a uniformizer `π ∈ 𝓞 F` of `w`
  has `φ π ∈ 𝔪(𝒪_M) ^ 2 = (φ π) ^ 2`; cancelling one factor (`φ π ≠ 0`)
  makes `φ π` a unit inside the proper ideal `𝔪(𝒪_M)`.
* `|I(Q₀)| = e(Q₀ | w) = 1` by `Ideal.card_inertia_eq_ramificationIdxIn`,
  applicable because the residue field of `w` is FINITE, hence perfect.

WHERE THE `ℚ`-LEVEL PROOF NEEDED A CHANGE. Over `ℚ` the rational prime `q`
is itself a generator of `𝔪(ℤ_q)` — that is absolute unramifiedness of the
base, and it is what
`Fermat/FLT/Mathlib/.../Ideal/Lemmas.lean`'s
`maximalIdeal_adicCompletionIntegers_eq_span` records. Over `F` there is no
such rational generator, so the generator is produced by
`IsDedekindDomain.HeightOneSpectrum.intValuation_exists_uniformizer` and fed
to `adicCompletion.maximalIdeal_eq_span_uniformizer` directly; the membership
`π ∈ w.asIdeal` is `intValuation_lt_one_iff_mem`. Everything else is the
`ℚ` argument with `ℤ ↦ 𝓞 F`, `span {q} ↦ w.asIdeal` and `ℚ_q ↦ F_w`. -/
theorem exists_prime_over_inertia_eq_bot_of_hilbertInertiaTrivialAt
    (F : Type u) [Field F] [NumberField F]
    (K : IntermediateField F (AlgebraicClosure F))
    [FiniteDimensional F K] [IsGalois F K] [NumberField ↥K]
    (w : HeightOneSpectrum (𝓞 F))
    (hinert : HilbertInertiaTrivialAt w K.fixingSubgroup) :
    ∃ (Q₀ : Ideal (𝓞 ↥K)) (_ : Q₀.IsPrime) (_ : Q₀.LiesOver w.asIdeal),
      Q₀.inertia (↥K ≃ₐ[F] ↥K) = ⊥ := by
  classical
  set f : F →+* w.adicCompletion F := algebraMap F _ with hf
  set ι : AlgebraicClosure F →+* AlgebraicClosure (w.adicCompletion F) :=
    AlgebraicClosure.map f with hι
  -- a finite generating set for `K/F`
  obtain ⟨s, hs⟩ := K.fg_iff_finiteType.mpr (inferInstanceAs (Algebra.FiniteType F K))
  have hKgen : K = IntermediateField.adjoin F ↑s :=
    IntermediateField.eq_adjoin_of_eq_algebra_adjoin _ _ _ hs.symm
  -- the image field `M := F_w(ι(K))`
  set M : IntermediateField (w.adicCompletion F)
      (AlgebraicClosure (w.adicCompletion F)) :=
    IntermediateField.adjoin _ (ι '' ↑s) with hM
  have hsub : ∀ x ∈ K, ι x ∈ M := by
    intro x hx
    rw [hKgen] at hx
    induction hx using IntermediateField.adjoin_induction with
    | mem y hy => exact IntermediateField.subset_adjoin _ _ ⟨y, hy, rfl⟩
    | algebraMap c =>
        rw [hι, AlgebraicClosure.map_algebraMap]
        exact M.algebraMap_mem _
    | add x y hx hy ihx ihy => rw [map_add]; exact add_mem ihx ihy
    | inv x hx ihx => rw [map_inv₀]; exact inv_mem ihx
    | mul x y hx hy ihx ihy => rw [map_mul]; exact mul_mem ihx ihy
  haveI hfdM : FiniteDimensional (w.adicCompletion F) M := by
    haveI : Finite (ι '' (↑s : Set (AlgebraicClosure F))) :=
      (s.finite_toSet.image ι).to_subtype
    exact IntermediateField.finiteDimensional_adjoin
      fun x _ => Algebra.IsIntegral.isIntegral x
  have hMfix : M ≤ IntermediateField.fixedField (localInertiaGroup w) := by
    rw [hM, IntermediateField.adjoin_le_iff]
    rintro _ ⟨y, hy, rfl⟩
    rw [SetLike.mem_coe, IntermediateField.mem_fixedField_iff]
    intro σ hσ
    have hmem : (Field.absoluteGaloisGroup.map f) σ ∈ K.fixingSubgroup := hinert σ hσ
    have hfixy : (Field.absoluteGaloisGroup.map f σ) y = y :=
      (IntermediateField.mem_fixingSubgroup_iff K
        ((Field.absoluteGaloisGroup.map f) σ)).mp hmem y
        (hKgen ▸ IntermediateField.subset_adjoin _ _ hy)
    calc σ (ι y) = ι ((Field.absoluteGaloisGroup.map f σ) y) :=
          (Field.absoluteGaloisGroup.lift_map f σ y).symm
      _ = ι y := by rw [hfixy]
  -- the local node: `𝔪(𝒪_w)` generates `𝔪(𝒪_M)`
  have hmax := maximalIdeal_map_eq_of_le_fixedField_localInertiaGroup w M hMfix
  -- the ring homomorphism `ψ : K → M` induced by `ι`
  set ψ : ↥K →+* ↥M :=
    { toFun := fun y => ⟨ι (y : AlgebraicClosure F), hsub _ y.2⟩
      map_one' := by apply Subtype.ext; simp
      map_mul' := fun a b => by apply Subtype.ext; simp
      map_zero' := by apply Subtype.ext; simp
      map_add' := fun a b => by apply Subtype.ext; simp } with hψ
  have hψint : ∀ x : 𝓞 ↥K,
      ψ (algebraMap (𝓞 ↥K) ↥K x) ∈
        integralClosure (w.adicCompletionIntegers F) ↥M := by
    intro x
    have h1 : IsIntegral ℤ (algebraMap (𝓞 ↥K) ↥K x) :=
      NumberField.RingOfIntegers.isIntegral_coe x
    let ψℤ : ↥K →ₐ[ℤ] ↥M :=
      { toRingHom := ψ
        commutes' := fun n => by
          rw [RingHom.eq_intCast' (algebraMap ℤ ↥K),
            RingHom.eq_intCast' (algebraMap ℤ ↥M)]
          exact map_intCast ψ n }
    have h2 : IsIntegral ℤ (ψ (algebraMap (𝓞 ↥K) ↥K x)) := h1.map ψℤ
    obtain ⟨p, hp, hpeval⟩ := h2
    refine ⟨p.map (Int.castRingHom (w.adicCompletionIntegers F)), hp.map _, ?_⟩
    rw [Polynomial.eval₂_map, Subsingleton.elim
      ((algebraMap (w.adicCompletionIntegers F) ↥M).comp
        (Int.castRingHom (w.adicCompletionIntegers F))) (algebraMap ℤ ↥M)]
    exact hpeval
  set φ : 𝓞 ↥K →+* IntegralClosure (w.adicCompletionIntegers F) ↥M :=
    (ψ.comp (algebraMap (𝓞 ↥K) ↥K)).codRestrict
      (integralClosure (w.adicCompletionIntegers F) ↥M) hψint with hφ
  -- `φ` extends the structure map of `𝒪_w`
  have hcomm : ∀ x : 𝓞 F, φ (algebraMap (𝓞 F) (𝓞 ↥K) x) =
      algebraMap (w.adicCompletionIntegers F)
        (IntegralClosure (w.adicCompletionIntegers F) ↥M)
        (algebraMap (𝓞 F) (w.adicCompletionIntegers F) x) := by
    intro x
    apply Subtype.ext
    apply Subtype.ext
    show ι ((algebraMap (𝓞 ↥K) ↥K (algebraMap (𝓞 F) (𝓞 ↥K) x) :
      AlgebraicClosure F)) = _
    rw [show ((algebraMap (𝓞 ↥K) ↥K (algebraMap (𝓞 F) (𝓞 ↥K) x) : ↥K) :
        AlgebraicClosure F) =
        algebraMap F (AlgebraicClosure F) (algebraMap (𝓞 F) F x) from by
      rw [← IsScalarTower.algebraMap_apply (𝓞 F) (𝓞 ↥K) ↥K,
        IsScalarTower.algebraMap_apply (𝓞 F) F ↥K]
      rfl,
      hι, AlgebraicClosure.map_algebraMap, hf]
    show algebraMap (w.adicCompletion F) (AlgebraicClosure (w.adicCompletion F))
        (algebraMap F (w.adicCompletion F) (algebraMap (𝓞 F) F x)) =
      algebraMap (w.adicCompletion F) (AlgebraicClosure (w.adicCompletion F))
        ((algebraMap (𝓞 F) (w.adicCompletionIntegers F) x : w.adicCompletion F))
    rw [IsDedekindDomain.HeightOneSpectrum.algebraMap_adicCompletionIntegers_apply]
    rfl
  -- the embedding prime `Q₀`
  haveI hmaxprime : (IsLocalRing.maximalIdeal
      (IntegralClosure (w.adicCompletionIntegers F) ↥M)).IsPrime :=
    (IsLocalRing.maximalIdeal.isMaximal _).isPrime
  set Q₀ : Ideal (𝓞 ↥K) := Ideal.comap φ
    (IsLocalRing.maximalIdeal (IntegralClosure (w.adicCompletionIntegers F) ↥M))
    with hQ₀def
  haveI hQ₀p : Q₀.IsPrime := Ideal.IsPrime.comap φ
  -- the contraction of `𝔪(𝒪_M)` to `𝒪_w` is `𝔪(𝒪_w)`
  have hcomapIC : Ideal.comap (algebraMap (w.adicCompletionIntegers F)
      (IntegralClosure (w.adicCompletionIntegers F) ↥M))
      (IsLocalRing.maximalIdeal (IntegralClosure (w.adicCompletionIntegers F) ↥M)) =
      IsLocalRing.maximalIdeal (w.adicCompletionIntegers F) := by
    refine ((IsLocalRing.maximalIdeal.isMaximal
      (w.adicCompletionIntegers F)).eq_of_le ?_ ?_).symm
    · intro htop
      have h1 := (Ideal.eq_top_iff_one _).mp htop
      rw [Ideal.mem_comap, map_one] at h1
      exact (IsLocalRing.maximalIdeal.isMaximal _).ne_top ((Ideal.eq_top_iff_one _).mpr h1)
    · intro y hy
      rw [Ideal.mem_comap, ← hmax]
      exact Ideal.mem_map_of_mem _ hy
  -- so `Q₀` lies over `w`
  have hunder : Ideal.comap (algebraMap (𝓞 F) (𝓞 ↥K)) Q₀ = w.asIdeal := by
    have hlo : Ideal.comap (algebraMap (𝓞 F) (w.adicCompletionIntegers F))
        (IsLocalRing.maximalIdeal (w.adicCompletionIntegers F)) = w.asIdeal := by
      have := (Ideal.LiesOver.over (A := 𝓞 F) (p := w.asIdeal)
        (P := IsDedekindDomain.HeightOneSpectrum.completionIdeal F w)).symm
      rwa [Ideal.under_def] at this
    ext y
    rw [Ideal.mem_comap, hQ₀def, Ideal.mem_comap, hcomm y, ← Ideal.mem_comap, hcomapIC,
      ← Ideal.mem_comap, hlo]
  haveI hQ₀lo : Q₀.LiesOver w.asIdeal := ⟨hunder.symm⟩
  refine ⟨Q₀, hQ₀p, hQ₀lo, ?_⟩
  -- a uniformizer of `w` inside `𝓞 F`
  obtain ⟨π, hπ⟩ := w.intValuation_exists_uniformizer
  have hπmem : π ∈ w.asIdeal := by
    rw [← IsDedekindDomain.HeightOneSpectrum.intValuation_lt_one_iff_mem, hπ]
    simpa using (WithZero.exp_lt_exp (a := (-1 : ℤ)) (b := 0)).mpr (by norm_num)
  have hπw : Valued.v ((algebraMap (𝓞 F) (w.adicCompletionIntegers F) π :
      w.adicCompletion F)) = Multiplicative.ofAdd (-1 : ℤ) := by
    have h := (IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation
        (v := w) (K := F) π).trans
      ((IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap
        (v := w) (K := F) π).trans hπ)
    exact h
  have hπOw0 : (algebraMap (𝓞 F) (w.adicCompletionIntegers F) π) ≠ 0 := by
    intro h0
    rw [h0] at hπw
    simp at hπw
  have hspanOw : IsLocalRing.maximalIdeal (w.adicCompletionIntegers F) =
      Ideal.span {(algebraMap (𝓞 F) (w.adicCompletionIntegers F) π)} :=
    IsDedekindDomain.HeightOneSpectrum.adicCompletion.maximalIdeal_eq_span_uniformizer
      F w hπw
  have hspanIC : IsLocalRing.maximalIdeal
      (IntegralClosure (w.adicCompletionIntegers F) ↥M) =
      Ideal.span {algebraMap (w.adicCompletionIntegers F)
        (IntegralClosure (w.adicCompletionIntegers F) ↥M)
        (algebraMap (𝓞 F) (w.adicCompletionIntegers F) π)} := by
    rw [← hmax, hspanOw, Ideal.map_span, Set.image_singleton]
  have hICinj : Function.Injective (algebraMap (w.adicCompletionIntegers F)
      (IntegralClosure (w.adicCompletionIntegers F) ↥M)) := by
    have h1 : Function.Injective (algebraMap (w.adicCompletionIntegers F) ↥M) :=
      FaithfulSMul.algebraMap_injective _ _
    intro a b hab
    exact h1 (congrArg Subtype.val hab)
  have hπIC0 : algebraMap (w.adicCompletionIntegers F)
      (IntegralClosure (w.adicCompletionIntegers F) ↥M)
      (algebraMap (𝓞 F) (w.adicCompletionIntegers F) π) ≠ 0 := by
    intro h0
    exact hπOw0 (hICinj (by rw [h0, map_zero]))
  -- `e(Q₀ | w) = 1`
  have hple : Ideal.map (algebraMap (𝓞 F) (𝓞 ↥K)) w.asIdeal ≤ Q₀ :=
    Ideal.map_le_iff_le_comap.mpr (le_of_eq hunder.symm)
  have he1 : Ideal.ramificationIdx' w.asIdeal Q₀ = 1 := by
    by_contra hne1
    have hsq := (Ideal.ramificationIdx'_ne_one_iff hple).mp hne1
    have hqQ2 : algebraMap (𝓞 F) (𝓞 ↥K) π ∈ Q₀ ^ 2 :=
      hsq (Ideal.mem_map_of_mem _ hπmem)
    have hcomap2 : Q₀ ^ 2 ≤ Ideal.comap φ
        ((IsLocalRing.maximalIdeal
          (IntegralClosure (w.adicCompletionIntegers F) ↥M)) ^ 2) := by
      rw [pow_two, pow_two, hQ₀def]
      exact Ideal.mul_le.mpr fun r hr t ht => Ideal.mem_comap.mpr
        (by rw [map_mul]; exact Ideal.mul_mem_mul hr ht)
    have hφπ := Ideal.mem_comap.mp (hcomap2 hqQ2)
    rw [hcomm π, hspanIC, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hφπ
    obtain ⟨c, hc⟩ := hφπ
    have hcancel : algebraMap (w.adicCompletionIntegers F)
        (IntegralClosure (w.adicCompletionIntegers F) ↥M)
        (algebraMap (𝓞 F) (w.adicCompletionIntegers F) π) * c = 1 := by
      refine mul_left_cancel₀ hπIC0 ?_
      rw [mul_one, ← mul_assoc, ← pow_two]
      exact hc.symm
    have hmemπ : algebraMap (w.adicCompletionIntegers F)
        (IntegralClosure (w.adicCompletionIntegers F) ↥M)
        (algebraMap (𝓞 F) (w.adicCompletionIntegers F) π) ∈
        IsLocalRing.maximalIdeal
          (IntegralClosure (w.adicCompletionIntegers F) ↥M) := by
      rw [hspanIC]; exact Ideal.mem_span_singleton_self _
    exact (IsLocalRing.maximalIdeal.isMaximal _).ne_top
      (Ideal.eq_top_of_isUnit_mem _ hmemπ
        (isUnit_iff_exists.mpr ⟨c, hcancel, by rwa [mul_comm] at hcancel⟩))
  -- conclude `|I(Q₀)| = e = 1`
  haveI : IsGaloisGroup (↥K ≃ₐ[F] ↥K) (𝓞 F) (𝓞 ↥K) :=
    IsGaloisGroup.of_isFractionRing (↥K ≃ₐ[F] ↥K) (𝓞 F) (𝓞 ↥K) F ↥K
  haveI hmaxw : w.asIdeal.IsMaximal := w.isPrime.isMaximal_of_ne_bot w.ne_bot
  have hsurjw : Function.Surjective
      (algebraMap (𝓞 F ⧸ w.asIdeal) w.asIdeal.ResidueField) :=
    IsFractionRing.surjective_iff_isField.mpr
      ((Ideal.Quotient.maximal_ideal_iff_isField_quotient _).mp hmaxw)
  haveI : Finite (𝓞 F ⧸ w.asIdeal) :=
    Ring.HasFiniteQuotients.finiteQuotient w.ne_bot
  haveI : Finite (w.asIdeal.ResidueField) := Finite.of_surjective _ hsurjw
  have h2 : Q₀.ramificationIdx (𝓞 F) = 1 := by
    rw [← Ideal.ramificationIdx'_eq_ramificationIdx w.asIdeal Q₀ w.ne_bot]
    exact he1
  have hcard := Ideal.card_inertia_eq_ramificationIdxIn
    (G := (↥K ≃ₐ[F] ↥K)) w.asIdeal Q₀
  rw [Ideal.ramificationIdxIn_eq_ramificationIdx w.asIdeal Q₀ (↥K ≃ₐ[F] ↥K), h2] at hcard
  exact Subgroup.eq_bot_of_card_eq _ hcard

/-- **Trivial ideal-inertia propagates to every prime over `w`** (PROVEN
2026-07-26; step (b), and the `F`-level twin of `MazurTorsion.lean`'s
`inertia_eq_bot_of_exists_prime_over`).

`Gal(K/F)` acts transitively on the primes of `𝓞 K` over `w`
(`Ideal.exists_smul_eq_of_isGaloisGroup`, through
`IsGaloisGroup.of_isFractionRing`), and `I(σ • Q₀) = σ I(Q₀) σ⁻¹`, so a
single prime with trivial inertia forces all of them to have it. -/
theorem inertia_eq_bot_of_exists_prime_over_hilbert
    (F : Type u) [Field F] [NumberField F]
    (K : IntermediateField F (AlgebraicClosure F))
    [FiniteDimensional F K] [IsGalois F K] [NumberField ↥K]
    (w : HeightOneSpectrum (𝓞 F))
    (Q₀ : Ideal (𝓞 ↥K)) [Q₀.IsPrime] [Q₀.LiesOver w.asIdeal]
    (hQ₀ : Q₀.inertia (↥K ≃ₐ[F] ↥K) = ⊥)
    (Q : Ideal (𝓞 ↥K)) [Q.IsPrime] [Q.LiesOver w.asIdeal] :
    Q.inertia (↥K ≃ₐ[F] ↥K) = ⊥ := by
  haveI : IsGaloisGroup (↥K ≃ₐ[F] ↥K) (𝓞 F) (𝓞 ↥K) :=
    IsGaloisGroup.of_isFractionRing (↥K ≃ₐ[F] ↥K) (𝓞 F) (𝓞 ↥K) F ↥K
  obtain ⟨σ, hσ⟩ :=
    Ideal.exists_smul_eq_of_isGaloisGroup w.asIdeal Q₀ Q (↥K ≃ₐ[F] ↥K)
  rw [← hσ]
  rw [Subgroup.eq_bot_iff_forall] at hQ₀ ⊢
  intro g hg
  have hconj : σ⁻¹ * g * σ ∈ Q₀.inertia (↥K ≃ₐ[F] ↥K) := by
    intro y
    have h1 := hg (σ • y)
    rw [Submodule.mem_toAddSubgroup,
      Ideal.mem_pointwise_smul_iff_inv_smul_mem] at h1
    rw [Submodule.mem_toAddSubgroup]
    have h2 : σ⁻¹ • (g • σ • y - σ • y) = (σ⁻¹ * g * σ) • y - y := by
      rw [smul_sub, inv_smul_smul, ← mul_smul, ← mul_smul]
    rwa [h2] at h1
  have h3 : σ⁻¹ * g * σ = 1 := hQ₀ _ hconj
  have h4 : g = σ * (σ⁻¹ * g * σ) * σ⁻¹ := by group
  rw [h4, h3, mul_one, mul_inv_cancel]

/-- **Local-global inertia transport over `F`** (PROVEN 2026-07-26; it was
half (1) of the cut of `not_dvd_discr_of_hilbertInertiaTrivialAt` below,
the genuinely `F`-level half): if the local inertia at a place `w` of `F`
acts trivially on the finite Galois subextension `K ⊆ Fᵃˡᵍ`, then every
prime `P` of `𝓞 K` lying over `w` is unramified over `𝓞 F`.

This is the `F`-level twin of `FreyCurve/MazurTorsion.lean`'s PROVEN
`isUnramifiedAt_of_inertia_le_fixingSubgroup`, and it was genuinely new
work rather than a reuse: every line of that development is written over
`ℚ` and over `hq.toHeightOneSpectrumRingOfIntegersRat`, and
`MazurTorsion.lean` is NOT in this module's import cone (it is not
importable here without enlarging the cone from 32 to 91 modules, which
would make this module — and `Deformation.lean`, which re-exports it —
rebuild on every `MazurTorsion` merge). The port was carried out AS THE
DOCSTRING PREDICTED, in the same two steps, which are now the two PROVEN
declarations immediately above:
`exists_prime_over_inertia_eq_bot_of_hilbertInertiaTrivialAt` (the
embedding-determined prime over `w` has trivial ideal-inertia, the local
node of `LocalInertiaFixedField.lean` doing the work) and
`inertia_eq_bot_of_exists_prime_over_hilbert` (conjugacy under `Gal(K/F)`,
transitive on the primes over `w`, propagates it to all of them). What is
left here is the counting step: `|I(P)| = e(P | w)`
(`Ideal.card_inertia_eq_ramificationIdxIn`, whose `PerfectField` side
condition is discharged by finiteness of the residue field of `w`), and
`e = 1 ↔ unramified` (`Ideal.ramificationIdx_eq_one_iff`).

ONE IMPORT NOTE, because it cost a build cycle.
`LocalInertiaFixedField.lean` was already in this module's transitive cone
but only through a NON-public import, so
`maximalIdeal_map_eq_of_le_fixedField_localInertiaGroup` was not in scope —
in a proof BODY, not merely in signature position. It is now
`public import`ed at the head of this file; the cone is unchanged.

FAITHFULNESS. The quantifier is over `localInertiaGroup w` — an
inertia-only hypothesis, which is exactly what makes the conclusion
`Algebra.IsUnramifiedAt (𝓞 F) P` correct; widening it to all of `Γ F`
would be a different (and for this purpose wrong) statement. Not
vacuous: `K = ⊥` and any everywhere-unramified extension of `F` inhabit
the hypotheses, and the conclusion is a genuine restriction. -/
theorem isUnramifiedAt_of_hilbertInertiaTrivialAt
    (F : Type u) [Field F] [NumberField F]
    (K : IntermediateField F (AlgebraicClosure F))
    [FiniteDimensional F K] [IsGalois F K] [NumberField ↥K]
    (w : HeightOneSpectrum (𝓞 F))
    (hinert : HilbertInertiaTrivialAt w K.fixingSubgroup)
    (P : Ideal (𝓞 ↥K)) [P.IsPrime] [P.LiesOver w.asIdeal] :
    Algebra.IsUnramifiedAt (𝓞 F) P := by
  haveI : IsGaloisGroup (↥K ≃ₐ[F] ↥K) (𝓞 F) (𝓞 ↥K) :=
    IsGaloisGroup.of_isFractionRing (↥K ≃ₐ[F] ↥K) (𝓞 F) (𝓞 ↥K) F ↥K
  -- the residue field of `w` is finite, hence perfect: the hypothesis of
  -- `Ideal.card_inertia_eq_ramificationIdxIn` and of
  -- `Ideal.ramificationIdx_eq_one_iff`
  haveI hmaxw : w.asIdeal.IsMaximal := w.isPrime.isMaximal_of_ne_bot w.ne_bot
  have hsurjw : Function.Surjective
      (algebraMap (𝓞 F ⧸ w.asIdeal) w.asIdeal.ResidueField) :=
    IsFractionRing.surjective_iff_isField.mpr
      ((Ideal.Quotient.maximal_ideal_iff_isField_quotient _).mp hmaxw)
  haveI : Finite (𝓞 F ⧸ w.asIdeal) :=
    Ring.HasFiniteQuotients.finiteQuotient w.ne_bot
  haveI : Finite (w.asIdeal.ResidueField) := Finite.of_surjective _ hsurjw
  -- (a) one prime over `w` has trivial inertia, (b) hence all of them do
  obtain ⟨Q₀, hQ₀p, hQ₀o, hQ₀⟩ :=
    exists_prime_over_inertia_eq_bot_of_hilbertInertiaTrivialAt F K w hinert
  have hbot : P.inertia (↥K ≃ₐ[F] ↥K) = ⊥ :=
    inertia_eq_bot_of_exists_prime_over_hilbert F K w Q₀ hQ₀ P
  -- `e = |I| = |⊥| = 1`
  have hcard := Ideal.card_inertia_eq_ramificationIdxIn
    (G := (↥K ≃ₐ[F] ↥K)) w.asIdeal P
  rw [hbot] at hcard
  have h1 : Ideal.ramificationIdxIn w.asIdeal (𝓞 ↥K) = 1 := by
    rw [← hcard]; simp
  have h2 : P.ramificationIdx (𝓞 F) = 1 := by
    rw [← Ideal.ramificationIdxIn_eq_ramificationIdx w.asIdeal P (↥K ≃ₐ[F] ↥K)]
    exact h1
  exact Ideal.ramificationIdx_eq_one_iff.mp h2

/-- **Ramification in the tower `ℚ ⊆ F ⊆ K`** (PROVEN 2026-07-26; it was
half (2) of the cut of `not_dvd_discr_of_hilbertInertiaTrivialAt` below,
the routine half): a rational prime `q` with `q ∤ d_F` is unramified in
`F`, so a prime `P` of `𝓞 K` over `q` that is unramified over `𝓞 F` is
unramified over `ℤ`.

ROUTE AS EXECUTED, which is shorter than the different-ideal route this
docstring originally recorded. `q ∤ d_F` gives
`Algebra.IsUnramifiedAt ℤ (P.under (𝓞 F))` through mathlib's
`NumberField.not_dvd_discr_iff_forall_mem` applied to `F` — the
membership `(q : 𝓞 F) ∈ P.under (𝓞 F)` is `hmem` transported along
`map_natCast`. Composing with the hypothesis
`Algebra.IsUnramifiedAt (𝓞 F) P` is then mathlib's
`Algebra.IsUnramifiedAt.comp`, which is transitivity of
`Algebra.FormallyUnramified` at the localizations and needs no
different-ideal bookkeeping at all; the tower instance
`IsScalarTower ℤ (𝓞 F) (𝓞 K)` and `P.LiesOver (P.under (𝓞 F))` are both
found by synthesis. (`differentIdeal_eq_differentIdeal_mul_differentIdeal`
together with `not_dvd_differentIdeal_iff` is a second, longer route: it
would additionally require the separability side conditions of the
different, which `IsUnramifiedAt.comp` does not.)

FAITHFULNESS. `hqF` (`q ∤ d_F`) is LOAD-BEARING and must not be dropped:
`d_K` is divisible by `d_F ^ [K : F]` by the discriminant tower formula,
so every prime dividing `d_F` divides `d_K` however unramified `K/F`
is. -/
theorem isUnramifiedAt_int_of_isUnramifiedAt_of_not_dvd_discr
    (F : Type u) [Field F] [NumberField F]
    (K : IntermediateField F (AlgebraicClosure F))
    [FiniteDimensional F K] [NumberField ↥K]
    {q : ℕ} (hq : q.Prime)
    (hqF : ¬ ((q : ℤ) ∣ NumberField.discr F))
    (P : Ideal (𝓞 ↥K)) [P.IsPrime]
    (hmem : (q : 𝓞 ↥K) ∈ P)
    (hur : Algebra.IsUnramifiedAt (𝓞 F) P) :
    Algebra.IsUnramifiedAt ℤ P := by
  haveI := hur
  -- The place `w` of `F` below `P`.
  set w : Ideal (𝓞 F) := P.under (𝓞 F) with hw
  haveI : w.IsPrime := Ideal.IsPrime.under (𝓞 F) P
  haveI : P.LiesOver w := ⟨rfl⟩
  -- `q ∈ w`, because `q` is a rational integer lying in `P`.
  have hqw : ((q : ℤ) : 𝓞 F) ∈ w := by
    rw [hw, Ideal.under, Ideal.mem_comap]
    push_cast
    simpa using hmem
  -- `q ∤ d_F` makes `w` unramified over `ℤ`.
  haveI : Algebra.IsUnramifiedAt ℤ w :=
    (NumberField.not_dvd_discr_iff_forall_mem F (𝓞 F)
      (Nat.prime_iff_prime_int.mp hq)).mp hqF w inferInstance hqw
  -- Unramifiedness composes along the tower `ℤ ⊆ 𝓞 F ⊆ 𝓞 K`.
  exact Algebra.IsUnramifiedAt.comp (R := ℤ) (A := 𝓞 F) (B := 𝓞 ↥K) w P

/-- **Inertia-trivial extensions of `F` have discriminant supported over
`2ℓd_F`** (PROVEN 2026-07-26 over the two leaves immediately above — it
was itself a leaf until then; the second and genuinely `F`-level
arithmetic input of Hermite–Minkowski over `F`): if the local inertia of
`F` at every place away from `2` and `ℓ` acts trivially on the finite
Galois subextension `K ⊆ Fᵃˡᵍ`, then no rational prime `q ∉ {2, ℓ}` with
`q ∤ d_F` divides the discriminant of `K` viewed as a number field over
`ℚ`.

WHAT IS PROVEN HERE — the whole non-arithmetic half, and it is the
place-selection bookkeeping that the two halves are glued by. Mathlib's
`NumberField.not_dvd_discr_iff_forall_mem` reduces the goal to
`Algebra.IsUnramifiedAt ℤ P` for every prime `P` of `𝓞 K` over `q`; the
place `w` of `F` below `P` is `P.under (𝓞 F)` (prime, and nonzero
because it contains `q`); `P ∩ ℤ = (q)` because a prime of `ℤ`
containing the prime `q` is `(q)`, whence a rational integer lying in
`w` is divisible by `q`, so `q ≠ 2` and `q ≠ ℓ` put `w` outside
`{w ∣ 2ℓ}` and the inertia hypothesis applies at `w`. The two leaves
then compose: `isUnramifiedAt_of_hilbertInertiaTrivialAt` gives
`IsUnramifiedAt (𝓞 F) P` and
`isUnramifiedAt_int_of_isUnramifiedAt_of_not_dvd_discr` descends it to
`ℤ`.

ONE ELABORATION NOTE worth keeping. `↥(K.restrictScalars ℚ)` and `↥K`
are DEFEQ (`restrictScalars` keeps the carrier), and so are `𝓞` of them;
but `Algebra F ↥(K.restrictScalars ℚ)` is NOT an instance, so
`Ideal.under (𝓞 F)` cannot be formed against the `restrictScalars`
carrier. The proof therefore opens with
`show ¬ ((q : ℤ) ∣ NumberField.discr ↥K)` and does everything over the
canonical carrier, where `Algebra F ↥K` and `Algebra (𝓞 F) (𝓞 ↥K)` are
the canonical instances. Supplying the missing instance by
`inferInstanceAs` instead does NOT work: it generates auxiliary
definitions, and the two sides then carry syntactically distinct
`Algebra` terms that print identically and refuse to unify.

MATHEMATICAL CONTENT, and the cut this declaration NOW MAKES (the two
leaves above are exactly these two steps). Two steps, of
which only the FIRST is genuinely new at the `F` level:

1. *Local-global inertia transport over `F`* — pointwise triviality of
   the image of `localInertiaGroup w` in `Γ F` on `K` forces every prime
   `P` of `𝓞 K` over `w` to be unramified over `𝓞 F`. This is the
   `F`-level twin of `FreyCurve/MazurTorsion.lean`'s PROVEN
   `isUnramifiedAt_of_inertia_le_fixingSubgroup` (via
   `exists_prime_over_inertia_eq_bot_of_le_fixingSubgroup` and
   `inertia_eq_bot_of_exists_prime_over`): the embedding-determined prime
   over `w` has trivial ideal-inertia because the local Galois group
   surjects onto the decomposition group, and conjugacy under
   `Gal(K/F)` — transitive on the primes over `w` — propagates it to all
   of them. Every line of that chain is written over `ℚ` and over
   `hq.toHeightOneSpectrumRingOfIntegersRat`; the `F`-level version needs
   the same argument with `w : HeightOneSpectrum (𝓞 F)` in place of the
   rational prime.
2. *Ramification in the tower `ℚ ⊆ F ⊆ K`* — a rational prime `q` with
   `q ∤ d_F` is unramified in `F`, so `e(w ∣ q) = 1` for the place `w`
   below `P`; combined with `e(P ∣ w) = 1` from (1), multiplicativity of
   the ramification index gives `e(P ∣ q) = 1`, and a prime unramified in
   every prime above it does not divide the discriminant
   (`NumberField.not_dvd_discr_iff_forall_mem`). In the different
   language this is mathlib's tower formula
   `differentIdeal_eq_differentIdeal_mul_differentIdeal` together with
   `not_dvd_differentIdeal_iff`, and it is the routine half.

The hypotheses are exactly what makes `q` avoid the bad set: `q ≠ 2` and
`q ≠ ℓ` put every place `w` of `F` over `q` outside `{w ∣ 2ℓ}`, where the
inertia hypothesis applies, and `q ∤ d_F` is step (2)'s input.

BOTH-WAYS AUDIT. Faithful in both directions. It is not vacuous: the
hypothesis set is inhabited (`K = ⊥` satisfies every clause, and so does
any everywhere-unramified extension of `F`, e.g. the Hilbert class
field), and the conclusion is a genuine restriction — dropping `q ∤ d_F`
makes the statement FALSE, since `d_K` is divisible by `d_F^{[K : F]}`
by the discriminant tower formula, so every prime dividing `d_F` divides
`d_K` no matter how unramified `K/F` is. Dropping `q ≠ 2` or `q ≠ ℓ` is
likewise false (a ramified place over `2` or `ℓ` is not excluded by any
hypothesis). -/
theorem not_dvd_discr_of_hilbertInertiaTrivialAt (ℓ : ℕ) [Fact ℓ.Prime]
    (F : Type u) [Field F] [NumberField F]
    (K : IntermediateField F (AlgebraicClosure F))
    (hfd : FiniteDimensional F K) (hgal : IsGalois F K)
    (hinert : ∀ w : HeightOneSpectrum (𝓞 F), ((2 : ℕ) : 𝓞 F) ∉ w.asIdeal →
      ((ℓ : ℕ) : 𝓞 F) ∉ w.asIdeal → HilbertInertiaTrivialAt w K.fixingSubgroup)
    {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) (hqℓ : q ≠ ℓ)
    (hqF : ¬ ((q : ℤ) ∣ NumberField.discr F))
    (hfdQ : FiniteDimensional ℚ (K.restrictScalars ℚ)) :
    haveI : NumberField (K.restrictScalars ℚ) := @NumberField.mk _ _ inferInstance hfdQ
    ¬ ((q : ℤ) ∣ NumberField.discr (K.restrictScalars ℚ)) := by
  haveI := hfd
  haveI := hgal
  haveI : NumberField (K.restrictScalars ℚ) := @NumberField.mk _ _ inferInstance hfdQ
  haveI hnfK : NumberField ↥K := inferInstanceAs (NumberField ↥(K.restrictScalars ℚ))
  have hqZ : Prime ((q : ℤ)) := Nat.prime_iff_prime_int.mp hq
  -- move to the canonical carrier `↥K`: `↥(K.restrictScalars ℚ)` and `↥K` are
  -- DEFEQ (`restrictScalars` keeps the carrier), and working over the canonical
  -- one keeps the `Algebra F ↥K` / `Algebra (𝓞 F) (𝓞 ↥K)` instances canonical
  show ¬ ((q : ℤ) ∣ NumberField.discr ↥K)
  rw [NumberField.not_dvd_discr_iff_forall_mem (↥K) (𝓞 ↥K) hqZ]
  intro P hP hmem
  haveI := hP
  have hmem' : (q : 𝓞 ↥K) ∈ P := by exact_mod_cast hmem
  -- `P ∩ ℤ = (q)`, since a prime of `ℤ` containing the prime `q` is `(q)`
  haveI hqZmax : (Ideal.span {(q : ℤ)}).IsMaximal :=
    ((Ideal.span_singleton_prime (by exact_mod_cast hq.ne_zero)).mpr hqZ).isMaximal
      (by simp only [Ne, Ideal.span_singleton_eq_bot]; exact_mod_cast hq.ne_zero)
  have hqinP : ((q : ℤ)) ∈ Ideal.under ℤ P := by
    rw [Ideal.mem_under]
    exact_mod_cast hmem'
  have hunderZ : Ideal.under ℤ P = Ideal.span {(q : ℤ)} :=
    (hqZmax.eq_of_le (Ideal.IsPrime.ne_top inferInstance)
      (by rwa [Ideal.span_le, Set.singleton_subset_iff])).symm
  -- the place `w` of `F` below `P`
  haveI hw0p : (P.under (𝓞 F)).IsPrime := Ideal.IsPrime.under (𝓞 F) P
  have hqw0 : (q : 𝓞 F) ∈ P.under (𝓞 F) := by
    rw [Ideal.mem_under]
    exact_mod_cast hmem'
  have hw0bot : P.under (𝓞 F) ≠ ⊥ := by
    intro h
    rw [h, Ideal.mem_bot] at hqw0
    exact hq.ne_zero (by exact_mod_cast hqw0)
  set w : HeightOneSpectrum (𝓞 F) := ⟨P.under (𝓞 F), hw0p, hw0bot⟩ with hwdef
  -- `2` and `ℓ` avoid `w`: `w` lies over `q`, and `q ∉ {2, ℓ}`
  have hnat : ∀ m : ℕ, ((m : ℕ) : 𝓞 F) ∈ w.asIdeal → q ∣ m := by
    intro m hm
    have hmP : ((m : ℕ) : 𝓞 ↥K) ∈ P := by
      have hm' : ((m : ℕ) : 𝓞 F) ∈ P.under (𝓞 F) := by rw [hwdef] at hm; exact hm
      rw [Ideal.mem_under] at hm'
      exact_mod_cast hm'
    have hmZ : ((m : ℕ) : ℤ) ∈ Ideal.under ℤ P := by
      rw [Ideal.mem_under]
      exact_mod_cast hmP
    rw [hunderZ, Ideal.mem_span_singleton] at hmZ
    exact_mod_cast hmZ
  have h2 : ((2 : ℕ) : 𝓞 F) ∉ w.asIdeal := fun hc =>
    hq2 ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp (hnat 2 hc))
  have hl : ((ℓ : ℕ) : 𝓞 F) ∉ w.asIdeal := fun hc =>
    hqℓ ((Nat.prime_dvd_prime_iff_eq hq (Fact.out : ℓ.Prime)).mp (hnat ℓ hc))
  haveI hlies : P.LiesOver w.asIdeal := ⟨rfl⟩
  exact isUnramifiedAt_int_of_isUnramifiedAt_of_not_dvd_discr F K hq hqF P hmem'
    (isUnramifiedAt_of_hilbertInertiaTrivialAt F K w (hinert w h2 hl) P)

/-- **Hermite–Minkowski over `F`** (PROVEN 2026-07-26 over the two
arithmetic leaves above — the ONLY arithmetic input of Schlessinger's H3
at the `F` level): for a fixed degree bound `n` there are only finitely
many finite Galois subextensions `K` of `Fᵃˡᵍ/F` with `[K : F] ≤ n` on
which the local inertia at every place of `F` away from `2` and `ℓ` acts
trivially.

PROOF (the whole non-arithmetic half, written out here). Restriction of
scalars `K ↦ K.restrictScalars ℚ` is injective
(`IntermediateField.restrictScalars_injective`), so it suffices to make
the IMAGE finite, and the image sits inside the fields of `Fᵃˡᵍ` of
bounded discriminant, which is Hermite's theorem
(`NumberField.finite_of_discr_bdd`, applicable because `Fᵃˡᵍ` is a field
of characteristic zero — algebraic closedness is not needed). The bound:
put `N = [F : ℚ]·n`, `c = (N + 1)·N` and `M = 2·ℓ·|d_F|`. Then

* `[K : ℚ] = [F : ℚ]·[K : F] ≤ N` (`Module.finrank_mul_finrank`, with
  `FiniteDimensional.trans` supplying finiteness over `ℚ`);
* every prime `q` dividing `|d_K|` divides `M`, by
  `not_dvd_discr_of_hilbertInertiaTrivialAt` — a `q` dividing neither
  `2`, nor `ℓ`, nor `|d_F|` is excluded;
* `v_q(|d_K|) ≤ c` for every `q`, by
  `discr_factorization_le_of_finrank_le`;

so `|d_K|.factorization ≤ c • M.factorization` pointwise, i.e.
`|d_K| ∣ M^c` (`Nat.factorization_le_iff_dvd`), whence `|d_K| ≤ M^c`.

MATHEMATICAL CONTENT of the two leaves: such a `K` is unramified over
`F` outside the places above `2ℓ`, hence unramified over `ℚ` outside the
rational primes dividing `2·ℓ·d_F`, with different exponents bounded in
terms of the degree alone (Serre, *Corps Locaux* III §6 Prop. 13).

THE DEDUPE THIS CUT IS DESIGNED FOR — HALF OF IT IS NOW DONE (update
2026-07-26). Three copies of Hermite–Minkowski existed in the tree:
`finite_setOf_intermediateField_inertiaAt_le` (over `ℚ`, place-indexed by
rational primes, PROVEN over the same two ingredients),
`Deformation.lean`'s `finite_setOf_isHardlyRamified_frames` (the `ℚ`
consumer), and this one. The honest discharge is the module split
recorded in `~/.flt-design-deformation-patching-dedup.md` — hoist the
Hermite–Minkowski block into a module upstream of all three and
generalize it from `ℚ`/`{2, p}` to a variable base number field and a
finite set of places.

**The hoist has since happened**: the block now lives in
`HardlyRamified/HermiteMinkowski.lean` (which is where
`finite_setOf_intermediateField_inertiaAt_le` and the different-exponent
chain moved to, out of `Modularity/Patching.lean`), upstream of all three
consumers. The half of this docstring's plan that was "a signature
change, no mathematics" is therefore DISCHARGED:
`discr_factorization_le_of_finrank_le` above is now PROVEN by importing
that module and deleting the ambient binder from its proof. What remains
of the plan is the genuinely new argument it also named — generalizing
`MazurTorsion.lean`'s inertia dictionary from `ℚ` to `F`, which is what
`not_dvd_discr_of_hilbertInertiaTrivialAt` still carries.

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
            HilbertInertiaTrivialAt w K.fixingSubgroup}.Finite := by
  classical
  -- the degree bound over `ℚ`, the exponent bound, and the bad modulus
  set N : ℕ := Module.finrank ℚ F * n with hNdef
  set c : ℕ := (N + 1) * N with hcdef
  set M : ℕ := 2 * ℓ * (NumberField.discr F).natAbs with hMdef
  have hdF0 : (NumberField.discr F).natAbs ≠ 0 :=
    Int.natAbs_ne_zero.mpr (NumberField.discr_ne_zero F)
  have hM0 : M ≠ 0 := by
    rw [hMdef]
    exact Nat.mul_ne_zero (Nat.mul_ne_zero two_ne_zero (Fact.out : ℓ.Prime).ne_zero) hdF0
  -- restriction of scalars is injective, so it suffices to bound the image
  refine Set.Finite.of_finite_image
    (f := fun K : IntermediateField F (AlgebraicClosure F) => K.restrictScalars ℚ)
    ?_ (Set.injOn_of_injective (IntermediateField.restrictScalars_injective ℚ))
  refine Set.Finite.subset
    ((NumberField.finite_of_discr_bdd (AlgebraicClosure F) (M ^ c)).image Subtype.val) ?_
  rintro _ ⟨K, ⟨hfd, hgal, hrank, hinert⟩, rfl⟩
  haveI := hfd
  have hfdQ : FiniteDimensional ℚ (K.restrictScalars ℚ) := FiniteDimensional.trans ℚ F K
  refine ⟨⟨K.restrictScalars ℚ, hfdQ⟩, ?_, rfl⟩
  haveI hNF : NumberField (K.restrictScalars ℚ) := @NumberField.mk _ _ inferInstance hfdQ
  show |NumberField.discr (K.restrictScalars ℚ)| ≤ ((M ^ c : ℕ) : ℤ)
  set a : ℕ := (NumberField.discr (K.restrictScalars ℚ)).natAbs with hadef
  have ha0 : a ≠ 0 := Int.natAbs_ne_zero.mpr (NumberField.discr_ne_zero _)
  -- `[K : ℚ] = [F : ℚ]·[K : F] ≤ N`
  have hrankQ : Module.finrank ℚ (K.restrictScalars ℚ) ≤ N := by
    calc Module.finrank ℚ (K.restrictScalars ℚ)
        = Module.finrank ℚ F * Module.finrank F K := (Module.finrank_mul_finrank ℚ F K).symm
      _ ≤ Module.finrank ℚ F * n := Nat.mul_le_mul_left _ hrank
      _ = N := hNdef.symm
  -- the two arithmetic inputs
  have hexp : ∀ q : ℕ, a.factorization q ≤ c := fun q => by
    rw [hcdef, hadef]
    exact discr_factorization_le_of_finrank_le N (K.restrictScalars ℚ) hrankQ q
  have hsupp : ∀ q : ℕ, q.Prime → q ∣ a → q ∣ M := by
    intro q hq hqa
    by_contra hqM
    have h2 : q ≠ 2 := by
      rintro rfl
      exact hqM (by rw [hMdef]; exact ⟨ℓ * (NumberField.discr F).natAbs, by ring⟩)
    have hl : q ≠ ℓ := by
      rintro rfl
      exact hqM (by rw [hMdef]; exact ⟨2 * (NumberField.discr F).natAbs, by ring⟩)
    have hdF : ¬ ((q : ℤ) ∣ NumberField.discr F) := by
      intro hdvd
      have hnat : q ∣ (NumberField.discr F).natAbs := by
        simpa using Int.natAbs_dvd_natAbs.mpr hdvd
      exact hqM (by rw [hMdef]; exact hnat.mul_left (2 * ℓ))
    have hZ : ((q : ℤ)) ∣ NumberField.discr (K.restrictScalars ℚ) := by
      have h1 : ((a : ℤ)) ∣ NumberField.discr (K.restrictScalars ℚ) := by
        rw [hadef, Int.natCast_natAbs]
        exact (abs_dvd _ _).mpr dvd_rfl
      exact dvd_trans (Int.natCast_dvd_natCast.mpr hqa) h1
    exact not_dvd_discr_of_hilbertInertiaTrivialAt ℓ F K hfd hgal hinert hq h2 hl hdF hfdQ hZ
  -- pointwise on factorizations, hence `|d_K| ∣ M ^ c`
  have hdvdM : a ∣ M ^ c := by
    rw [← Nat.factorization_le_iff_dvd ha0 (pow_ne_zero _ hM0)]
    refine Finsupp.le_def.mpr fun q => ?_
    simp only [Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul]
    by_cases hq0 : a.factorization q = 0
    · simp [hq0]
    · have hmem : q ∈ a.primeFactors := by
        rw [← Nat.support_factorization]
        exact Finsupp.mem_support_iff.mpr hq0
      have h1 : 1 ≤ M.factorization q :=
        Nat.Prime.factorization_pos_of_dvd (Nat.prime_of_mem_primeFactors hmem) hM0
          (hsupp q (Nat.prime_of_mem_primeFactors hmem) (Nat.dvd_of_mem_primeFactors hmem))
      calc a.factorization q ≤ c := hexp q
        _ = c * 1 := (mul_one c).symm
        _ ≤ c * M.factorization q := Nat.mul_le_mul_left _ h1
  have hle : a ≤ M ^ c := Nat.le_of_dvd (Nat.pos_of_ne_zero (pow_ne_zero _ hM0)) hdvdM
  calc |NumberField.discr (K.restrictScalars ℚ)| = (a : ℤ) := by
        rw [hadef, Int.natCast_natAbs]
    _ ≤ ((M ^ c : ℕ) : ℤ) := by exact_mod_cast hle

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

/-! #### The base-field-free machinery of the pro-limit step

Everything in this subsection is pure commutative and linear algebra: no
Galois group, no number field, no place. It is the exact material that
`Deformation.lean` carries for the `ℚ`-level twin
`isTameAtTwo_of_forall_isOpen_quotient`, restated HERE because that module
lies DOWNSTREAM of this one and so nothing in it may be imported.

NAMING. Every name below is deliberately DIFFERENT from its `ℚ`-level
original (`isUnit_two_of_oddPrime`, `false_of_three_quotient_characters`,
`piIdeal`, `exists_unimodular_mem_iInf`, …). `Deformation.lean` `public
import`s this module into the SAME namespace, so a shared name would be a
duplicate declaration there; this repeats the convention already used for
`framePushforward` and the five transport bricks above. -/

/-- `2` is a unit in every `ℤ_[ℓ]`-algebra when `ℓ` is an odd prime.
(The `F`-level twin of `Deformation.lean`'s `isUnit_two_of_oddPrime`.) -/
lemma isUnit_two_of_odd_padicAlgebra (ℓ : ℕ) [Fact ℓ.Prime] (hodd : Odd ℓ)
    {A : Type*} [CommRing A] [Algebra ℤ_[ℓ] A] : IsUnit (2 : A) := by
  have hp : ℓ.Prime := Fact.out
  have hne : ℓ ≠ 2 := by
    rintro rfl
    rw [Nat.odd_iff] at hodd
    omega
  have hcop : Nat.Coprime ℓ 2 := (Nat.coprime_primes hp Nat.prime_two).mpr hne
  have h2 : IsUnit ((2 : ℕ) : ℤ_[ℓ]) :=
    PadicInt.isUnit_iff.mpr (PadicInt.norm_natCast_eq_one_iff.mpr hcop)
  have h3 := h2.map (algebraMap ℤ_[ℓ] A)
  rw [map_natCast] at h3
  simpa using h3

/-- In a nontrivial commutative ring in which `2` is a unit, `1 ≠ -1`. -/
lemma one_ne_neg_one_of_two_isUnit {A : Type*} [CommRing A] [Nontrivial A]
    (h2 : IsUnit (2 : A)) : (1 : A) ≠ -1 := by
  intro h
  have h0 : (2 : A) = 0 := by linear_combination h
  rw [h0] at h2
  exact not_isUnit_zero h2

/-- A unit lying in an ideal forces the ideal to be everything. -/
lemma eq_top_of_isUnit_mem {A : Type*} [CommRing A] (I : Ideal A) {x : A}
    (hx : x ∈ I) (hu : IsUnit x) : I = ⊤ := by
  obtain ⟨u, rfl⟩ := hu
  refine (Ideal.eq_top_iff_one I).mpr ?_
  have := I.mul_mem_left (↑u⁻¹ : A) hx
  simpa using this

/-- A square root of `1` in a local ring in which `2` is a unit is `±1`.
This is the `±1`-RIGIDITY on which the whole pro-limit argument turns, and
it is the ONE place the oddness of `ℓ` is used — see the leaf's docstring
for why the statement has no substitute at `ℓ = 2`. -/
lemma eq_pm_one_of_sq_eq_one_local {A : Type*} [CommRing A] [IsLocalRing A]
    (h2 : IsUnit (2 : A)) {x : A} (hx : x * x = 1) : x = 1 ∨ x = -1 := by
  have hfac : (x - 1) * (x + 1) = 0 := by linear_combination hx
  have hsum : IsUnit ((-(x - 1)) + (x + 1)) := by
    have he : (-(x - 1)) + (x + 1) = 2 := by ring
    rw [he]; exact h2
  rcases IsLocalRing.isUnit_or_isUnit_of_isUnit_add hsum with h | h
  · right
    have hu : IsUnit (x - 1) := (IsUnit.neg_iff _).mp h
    obtain ⟨u, hu'⟩ := hu
    have h1 : (↑u⁻¹ : A) * ((x - 1) * (x + 1)) = 0 := by rw [hfac, mul_zero]
    rw [← hu', ← mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mul] at h1
    linear_combination h1
  · left
    obtain ⟨u, hu'⟩ := h
    have h1 : (↑u⁻¹ : A) * ((x + 1) * (x - 1)) = 0 := by
      rw [mul_comm (x + 1) (x - 1), hfac, mul_zero]
    rw [← hu', ← mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mul] at h1
    linear_combination h1

/-- A `±1`-valued element of a commutative ring in which `2` is a unit is
determined by its class modulo any proper ideal. -/
lemma eq_of_pm_of_sub_mem {A : Type*} [CommRing A] (h2 : IsUnit (2 : A))
    {I : Ideal A} (hI : I ≠ ⊤) {x y : A}
    (hx : x = 1 ∨ x = -1) (hy : y = 1 ∨ y = -1) (h : x - y ∈ I) : x = y := by
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
  · rfl
  · refine absurd (eq_top_of_isUnit_mem I ?_ h2) hI
    have he : (1 : A) - -1 = 2 := by ring
    rwa [he] at h
  · refine absurd (eq_top_of_isUnit_mem I ?_ h2.neg) hI
    have he : (-1 : A) - 1 = -2 := by ring
    rwa [he] at h
  · rfl

/-- Two distinct `±1`-values stay distinct under a ring map to a nontrivial
ring in which `2` is a unit. -/
lemma map_ne_map_of_pm_of_ne {A B : Type*} [CommRing A] [CommRing B] [Nontrivial B]
    (f : A →+* B) (h2 : IsUnit (2 : B)) {x y : A}
    (hx : x = 1 ∨ x = -1) (hy : y = 1 ∨ y = -1) (hxy : x ≠ y) : f x ≠ f y := by
  have hone := one_ne_neg_one_of_two_isUnit h2
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
  · exact absurd rfl hxy
  · simpa using hone
  · simpa using fun h => hone h.symm
  · exact absurd rfl hxy

/-! ##### At most two quotient characters of a rank-two space -/

section HilbertThreeCharacters

variable {k : Type*} [Field k] {G : Type*}

/-- A nonzero vector of `k²` has a nonzero coordinate. -/
lemma coord_ne_zero_of_ne_zero_finTwo {a : Fin 2 → k} (ha : a ≠ 0) :
    a 0 ≠ 0 ∨ a 1 ≠ 0 := by
  by_cases h0 : a 0 = 0
  · refine Or.inr fun h1 => ha (funext fun j => ?_)
    fin_cases j
    · simpa using h0
    · simpa using h1
  · exact Or.inl h0

/-- Cramer: a nonzero `2 × 2` determinant kills the coefficients of a
vanishing linear combination. -/
lemma coeffs_eq_zero_of_det_ne_zero {a₁ a₂ : Fin 2 → k}
    (hD : a₁ 0 * a₂ 1 - a₁ 1 * a₂ 0 ≠ 0) {c d : k}
    (h0 : c * a₁ 0 + d * a₂ 0 = 0) (h1 : c * a₁ 1 + d * a₂ 1 = 0) :
    c = 0 ∧ d = 0 := by
  constructor
  · have huD : c * (a₁ 0 * a₂ 1 - a₁ 1 * a₂ 0) = 0 := by
      linear_combination a₂ 1 * h0 - a₂ 0 * h1
    exact (mul_eq_zero.mp huD).resolve_right hD
  · have hwD : d * (a₁ 0 * a₂ 1 - a₁ 1 * a₂ 0) = 0 := by
      linear_combination a₁ 0 * h1 - a₁ 1 * h0
    exact (mul_eq_zero.mp hwD).resolve_right hD

/-- **Two eigenvectors with somewhere-different eigenvalue functions
span**. -/
lemma det_ne_zero_of_eigenvalues_ne (m : G → Fin 2 → Fin 2 → k) (s t : G → k)
    (a b : Fin 2 → k)
    (ha : ∀ g j, ∑ i, m g j i * a i = s g * a j)
    (hb : ∀ g j, ∑ i, m g j i * b i = t g * b j)
    (ha0 : a ≠ 0) (hb0 : b ≠ 0) (g : G) (hst : s g ≠ t g) :
    a 0 * b 1 - a 1 * b 0 ≠ 0 := by
  intro hD
  simp only [Fin.sum_univ_two] at ha hb
  have key0 : ∀ j, b 0 * (s g * a j) - a 0 * (t g * b j) = 0 := by
    intro j
    linear_combination (-(b 0)) * ha g j + (a 0) * hb g j - (m g j 1) * hD
  have key1 : ∀ j, b 1 * (s g * a j) - a 1 * (t g * b j) = 0 := by
    intro j
    linear_combination (-(b 1)) * ha g j + (a 1) * hb g j + (m g j 0) * hD
  have hsub : s g - t g ≠ 0 := sub_ne_zero.mpr hst
  have h00 : a 0 * b 0 = 0 := by
    have hk := key0 0
    have h : (s g - t g) * (a 0 * b 0) = 0 := by linear_combination hk
    exact (mul_eq_zero.mp h).resolve_left hsub
  have h11 : a 1 * b 1 = 0 := by
    have hk := key1 1
    have h : (s g - t g) * (a 1 * b 1) = 0 := by linear_combination hk
    exact (mul_eq_zero.mp h).resolve_left hsub
  rcases coord_ne_zero_of_ne_zero_finTwo ha0 with ha0' | ha1'
  · have hb0z : b 0 = 0 := (mul_eq_zero.mp h00).resolve_left ha0'
    have hb1 : b 1 ≠ 0 := by
      intro h
      refine hb0 (funext fun j => ?_)
      fin_cases j
      · simpa using hb0z
      · simpa using h
    have ha1z : a 1 = 0 := (mul_eq_zero.mp h11).resolve_right hb1
    refine mul_ne_zero ha0' hb1 ?_
    linear_combination hD + b 0 * ha1z
  · have hb1z : b 1 = 0 := (mul_eq_zero.mp h11).resolve_left ha1'
    have hb0' : b 0 ≠ 0 := by
      intro h
      refine hb0 (funext fun j => ?_)
      fin_cases j
      · simpa using h
      · simpa using hb1z
    have ha0z : a 0 = 0 := (mul_eq_zero.mp h00).resolve_right hb0'
    refine mul_ne_zero ha1' hb0' ?_
    linear_combination -hD + b 1 * ha0z

/-- **At most two characters can occur as one-dimensional quotients of a
rank-two space** (elementary linear algebra over a field; the `F`-level
twin of `Deformation.lean`'s `false_of_three_quotient_characters`). -/
theorem false_of_three_quotient_chars (m : G → Fin 2 → Fin 2 → k)
    (s₁ s₂ s₃ : G → k) (a₁ a₂ a₃ : Fin 2 → k)
    (h₁ : ∀ g j, ∑ i, m g j i * a₁ i = s₁ g * a₁ j)
    (h₂ : ∀ g j, ∑ i, m g j i * a₂ i = s₂ g * a₂ j)
    (h₃ : ∀ g j, ∑ i, m g j i * a₃ i = s₃ g * a₃ j)
    (ha₁ : a₁ ≠ 0) (ha₂ : a₂ ≠ 0) (ha₃ : a₃ ≠ 0)
    (h12 : ∃ g, s₁ g ≠ s₂ g) (h13 : ∃ g, s₁ g ≠ s₃ g) (h23 : ∃ g, s₂ g ≠ s₃ g) :
    False := by
  obtain ⟨g₁₂, hg₁₂⟩ := h12
  obtain ⟨g₁₃, hg₁₃⟩ := h13
  obtain ⟨g₂₃, hg₂₃⟩ := h23
  have hD : a₁ 0 * a₂ 1 - a₁ 1 * a₂ 0 ≠ 0 :=
    det_ne_zero_of_eigenvalues_ne m s₁ s₂ a₁ a₂ h₁ h₂ ha₁ ha₂ g₁₂ hg₁₂
  set α : k := a₃ 0 * a₂ 1 - a₃ 1 * a₂ 0 with hα
  set β : k := a₁ 0 * a₃ 1 - a₁ 1 * a₃ 0 with hβ
  set D : k := a₁ 0 * a₂ 1 - a₁ 1 * a₂ 0 with hDdef
  have hexp0 : D * a₃ 0 = α * a₁ 0 + β * a₂ 0 := by
    simp only [hα, hβ, hDdef]; ring
  have hexp1 : D * a₃ 1 = α * a₁ 1 + β * a₂ 1 := by
    simp only [hα, hβ, hDdef]; ring
  have hexp : ∀ j, D * a₃ j = α * a₁ j + β * a₂ j := by
    intro j
    fin_cases j
    · exact hexp0
    · exact hexp1
  have hzero : ∀ g j, (α * (s₁ g - s₃ g)) * a₁ j + (β * (s₂ g - s₃ g)) * a₂ j = 0 := by
    intro g j
    have e₃ := h₃ g j
    have e₁ := h₁ g j
    have e₂ := h₂ g j
    simp only [Fin.sum_univ_two] at e₁ e₂ e₃
    have hx0 := hexp 0
    have hx1 := hexp 1
    have hxj := hexp j
    linear_combination D * e₃ - α * e₁ - β * e₂ - m g j 0 * hx0 - m g j 1 * hx1 +
      s₃ g * hxj
  have hcoef : ∀ g, α * (s₁ g - s₃ g) = 0 ∧ β * (s₂ g - s₃ g) = 0 := fun g =>
    coeffs_eq_zero_of_det_ne_zero hD (hzero g 0) (hzero g 1)
  have hα0 : α = 0 :=
    (mul_eq_zero.mp (hcoef g₁₃).1).resolve_right (sub_ne_zero.mpr hg₁₃)
  have hβ0 : β = 0 :=
    (mul_eq_zero.mp (hcoef g₂₃).2).resolve_right (sub_ne_zero.mpr hg₂₃)
  refine ha₃ (funext fun j => ?_)
  have hj := hexp j
  rw [hα0, hβ0] at hj
  simp only [zero_mul, add_zero] at hj
  simpa using (mul_eq_zero.mp hj).resolve_left hD

end HilbertThreeCharacters

/-! ##### Artinian truncations and Mittag-Leffler -/

section HilbertMittagLeffler

variable {R : Type u} [CommRing R]

/-- The quotient of a local ring by a power of its maximal ideal is local. -/
lemma isLocalRing_quotient_pow_maximalIdeal [IsLocalRing R] (n : ℕ) :
    IsLocalRing (R ⧸ (IsLocalRing.maximalIdeal R ^ (n + 1))) := by
  have hle : (IsLocalRing.maximalIdeal R ^ (n + 1) : Ideal R) ≤ IsLocalRing.maximalIdeal R :=
    Ideal.pow_le_self (Nat.succ_ne_zero n)
  have hne : (IsLocalRing.maximalIdeal R ^ (n + 1) : Ideal R) ≠ ⊤ := by
    intro h
    rw [h, top_le_iff] at hle
    exact (IsLocalRing.maximalIdeal.isMaximal R).ne_top hle
  haveI : Nontrivial (R ⧸ (IsLocalRing.maximalIdeal R ^ (n + 1))) :=
    Ideal.Quotient.nontrivial_iff.mpr hne
  exact IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective

/-- The maximal ideal of `R ⧸ 𝔪ⁿ` is nilpotent. -/
lemma isNilpotent_maximalIdeal_of_quotient_pow [IsLocalRing R] (n : ℕ) :
    letI := isLocalRing_quotient_pow_maximalIdeal (R := R) n
    IsNilpotent (IsLocalRing.maximalIdeal (R ⧸ (IsLocalRing.maximalIdeal R ^ (n + 1)))) := by
  letI := isLocalRing_quotient_pow_maximalIdeal (R := R) n
  refine ⟨n + 1, ?_⟩
  have h1 : IsLocalRing.maximalIdeal (R ⧸ (IsLocalRing.maximalIdeal R ^ (n + 1))) ≤
      Ideal.map (Ideal.Quotient.mk (IsLocalRing.maximalIdeal R ^ (n + 1)))
        (IsLocalRing.maximalIdeal R) := by
    intro x hx
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
    by_cases hy : y ∈ IsLocalRing.maximalIdeal R
    · exact Ideal.mem_map_of_mem _ hy
    · have hu : IsUnit (Ideal.Quotient.mk (IsLocalRing.maximalIdeal R ^ (n + 1)) y) :=
        (IsLocalRing.notMem_maximalIdeal.mp hy).map _
      exact absurd hx (IsLocalRing.notMem_maximalIdeal.mpr hu)
  have h2 : (Ideal.map (Ideal.Quotient.mk (IsLocalRing.maximalIdeal R ^ (n + 1)))
      (IsLocalRing.maximalIdeal R)) ^ (n + 1) = ⊥ := by
    rw [← Ideal.map_pow, Ideal.map_quotient_self]
  have h3 := Ideal.pow_right_mono h1 (n + 1)
  rw [h2] at h3
  simpa using le_bot_iff.mp h3

/-- `R ⧸ 𝔪ⁿ` is an Artinian ring (Hopkins–Levitzki). -/
lemma isArtinianRing_quotient_pow_maximalIdeal [IsLocalRing R] [IsNoetherianRing R] (n : ℕ) :
    IsArtinianRing (R ⧸ (IsLocalRing.maximalIdeal R ^ (n + 1))) := by
  letI := isLocalRing_quotient_pow_maximalIdeal (R := R) n
  rw [isArtinianRing_iff_isNilpotent_maximalIdeal]
  exact isNilpotent_maximalIdeal_of_quotient_pow n

/-- A finite power of `R ⧸ 𝔪ⁿ` is Artinian as an `R`-module. -/
lemma isArtinian_pi_quotient_pow_maximalIdeal [IsLocalRing R] [IsNoetherianRing R]
    {ι : Type*} [Finite ι] (n : ℕ) :
    IsArtinian R (ι → (R ⧸ (IsLocalRing.maximalIdeal R ^ (n + 1)))) := by
  haveI := isArtinianRing_quotient_pow_maximalIdeal (R := R) n
  haveI : IsArtinian R (R ⧸ (IsLocalRing.maximalIdeal R ^ (n + 1))) := by
    refine isArtinian_of_surjective_algebraMap
      (R := R ⧸ (IsLocalRing.maximalIdeal R ^ (n + 1)))
      (M := R ⧸ (IsLocalRing.maximalIdeal R ^ (n + 1))) (S := R) ?_
    rw [Ideal.Quotient.algebraMap_eq]
    exact Ideal.Quotient.mk_surjective
  infer_instance

variable {ι : Type*} [Fintype ι]

/-- The submodule of vectors all of whose coordinates lie in `J`. -/
def piCoordIdeal (J : Ideal R) : Submodule R (ι → R) :=
  ⨅ i : ι, Submodule.comap (LinearMap.proj i : (ι → R) →ₗ[R] R) (J : Submodule R R)

omit [Fintype ι] in
lemma mem_piCoordIdeal {J : Ideal R} {a : ι → R} :
    a ∈ (piCoordIdeal J : Submodule R (ι → R)) ↔ ∀ i, a i ∈ J := by
  simp [piCoordIdeal, Submodule.mem_iInf]

omit [Fintype ι] in
/-- **Mittag-Leffler stabilisation at one level**. -/
lemma exists_stabilizes_sup_piCoordIdeal (J : Ideal R)
    (hart : IsArtinian R (ι → (R ⧸ J)))
    (N : ℕ → Submodule R (ι → R)) (hanti : Antitone N) :
    ∃ m₀ : ℕ, ∀ m, m₀ ≤ m → N m ⊔ piCoordIdeal J = N m₀ ⊔ piCoordIdeal J := by
  haveI := hart
  set q : (ι → R) →ₗ[R] (ι → (R ⧸ J)) :=
    LinearMap.pi (fun i => (J : Submodule R R).mkQ.comp (LinearMap.proj i)) with hq
  have hker : LinearMap.ker q = piCoordIdeal J := by
    ext a
    simp only [hq, LinearMap.mem_ker, funext_iff, LinearMap.pi_apply, LinearMap.comp_apply,
      LinearMap.proj_apply, Submodule.mkQ_apply, Pi.zero_apply,
      Submodule.Quotient.mk_eq_zero, mem_piCoordIdeal]
  have hmono : Monotone (fun m => OrderDual.toDual (Submodule.map q (N m))) := by
    intro p r hpr
    exact Submodule.map_mono (hanti hpr)
  obtain ⟨m₀, hm₀⟩ := IsArtinian.monotone_stabilizes ⟨_, hmono⟩
  refine ⟨m₀, fun m hm => ?_⟩
  have h : Submodule.map q (N m) = Submodule.map q (N m₀) := by
    have := (hm₀ m hm).symm
    simpa using this
  have h2 := congrArg (Submodule.comap q) h
  rwa [Submodule.comap_map_eq, Submodule.comap_map_eq, hker] at h2

/-- **The pro-limit step**: an antitone chain `N n` of submodules of `ι → R`,
each containing the vectors with coordinates in `𝔪ⁿ⁺¹` and each containing a
unimodular vector, has a unimodular vector in its intersection. (The
`F`-level twin of `Deformation.lean`'s `exists_unimodular_mem_iInf`.) -/
theorem exists_unimodular_mem_iInf_of_isAdicComplete [IsLocalRing R] [IsNoetherianRing R]
    (hcomp : IsAdicComplete (IsLocalRing.maximalIdeal R) R)
    (N : ℕ → Submodule R (ι → R)) (hanti : Antitone N)
    (hP : ∀ (n : ℕ) (x : ι → R),
      (∀ i, x i ∈ IsLocalRing.maximalIdeal R ^ (n + 1)) → x ∈ N n)
    (hne : ∀ n : ℕ, ∃ a ∈ N n, ∃ i, a i ∉ IsLocalRing.maximalIdeal R) :
    ∃ a : ι → R, (∀ n, a ∈ N n) ∧ ∃ i, a i ∉ IsLocalRing.maximalIdeal R := by
  classical
  set 𝔪 : Ideal R := IsLocalRing.maximalIdeal R with h𝔪
  have hstab : ∀ n : ℕ, ∃ m₀ : ℕ, n ≤ m₀ ∧
      ∀ m, m₀ ≤ m → N m ⊔ piCoordIdeal (𝔪 ^ (n + 1)) = N m₀ ⊔ piCoordIdeal (𝔪 ^ (n + 1)) := by
    intro n
    obtain ⟨m₀, hm₀⟩ := exists_stabilizes_sup_piCoordIdeal (𝔪 ^ (n + 1))
      (isArtinian_pi_quotient_pow_maximalIdeal (R := R) (ι := ι) n) N hanti
    refine ⟨max m₀ n, le_max_right _ _, fun m hm => ?_⟩
    rw [hm₀ m (le_trans (le_max_left _ _) hm), hm₀ _ (le_max_left _ _)]
  choose M hMge hMst using hstab
  set kk : ℕ → ℕ := fun j => (Finset.range (j + 1)).sup M with hk
  have hkM : ∀ j, M j ≤ kk j := fun j =>
    Finset.le_sup (f := M) (Finset.self_mem_range_succ j)
  have hkmono : Monotone kk := by
    intro p r hpr
    have hsub : Finset.range (p + 1) ⊆ Finset.range (r + 1) := by
      intro x hx
      simp only [Finset.mem_range] at hx ⊢
      omega
    exact Finset.sup_mono hsub
  have hkge : ∀ j, j ≤ kk j := fun j => le_trans (hMge j) (hkM j)
  have step : ∀ (j : ℕ) (x : ι → R), ∃ y : ι → R,
      x ∈ N (kk j) → (y ∈ N (kk (j + 1)) ∧ ∀ i, y i - x i ∈ 𝔪 ^ (j + 1)) := by
    intro j x
    by_cases hx : x ∈ N (kk j)
    · have h1 : N (kk j) ⊔ piCoordIdeal (𝔪 ^ (j + 1)) =
          N (M j) ⊔ piCoordIdeal (𝔪 ^ (j + 1)) :=
        hMst j (kk j) (hkM j)
      have h2 : N (kk (j + 1)) ⊔ piCoordIdeal (𝔪 ^ (j + 1)) =
          N (M j) ⊔ piCoordIdeal (𝔪 ^ (j + 1)) :=
        hMst j (kk (j + 1)) (le_trans (hkM j) (hkmono (Nat.le_succ j)))
      have hxmem : x ∈ N (kk (j + 1)) ⊔ piCoordIdeal (𝔪 ^ (j + 1)) := by
        rw [h2, ← h1]
        exact Submodule.mem_sup_left hx
      obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.mp hxmem
      refine ⟨y, fun _ => ⟨hy, fun i => ?_⟩⟩
      have hzi : z i ∈ 𝔪 ^ (j + 1) := mem_piCoordIdeal.mp hz i
      have hyx : y i - x i = -(z i) := by
        rw [← hyz]
        simp
      rw [hyx]
      exact neg_mem hzi
    · exact ⟨x, fun hx' => absurd hx' hx⟩
  choose f hf using step
  obtain ⟨a₀, ha₀N, i₀, hi₀⟩ := hne (kk 0)
  set v : ℕ → (ι → R) := fun j => Nat.rec a₀ (fun j x => f j x) j with hv
  have hv0 : v 0 = a₀ := rfl
  have hvsucc : ∀ j, v (j + 1) = f j (v j) := fun _ => rfl
  have hvN : ∀ j, v j ∈ N (kk j) := by
    intro j
    induction j with
    | zero => exact ha₀N
    | succ j ih => rw [hvsucc j]; exact (hf j (v j) ih).1
  have hvstep : ∀ j i, v (j + 1) i - v j i ∈ 𝔪 ^ (j + 1) := by
    intro j i
    rw [hvsucc j]
    exact (hf j (v j) (hvN j)).2 i
  have hdiff : ∀ (i : ι) (p r : ℕ), p ≤ r → v r i - v p i ∈ 𝔪 ^ p := by
    intro i p r hpr
    induction r, hpr using Nat.le_induction with
    | base =>
      have hz : v p i - v p i = 0 := by ring
      rw [hz]
      exact Submodule.zero_mem _
    | succ r hpr ih =>
      have h1 : v (r + 1) i - v r i ∈ 𝔪 ^ p :=
        Ideal.pow_le_pow_right (le_trans hpr (Nat.le_succ r)) (hvstep r i)
      have hsplit : v (r + 1) i - v p i = (v (r + 1) i - v r i) + (v r i - v p i) := by ring
      rw [hsplit]
      exact Submodule.add_mem _ h1 ih
  have hprec : ∀ i : ι, ∃ L : R, ∀ n, v n i - L ∈ 𝔪 ^ n := by
    intro i
    have hc : ∀ {p r : ℕ}, p ≤ r →
        (fun n => v n i) p ≡ (fun n => v n i) r [SMOD (𝔪 ^ p • ⊤ : Submodule R R)] := by
      intro p r hpr
      rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top]
      have h := hdiff i p r hpr
      have hneg : v p i - v r i = -(v r i - v p i) := by ring
      rw [hneg]
      exact neg_mem h
    obtain ⟨L, hL⟩ := IsPrecomplete.prec hcomp.toIsPrecomplete hc
    refine ⟨L, fun n => ?_⟩
    have h := (SModEq.sub_mem).mp (hL n)
    rwa [smul_eq_mul, Ideal.mul_top] at h
  choose L hL using hprec
  refine ⟨L, fun n => ?_, i₀, ?_⟩
  · have h1 : L - v (n + 1) ∈ N n := by
      refine hP n _ fun i => ?_
      have h := hL i (n + 1)
      have h2 : (L - v (n + 1)) i = -(v (n + 1) i - L i) := by
        simp only [Pi.sub_apply]
        ring
      rw [h2]
      exact neg_mem h
    have h2 : v (n + 1) ∈ N n :=
      hanti (le_trans (Nat.le_succ n) (hkge (n + 1))) (hvN (n + 1))
    have h3 : L = (L - v (n + 1)) + v (n + 1) := by ring
    rw [h3]
    exact Submodule.add_mem _ h1 h2
  · intro hLm
    refine hi₀ ?_
    have h1 : v 1 i₀ - L i₀ ∈ 𝔪 ^ 1 := hL i₀ 1
    rw [pow_one] at h1
    have h2 : v 1 i₀ - v 0 i₀ ∈ 𝔪 ^ 1 := hvstep 0 i₀
    rw [pow_one] at h2
    have h3 : a₀ i₀ = L i₀ + (v 1 i₀ - L i₀) - (v 1 i₀ - v 0 i₀) := by
      rw [hv0]
      ring
    rw [h3]
    exact Submodule.sub_mem _ (Submodule.add_mem _ hLm h1) h2

end HilbertMittagLeffler

/-! ##### Extraction of the sign character at one finite level -/

/-- **The tame-at-`w` datum at one finite level, in coordinates** (the
`F`-level twin of `Deformation.lean`'s
`exists_signChar_of_quotient_isTameAtTwo`): the level-`J` quotient
character is `±1`-valued by `eq_pm_one_of_sq_eq_one_local`, its sign lifts
UNIQUELY to a multiplicative `ε : Γ F_w → {±1} ⊆ R` (uniqueness by
`eq_of_pm_of_sub_mem`, since `1 ≠ −1` modulo a proper ideal), and the
defining relation `∑ᵢ ρ(g)_{ji} aᵢ ≡ ε(g) a_j (mod J)` is read off on a
lift `a` of the coordinate vector of `π_J`, together with its
unimodularity. -/
lemma exists_hilbertSignChar_of_isHilbertTameAtTwo (ℓ : ℕ) [Fact ℓ.Prime]
    (hℓOdd : Odd ℓ) (F : Type u) [Field F] [NumberField F]
    {R : Type u} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    [IsLocalRing R] [Algebra ℤ_[ℓ] R]
    {ρ : FramedGaloisRep F R (Fin 2)}
    {J : Ideal R} (hJm : J ≤ IsLocalRing.maximalIdeal R)
    [IsLocalRing (R ⧸ J)] (hmk : Continuous (Ideal.Quotient.mk J))
    (h : IsHilbertHardlyRamified ℓ F (rank_finTwoPi (R ⧸ J))
      (framePushforward (Ideal.Quotient.mk J) hmk ρ))
    (w : HeightOneSpectrum (𝓞 F)) (hw : ((2 : ℕ) : 𝓞 F) ∈ w.asIdeal) :
    ∃ ε : Γ (w.adicCompletion F) → R,
      (∀ g, ε g = 1 ∨ ε g = -1) ∧
      (∀ g₁ g₂, ε (g₁ * g₂) = ε g₁ * ε g₂) ∧
      (∀ g ∈ localInertiaGroup w, ε g = 1) ∧
      ∃ a : Fin 2 → R, (∃ i, a i ∉ IsLocalRing.maximalIdeal R) ∧
        ∀ (g : Γ (w.adicCompletion F)) (j : Fin 2),
          (∑ i, (ρ.toLocal w g (Pi.single j 1)) i * a i) - ε g * a j ∈ J := by
  classical
  have h2R : IsUnit (2 : R) := isUnit_two_of_odd_padicAlgebra ℓ hℓOdd
  have hJtop : J ≠ ⊤ := by
    intro ht
    rw [ht, top_le_iff] at hJm
    exact (IsLocalRing.maximalIdeal.isMaximal R).ne_top hJm
  have h2Q : IsUnit (2 : R ⧸ J) := by
    have hh := h2R.map (Ideal.Quotient.mk J)
    rwa [map_ofNat] at hh
  obtain ⟨π', hπ'surj, δ', hδ'compat, hδ'ker, hδ'sq⟩ := h.isTameAtTwo w hw
  -- `π'` in coordinates
  obtain ⟨b, hb⟩ : ∃ b : Fin 2 → (R ⧸ J), ∀ i, b i = π' (Pi.single i 1) :=
    ⟨_, fun _ => rfl⟩
  have hπ'exp : ∀ v : Fin 2 → (R ⧸ J), π' v = ∑ i, v i * b i := by
    intro v
    have hv : v = ∑ i, v i • (Pi.single i 1 : Fin 2 → (R ⧸ J)) := by
      funext t
      simp [Finset.sum_apply, Pi.single_apply]
    conv_lhs => rw [hv]
    rw [map_sum]
    simp only [map_smul, smul_eq_mul, hb]
  -- `δ'` in coordinates
  obtain ⟨u, hu⟩ : ∃ u : Γ (w.adicCompletion F) → (R ⧸ J), ∀ g, u g = δ' g 1 :=
    ⟨_, fun _ => rfl⟩
  have hδ'exp : ∀ g x, δ' g x = x * u g := by
    intro g x
    have hx : (δ' g) (x • (1 : R ⧸ J)) = x • (δ' g) 1 := map_smul _ _ _
    rw [smul_eq_mul, mul_one, smul_eq_mul] at hx
    rw [hx, hu]
  have hu2 : ∀ g, u g * u g = 1 := by
    intro g
    have h1 : (δ' g * δ' g) 1 = (1 : Module.End (R ⧸ J) (R ⧸ J)) 1 := by rw [hδ'sq g]
    rw [Module.End.mul_apply, hδ'exp, hδ'exp, Module.End.one_apply] at h1
    linear_combination h1
  have humul : ∀ g₁ g₂, u (g₁ * g₂) = u g₁ * u g₂ := by
    intro g₁ g₂
    have h1 : δ' (g₁ * g₂) = δ' g₁ * δ' g₂ := map_mul _ _ _
    have h2 : δ' (g₁ * g₂) 1 = (δ' g₁ * δ' g₂) 1 := by rw [h1]
    rw [Module.End.mul_apply, hδ'exp, hδ'exp, hδ'exp] at h2
    linear_combination h2
  have hupm : ∀ g, u g = 1 ∨ u g = -1 := fun g =>
    eq_pm_one_of_sq_eq_one_local h2Q (hu2 g)
  -- the `±1`-valued lift
  obtain ⟨ε, hεdef⟩ : ∃ ε : Γ (w.adicCompletion F) → R,
      ∀ g, ε g = if u g = 1 then 1 else -1 := ⟨_, fun _ => rfl⟩
  have hεpm : ∀ g, ε g = 1 ∨ ε g = -1 := by
    intro g
    rw [hεdef]
    by_cases hg : u g = 1
    · exact Or.inl (if_pos hg)
    · exact Or.inr (if_neg hg)
  have hεmk : ∀ g, Ideal.Quotient.mk J (ε g) = u g := by
    intro g
    rw [hεdef]
    by_cases hg : u g = 1
    · rw [if_pos hg, map_one, hg]
    · rw [if_neg hg, map_neg, map_one, (hupm g).resolve_left hg]
  have hεmul : ∀ g₁ g₂, ε (g₁ * g₂) = ε g₁ * ε g₂ := by
    intro g₁ g₂
    have hprod : ε g₁ * ε g₂ = 1 ∨ ε g₁ * ε g₂ = -1 := by
      rcases hεpm g₁ with h1 | h1 <;> rcases hεpm g₂ with h2 | h2 <;> simp [h1, h2]
    refine eq_of_pm_of_sub_mem h2R hJtop (hεpm _) hprod ?_
    rw [← Ideal.Quotient.eq]
    rw [map_mul, hεmk, hεmk, hεmk, humul]
  have hεiner : ∀ g ∈ localInertiaGroup w, ε g = 1 := by
    intro g hg
    have hd : δ' g = 1 := hδ'ker hg
    have hug : u g = 1 := by rw [hu, hd]; rfl
    rw [hεdef, if_pos hug]
  -- the lifted vector
  choose a ha using fun i => Ideal.Quotient.mk_surjective (b i)
  have haunim : ∃ i, a i ∉ IsLocalRing.maximalIdeal R := by
    by_contra hcon
    have hall : ∀ i, a i ∈ IsLocalRing.maximalIdeal R := fun i => by
      by_contra hi
      exact hcon ⟨i, hi⟩
    obtain ⟨z, hz⟩ := hπ'surj 1
    choose z' hz' using fun i => Ideal.Quotient.mk_surjective (z i)
    have h1 : Ideal.Quotient.mk J (∑ i, z' i * a i) = 1 := by
      rw [map_sum]
      simp only [map_mul, hz', ha]
      rw [← hz]
      rw [hπ'exp z]
    have h2 : (1 : R) - (∑ i, z' i * a i) ∈ J := by
      rw [← Ideal.Quotient.eq, map_one, h1]
    have h3 : (∑ i, z' i * a i) ∈ IsLocalRing.maximalIdeal R :=
      Submodule.sum_mem _ fun i _ => Ideal.mul_mem_left _ _ (hall i)
    have h4 : (1 : R) ∈ IsLocalRing.maximalIdeal R := by
      have h5 := Submodule.add_mem (IsLocalRing.maximalIdeal R) (hJm h2) h3
      have h6 : (1 : R) - (∑ i, z' i * a i) + (∑ i, z' i * a i) = 1 := by ring
      rwa [h6] at h5
    exact (IsLocalRing.maximalIdeal.isMaximal R).ne_top ((Ideal.eq_top_iff_one _).mpr h4)
  refine ⟨ε, hεpm, hεmul, hεiner, a, haunim, ?_⟩
  intro g j
  have hsingle : (fun i => Ideal.Quotient.mk J ((Pi.single j 1 : Fin 2 → R) i)) =
      (Pi.single j 1 : Fin 2 → R ⧸ J) := by
    funext i
    simp [Pi.single_apply, apply_ite (Ideal.Quotient.mk J)]
  have hpf : (framePushforward (Ideal.Quotient.mk J) hmk ρ).toLocal w g
      (Pi.single j 1 : Fin 2 → R ⧸ J) =
      fun i => Ideal.Quotient.mk J ((ρ.toLocal w g (Pi.single j 1 : Fin 2 → R)) i) := by
    rw [GaloisRep.toLocal_apply, ← hsingle, framePushforward_apply, GaloisRep.toLocal_apply]
  have heq := hδ'compat g (Pi.single j 1 : Fin 2 → R ⧸ J)
  rw [hpf, hπ'exp, hπ'exp, hδ'exp] at heq
  have hsingsum : (∑ i, (Pi.single j 1 : Fin 2 → R ⧸ J) i * b i) = b j := by
    simp [Pi.single_apply, Finset.sum_ite_eq']
  rw [hsingsum] at heq
  rw [← Ideal.Quotient.eq, map_sum]
  simp only [map_mul, ha, hεmk]
  rw [heq, hb]
  ring

/-- **The tame quotient at a place over `2` is detected on the finite
levels** (PROVEN 2026-07-26, over the added hypothesis `Odd ℓ` — the ONE
clause of `isHilbertProLimitClause` that is a genuine pro-limit statement
rather than a congruence).

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

THE `ℓ = 2` QUESTION, SETTLED (2026-07-26). The previous owner recorded a
CAUTION here: `IsHilbertProLimitClause` carries only `[Fact ℓ.Prime]`,
whereas step 1 above needs `2` to be a unit, which over `ℚ` comes from the
ambient `hℓOdd : Odd ℓ` (`isUnit_two_of_oddPrime` — and the `ℚ`-level
docstring records that this is the ONE place oddness is used, and that it
is used essentially). The resolution, in three parts:

* *The gap is real, and it is exactly the residue characteristic `2`
  case.* `R` is a local ring, so `2 ∉ 𝔪_R` already makes `2` a unit and the
  argument below runs verbatim; nothing is needed beyond `IsUnit (2 : R)`.
  The genuinely open case is `ℓ = 2` WITH `2 ∈ 𝔪_R`, where `x² = 1` has the
  solutions `1 + v` for every `v ∈ 𝔪_R` with `v² + 2v = 0` — an infinite
  set in general (take `R = 𝔽̄₂⟦t⟧`, `v ∈ (t^{⌈n/2⌉})`), so the level
  characters `δ_I` are not drawn from a two-element set and steps 2–4 have
  nothing to propagate.
* *The escape through flatness does NOT exist.* At `ℓ = 2` the places over
  `ℓ` and over `2` coincide, so `IsHilbertHardlyRamified.isFlat` is
  available at the same `w`; but `δ` is UNRAMIFIED, so the rank-one
  quotient is an étale `Γ F_w`-module, its schematic prolongation is the
  corresponding étale group scheme over `𝒪_w`, and flatness is satisfied by
  EVERY value of `δ`. Flatness therefore imposes no constraint whatever on
  `δ` and supplies no substitute rigidity. (This is the standing
  `𝒪_w`-descent rule of this development read in the other direction:
  étale-by-étale is étale, so the flatness clause is blind to unramified
  twists.)
* *The clause is probably still TRUE at `ℓ = 2`, but not by anything
  available here.* With `δ` unramified and `δ² = 1`, `δ` factors through
  `Gal(F_w^{ur}/F_w)/2 = ℤ/2`, so the level datum is precisely the
  `R ⧸ 𝔪ⁿ⁺¹`-points of a FINITE TYPE `R`-scheme (unknowns: the two
  coordinates of `p`, the value `u = δ(Frob)`, and a unimodularity
  cofactor; equations: `u² = 1`, equivariance, and `∑ pᵢcᵢ = 1`). `R` is a
  complete Noetherian local ring, hence excellent and henselian, so
  Greenberg/strong Artin approximation gives an honest `R`-point out of the
  level points. That is a theorem far outside this development, and the
  elementary route below replaces it — at odd `ℓ` — by the observation that
  fixing `ε` makes the fibres MODULES, where Artinian Mittag-Leffler is
  free. So the hypothesis added here is a limitation of the PROOF, not a
  claim that the clause fails at `ℓ = 2`.

THE REPAIR, AND WHY IT COSTS NOTHING DOWNSTREAM. `Odd ℓ` is added to this
theorem and to `isHilbertProLimitClause`; the CLAUSE
`IsHilbertProLimitClause` itself is unchanged, so the Schlessinger machine
`exists_isWeaklyUniversal_hilbertDeformationDatum_of_clauses`, which
consumes it as a hypothesis, is untouched. The single call site is inside
`exists_isWeaklyUniversal_hilbertDeformationDatum`, which already carries
`hℓ5 : 5 ≤ ℓ`, and `Odd ℓ` follows from it by
`Nat.Prime.odd_of_ne_two`. No signature outside this pair changes. This
mirrors the sibling `isHilbertFibreProductClause ℓ hℓ5 F`, which already
takes an `ℓ`-hypothesis for the same kind of reason.

FAITHFULNESS: the inertia quantifier is inside `δ.ker` and must stay
there. `δ` is UNRAMIFIED, not trivial, and widening `localInertiaGroup w`
to all of `Γ F_w` makes the statement false for every unramified
quadratic twist — the standing rule of this development.

References: Mazur, *Deforming Galois representations*, MSRI Publ. 16
(1989), §1.2; Conrad–Diamond–Taylor, JAMS 12 (1999), §2; Grothendieck,
EGA III 5.4.1. -/
theorem isHilbertTameAtTwo_of_forall_isOpen_quotient (ℓ : ℕ) [Fact ℓ.Prime]
    (hℓOdd : Odd ℓ) (F : Type u) [Field F] [NumberField F]
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
      ∀ g : Γ (w.adicCompletion F), δ g * δ g = 1 := by
  classical
  haveI := hcomplete
  have h2R : IsUnit (2 : R) := isUnit_two_of_odd_padicAlgebra ℓ hℓOdd
  have hcont : ∀ Jd : Ideal R, Continuous (Ideal.Quotient.mk Jd) :=
    fun _ => continuous_quot_mk
  have hpow : ∀ n : ℕ, IsOpen ((IsLocalRing.maximalIdeal R ^ n : Ideal R) : Set R) :=
    (isAdic_iff.mp hadic).1
  have hle : ∀ n : ℕ, (IsLocalRing.maximalIdeal R ^ (n + 1) : Ideal R) ≤
      IsLocalRing.maximalIdeal R := fun n => Ideal.pow_le_self (Nat.succ_ne_zero n)
  have hsep : ∀ x : R,
      (∀ n : ℕ, x ∈ (IsLocalRing.maximalIdeal R ^ (n + 1) : Ideal R)) → x = 0 := by
    intro x hx
    refine IsHausdorff.haus
      (inferInstance : IsHausdorff (IsLocalRing.maximalIdeal R) R) _ fun n => ?_
    rw [SModEq.zero, smul_eq_mul, Ideal.mul_top]
    cases n with
    | zero => simp
    | succ m => exact hx m
  -- the matrix entries of `ρ` at `w`
  obtain ⟨mat, hmatdef⟩ : ∃ mat : Γ (w.adicCompletion F) → Fin 2 → Fin 2 → R,
      ∀ g j i, mat g j i = (ρ.toLocal w g (Pi.single j 1 : Fin 2 → R)) i :=
    ⟨_, fun _ _ _ => rfl⟩
  have hcoord : ∀ (g : Γ (w.adicCompletion F)) (v : Fin 2 → R) (i : Fin 2),
      (ρ.toLocal w g v) i = ∑ j, v j * mat g j i := by
    intro g v i
    have hv : v = ∑ j, v j • (Pi.single j 1 : Fin 2 → R) := by
      funext t
      simp [Finset.sum_apply, Pi.single_apply]
    conv_lhs => rw [hv]
    rw [map_sum]
    simp only [Finset.sum_apply, map_smul, Pi.smul_apply, smul_eq_mul, hmatdef]
  -- the set of sign characters realised at each level
  obtain ⟨Real, hReal⟩ : ∃ Real : ℕ → (Γ (w.adicCompletion F) → R) → Prop,
      ∀ n ε, Real n ε ↔
        ((∀ g, ε g = 1 ∨ ε g = -1) ∧
         (∀ g₁ g₂, ε (g₁ * g₂) = ε g₁ * ε g₂) ∧
         (∀ g ∈ localInertiaGroup w, ε g = 1) ∧
         ∃ a : Fin 2 → R, (∃ i, a i ∉ IsLocalRing.maximalIdeal R) ∧
           ∀ g j, (∑ i, mat g j i * a i) - ε g * a j ∈
             (IsLocalRing.maximalIdeal R ^ (n + 1) : Ideal R)) :=
    ⟨_, fun _ _ => Iff.rfl⟩
  have hlevel : ∀ n : ℕ, ∃ ε, Real n ε := by
    intro n
    haveI := isLocalRing_quotient_pow_maximalIdeal (R := R) n
    obtain ⟨ε, h1, h2, h3, a, h4, h5⟩ :=
      exists_hilbertSignChar_of_isHilbertTameAtTwo ℓ hℓOdd F (hle n) (hcont _)
        (hq _ (hpow (n + 1)) (hcont _)) w hw
    refine ⟨ε, (hReal n ε).mpr ⟨h1, h2, h3, a, h4, ?_⟩⟩
    intro g j
    simpa only [hmatdef] using h5 g j
  have hReal_anti : ∀ {p r : ℕ}, p ≤ r → ∀ ε, Real r ε → Real p ε := by
    intro p r hpr ε hε
    obtain ⟨h1, h2, h3, a, h4, h5⟩ := (hReal r ε).mp hε
    exact (hReal p ε).mpr ⟨h1, h2, h3, a, h4, fun g j =>
      Ideal.pow_le_pow_right (by omega) (h5 g j)⟩
  -- at most two characters occur at level one
  have hthree : ∀ ε₁ ε₂ ε₃, Real 0 ε₁ → Real 0 ε₂ → Real 0 ε₃ →
      ε₁ ≠ ε₂ → ε₁ ≠ ε₃ → ε₂ ≠ ε₃ → False := by
    intro ε₁ ε₂ ε₃ hr₁ hr₂ hr₃ n12 n13 n23
    haveI : (IsLocalRing.maximalIdeal R).IsMaximal := IsLocalRing.maximalIdeal.isMaximal R
    letI : Field (R ⧸ IsLocalRing.maximalIdeal R) := Ideal.Quotient.field _
    have h2F : IsUnit (2 : R ⧸ IsLocalRing.maximalIdeal R) := by
      have hh := h2R.map (Ideal.Quotient.mk (IsLocalRing.maximalIdeal R))
      rwa [map_ofNat] at hh
    have hrel : ∀ (ε : Γ (w.adicCompletion F) → R) (a : Fin 2 → R),
        (∀ g j, (∑ i, mat g j i * a i) - ε g * a j ∈
          (IsLocalRing.maximalIdeal R ^ (0 + 1) : Ideal R)) →
        ∀ g j, ∑ i, Ideal.Quotient.mk (IsLocalRing.maximalIdeal R) (mat g j i) *
            Ideal.Quotient.mk (IsLocalRing.maximalIdeal R) (a i) =
          Ideal.Quotient.mk (IsLocalRing.maximalIdeal R) (ε g) *
            Ideal.Quotient.mk (IsLocalRing.maximalIdeal R) (a j) := by
      intro ε a he g j
      have hm := he g j
      rw [pow_one] at hm
      have h0 : Ideal.Quotient.mk (IsLocalRing.maximalIdeal R)
          ((∑ i, mat g j i * a i) - ε g * a j) = 0 :=
        (Ideal.Quotient.eq_zero_iff_mem).mpr hm
      rw [map_sub, map_sum] at h0
      simp only [map_mul] at h0
      exact sub_eq_zero.mp h0
    have hnz : ∀ (a : Fin 2 → R), (∃ i, a i ∉ IsLocalRing.maximalIdeal R) →
        (fun i => Ideal.Quotient.mk (IsLocalRing.maximalIdeal R) (a i)) ≠ 0 := by
      rintro a ⟨i, hi⟩ hcon
      exact hi ((Ideal.Quotient.eq_zero_iff_mem).mp (congrFun hcon i))
    have hdist : ∀ (ε ε' : Γ (w.adicCompletion F) → R),
        (∀ g, ε g = 1 ∨ ε g = -1) → (∀ g, ε' g = 1 ∨ ε' g = -1) → ε ≠ ε' →
        ∃ g, Ideal.Quotient.mk (IsLocalRing.maximalIdeal R) (ε g) ≠
          Ideal.Quotient.mk (IsLocalRing.maximalIdeal R) (ε' g) := by
      intro ε ε' hp hp' hne
      obtain ⟨g, hg⟩ := Function.ne_iff.mp hne
      exact ⟨g, map_ne_map_of_pm_of_ne _ h2F (hp g) (hp' g) hg⟩
    obtain ⟨p₁, -, -, a₁, hu₁, e₁⟩ := (hReal 0 ε₁).mp hr₁
    obtain ⟨p₂, -, -, a₂, hu₂, e₂⟩ := (hReal 0 ε₂).mp hr₂
    obtain ⟨p₃, -, -, a₃, hu₃, e₃⟩ := (hReal 0 ε₃).mp hr₃
    exact false_of_three_quotient_chars
      (fun g j i => Ideal.Quotient.mk (IsLocalRing.maximalIdeal R) (mat g j i))
      (fun g => Ideal.Quotient.mk (IsLocalRing.maximalIdeal R) (ε₁ g))
      (fun g => Ideal.Quotient.mk (IsLocalRing.maximalIdeal R) (ε₂ g))
      (fun g => Ideal.Quotient.mk (IsLocalRing.maximalIdeal R) (ε₃ g))
      (fun i => Ideal.Quotient.mk (IsLocalRing.maximalIdeal R) (a₁ i))
      (fun i => Ideal.Quotient.mk (IsLocalRing.maximalIdeal R) (a₂ i))
      (fun i => Ideal.Quotient.mk (IsLocalRing.maximalIdeal R) (a₃ i))
      (hrel ε₁ a₁ e₁) (hrel ε₂ a₂ e₂) (hrel ε₃ a₃ e₃)
      (hnz a₁ hu₁) (hnz a₂ hu₂) (hnz a₃ hu₃)
      (hdist ε₁ ε₂ p₁ p₂ n12) (hdist ε₁ ε₃ p₁ p₃ n13) (hdist ε₂ ε₃ p₂ p₃ n23)
  -- one character is realised at EVERY level
  have hexistsEps : ∃ ε, ∀ n, Real n ε := by
    by_contra hcon
    have hfail : ∀ ε, ∃ n, ¬ Real n ε := by
      intro ε
      by_contra hε2
      refine hcon ⟨ε, fun n => ?_⟩
      by_contra hn
      exact hε2 ⟨n, hn⟩
    choose e he using hlevel
    obtain ⟨n₁, hn₁⟩ := hfail (e 0)
    obtain ⟨n₂, hn₂⟩ := hfail (e n₁)
    have hc1 : Real n₁ (e (max n₁ n₂)) := hReal_anti (le_max_left n₁ n₂) _ (he _)
    have hc2 : Real n₂ (e (max n₁ n₂)) := hReal_anti (le_max_right n₁ n₂) _ (he _)
    have hne1 : e 0 ≠ e n₁ := fun h => hn₁ (by rw [h]; exact he n₁)
    have hne2 : e 0 ≠ e (max n₁ n₂) := fun h => hn₁ (by rw [h]; exact hc1)
    have hne3 : e n₁ ≠ e (max n₁ n₂) := fun h => hn₂ (by rw [h]; exact hc2)
    exact hthree (e 0) (e n₁) (e (max n₁ n₂))
      (hReal_anti (Nat.zero_le _) _ (he 0)) (hReal_anti (Nat.zero_le _) _ (he n₁))
      (hReal_anti (Nat.zero_le _) _ (he _)) hne1 hne2 hne3
  obtain ⟨ε, hεall⟩ := hexistsEps
  obtain ⟨hεpm, hεmul, hεiner, -⟩ := (hReal 0 ε).mp (hεall 0)
  -- the eigenvector modules
  obtain ⟨Φ, hΦdef⟩ :
      ∃ Φ : Γ (w.adicCompletion F) → Fin 2 → ((Fin 2 → R) →ₗ[R] R),
      ∀ g j, Φ g j = (∑ i, (mat g j i) • (LinearMap.proj i : (Fin 2 → R) →ₗ[R] R))
        - (ε g) • (LinearMap.proj j : (Fin 2 → R) →ₗ[R] R) := ⟨_, fun _ _ => rfl⟩
  have hΦapp : ∀ g j (x : Fin 2 → R), Φ g j x = (∑ i, mat g j i * x i) - ε g * x j := by
    intro g j x
    rw [hΦdef]
    simp [LinearMap.sub_apply, LinearMap.smul_apply,
      LinearMap.proj_apply, smul_eq_mul]
  obtain ⟨N, hNdef⟩ : ∃ N : ℕ → Submodule R (Fin 2 → R), ∀ n, N n =
      ⨅ (g : Γ (w.adicCompletion F)) (j : Fin 2), Submodule.comap (Φ g j)
        ((IsLocalRing.maximalIdeal R ^ (n + 1) : Ideal R) : Submodule R R) :=
    ⟨_, fun _ => rfl⟩
  have hNmem : ∀ (n : ℕ) (x : Fin 2 → R), x ∈ N n ↔
      ∀ g j, (∑ i, mat g j i * x i) - ε g * x j ∈
        (IsLocalRing.maximalIdeal R ^ (n + 1) : Ideal R) := by
    intro n x
    rw [hNdef]
    simp only [Submodule.mem_iInf, Submodule.mem_comap, hΦapp]
  have hNanti : Antitone N := by
    intro p r hpr x hx
    rw [hNmem] at hx ⊢
    exact fun g j => Ideal.pow_le_pow_right (by omega) (hx g j)
  have hNP : ∀ (n : ℕ) (x : Fin 2 → R),
      (∀ i, x i ∈ IsLocalRing.maximalIdeal R ^ (n + 1)) → x ∈ N n := by
    intro n x hx
    rw [hNmem]
    intro g j
    exact Submodule.sub_mem _
      (Submodule.sum_mem _ fun i _ => Ideal.mul_mem_left _ _ (hx i))
      (Ideal.mul_mem_left _ _ (hx j))
  have hNne : ∀ n : ℕ, ∃ a ∈ N n, ∃ i, a i ∉ IsLocalRing.maximalIdeal R := by
    intro n
    obtain ⟨-, -, -, a, hua, hra⟩ := (hReal n ε).mp (hεall n)
    exact ⟨a, (hNmem n a).mpr hra, hua⟩
  obtain ⟨a, haN, i₀, hi₀⟩ :=
    exists_unimodular_mem_iInf_of_isAdicComplete hcomplete N hNanti hNP hNne
  have hrel : ∀ g j, (∑ i, mat g j i * a i) = ε g * a j := by
    intro g j
    exact sub_eq_zero.mp (hsep _ fun n => (hNmem n a).mp (haN n) g j)
  obtain ⟨u₀, hu₀⟩ : IsUnit (a i₀) := IsLocalRing.notMem_maximalIdeal.mp hi₀
  have hu₀inv : (↑u₀ : R) * ↑u₀⁻¹ = 1 := u₀.mul_inv
  -- the projection
  obtain ⟨π, hπdef⟩ : ∃ π : (Fin 2 → R) →ₗ[R] R,
    π = ∑ i, (a i) • (LinearMap.proj i : (Fin 2 → R) →ₗ[R] R) := ⟨_, rfl⟩
  have hπapp : ∀ v : Fin 2 → R, π v = ∑ i, a i * v i := by
    intro v
    rw [hπdef]
    simp [LinearMap.smul_apply, LinearMap.proj_apply, smul_eq_mul]
  have hπsurj : Function.Surjective π := by
    intro c
    refine ⟨Pi.single i₀ (c * ↑u₀⁻¹), ?_⟩
    rw [hπapp]
    have hs : ∑ i, a i * (Pi.single i₀ (c * ↑u₀⁻¹) : Fin 2 → R) i
        = a i₀ * (c * ↑u₀⁻¹) := by
      simp [Pi.single_apply, mul_ite, mul_zero, Finset.sum_ite_eq']
    rw [hs, ← hu₀]
    linear_combination c * hu₀inv
  -- the sign character is continuous
  have hεval : ∀ g, ε g = (∑ i, mat g i₀ i * a i) * ↑u₀⁻¹ := by
    intro g
    rw [hrel g i₀, ← hu₀]
    linear_combination (-(ε g)) * hu₀inv
  letI := moduleTopology R (Module.End R (Fin 2 → R))
  letI := IsModuleTopology.toContinuousAdd R (Module.End R (Fin 2 → R))
  have hevcont : Continuous (fun f : Module.End R (Fin 2 → R) =>
      π (f (Pi.single i₀ 1))) := by
    refine IsModuleTopology.continuous_of_linearMap
      ({ toFun := fun f : Module.End R (Fin 2 → R) => π (f (Pi.single i₀ 1))
         map_add' := by intro f₁ f₂; simp
         map_smul' := by intro c f; simp } : Module.End R (Fin 2 → R) →ₗ[R] R)
  have hρcont : Continuous (fun g : Γ (w.adicCompletion F) =>
      (ρ.toLocal w g : Module.End R (Fin 2 → R))) :=
    ContinuousMonoidHom.continuous_toFun _
  have hεcont : Continuous ε := by
    have h1 : Continuous (fun g : Γ (w.adicCompletion F) =>
        π (ρ.toLocal w g (Pi.single i₀ 1))) := hevcont.comp hρcont
    have h2 : Continuous (fun g : Γ (w.adicCompletion F) =>
        π (ρ.toLocal w g (Pi.single i₀ 1)) * (↑u₀⁻¹ : R)) :=
      h1.mul continuous_const
    refine h2.congr fun g => ?_
    rw [hεval g, hπapp]
    congr 1
    exact Finset.sum_congr rfl fun i _ => by rw [hmatdef]; ring
  have hε1 : ε 1 = 1 := by
    have h := hεmul 1 1
    rw [mul_one] at h
    rcases hεpm 1 with h1 | h1
    · exact h1
    · rw [h1] at h
      exact absurd (by linear_combination -h : (1 : R) = -1)
        (one_ne_neg_one_of_two_isUnit h2R)
  -- assembly
  letI := moduleTopology R (Module.End R R)
  letI := IsModuleTopology.toContinuousAdd R (Module.End R R)
  refine ⟨π, hπsurj,
    { toMonoidHom :=
        { toFun := fun g => algebraMap R (Module.End R R) (ε g)
          map_one' := by rw [hε1, map_one]
          map_mul' := fun g₁ g₂ => by rw [hεmul, map_mul] }
      continuous_toFun := (IsModuleTopology.continuous_of_linearMap
        (Algebra.linearMap R (Module.End R R))).comp hεcont }, ?_, ?_, ?_⟩
  · intro g v
    show π (ρ.toLocal w g v) = algebraMap R (Module.End R R) (ε g) (π v)
    rw [Module.algebraMap_end_apply, smul_eq_mul, hπapp, hπapp]
    have hc0 := hcoord g v 0
    have hc1 := hcoord g v 1
    have hr0 := hrel g 0
    have hr1 := hrel g 1
    simp only [Fin.sum_univ_two] at hc0 hc1 hr0 hr1 ⊢
    rw [hc0, hc1]
    linear_combination (v 0) * hr0 + (v 1) * hr1
  · intro σ hσ
    have hs : algebraMap R (Module.End R R) (ε σ) = 1 := by
      rw [hεiner σ hσ, map_one]
    exact hs
  · intro g'
    show algebraMap R (Module.End R R) (ε g') * algebraMap R (Module.End R R) (ε g') = 1
    rw [← map_mul]
    rcases hεpm g' with h | h <;> rw [h] <;> simp

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
* *tameness at `w ∣ 2`*: `isHilbertTameAtTwo_of_forall_isOpen_quotient`,
  the one genuine pro-limit statement, PROVEN 2026-07-26. It is the reason
  this theorem carries `hℓOdd : Odd ℓ` — see that leaf's docstring for the
  `ℓ = 2` analysis and for why the repair costs nothing downstream.

The hypothesis is stated over ALL open ideals rather than over the powers
`𝔪ⁿ` because that is the form `IsFlatAt` consumes; `hadic` makes the two
interchangeable. -/
theorem isHilbertProLimitClause (ℓ : ℕ) [Fact ℓ.Prime] (hℓOdd : Odd ℓ)
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
    exact isHilbertTameAtTwo_of_forall_isOpen_quotient ℓ hℓOdd F hadic hcomplete hq w hw

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
* `HilbertDeformationDatum.isWeaklyUniversal_of_finiteFrames` (PROVEN
  2026-07-26) — the LIMIT passage, from the finite discrete test objects
  the construction classifies to the whole of Mazur's category. The
  `ℚ`-level twin is `isWeaklyUniversalOnIdentifiedFrames_of_finite`.

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

/-! #### The 2026-07-26 CONSTRUCTION cut at the `F` level: a level system,
and its profinite limit

`exists_universalFrame_profinite_hilbert_of_clauses` below is proven as an
ASSEMBLY over the two declarations in this subsection, cut 2026-07-26 along
exactly the seam `Deformation.lean` uses at the `ℚ` level (its
`exists_levelIdealSystem_of_deformationCondition` /
`exists_universalFrame_profinite_of_levelIdealSystem` pair) — ARITHMETIC on
one side, pure algebra and topology on the other:

* `exists_hilbertLevelIdealSystem_of_clauses` (PROVEN 2026-07-26 as an
  assembly over four sharp leaves; was a single opaque leaf) — all of the
  arithmetic. It produces one "tautological" coefficient ring `P`, a
  matrix-valued function `M : Γ F → M₂(P)` and a downward-directed family
  `𝒥` of ideals of `P` such that every `P ⧸ J` is a FINITE LOCAL level
  carrying a hardly ramified framed representation with matrices `M mod J`,
  together with the two bookkeeping clauses that make `P` universal
  (`hclass`) and rigid (`hsep`).
* `exists_universalFrame_profinite_hilbert_of_levelIdealSystem` (PROVEN) —
  no arithmetic at all beyond the functoriality clause `hbase` it is handed.
  It forms the inverse limit `R = lim_{J ∈ 𝒥} P ⧸ J` through
  `LevelLimit.lean`, which is profinite because the levels are finite and
  `𝒥` is directed, and reads all five conclusion clauses off the limit.

WHY THIS CUT IS CHEAPER HERE THAN AT THE `ℚ` LEVEL, and why one of the
`ℚ`-level leaves has no twin. `Deformation.lean` needs a THIRD declaration,
`isStrictlyUniversalOnFrames_of_levelSystem`, because its notion of
universality identifies a test object's residual frame STRICTLY with the
model frame, while a test object arrives only RESIDUALLY identified: the
gap is closed by lifting a matrix `C ∈ GL₂(k)` to `GL₂(A)` and conjugating.
This module's `IsHilbertWeaklyUniversalOnFiniteFrames` is CHARPOLY-ONLY, and
characteristic polynomials are conjugation-invariant, so no such bridge is
needed — the whole conjugation is absorbed into the arithmetic leaf, where
it is discharged by `hrig` (`isHilbertResidualRigidityClause`, PROVEN
above). Concretely, the classification clause of the level system below is
stated as an equality of CHARPOLYS, not of matrices, in both its hypothesis
and its conclusion; that single change is what removes the third leaf.

THE TRACE-GENERATION STRENGTHENING WAS CONSIDERED AND DECLINED (2026-07-26,
flt-lean-163). Because `LevelLimit.ofP` has DENSE range, building `P` on
generators of a prescribed kind would let a "the closure of the subring
generated by … is `⊤`" clause be read straight off the presentation, and
that is exactly the shape of `HilbertDeformationDatum.IsTraceGenerated`. It
was declined because the sibling it would have closed,
`exists_isWeaklyUniversal_isTraceGenerated_hilbertDeformationDatum`, is
ALREADY PROVEN — by the trace-DESCENT route
(`exists_hilbertTraceDescent`, over `exists_isLocalRing_hilbertTraceSubring`
and `exists_framedGaloisRep_hilbertTraceSubring`), which replaces a datum by
its trace subring after the fact. Taking the strengthening here would
therefore buy nothing and would import that same Carayol-style
"conjugate into `M₂(C)`" obligation into the level-system leaf, where it
would be hidden rather than named. -/

/-- **A ring map out of `ℤ_ℓ` into a FINITE ring is unique** (PROVEN; a
local copy of `Deformation.lean`'s `ringHom_padicInt_ext_finite`, which
lives DOWNSTREAM of this module — the ninth such copy, see the duplication
note at the head of the `F`-level Schlessinger material).

`ker f` is a non-zero ideal of the DVR `ℤ_ℓ` (else `ℤ_ℓ` embeds in a finite
ring), hence `(ℓ^n)`, so `f` factors through `ℤ_ℓ ⧸ (ℓ^N)` for a common
`N`, where `ℤ` is dense (`PadicInt.appr_spec`) and a ring map is pinned by
its value on `1`.

It is what lets the level system's classification clause be applied to a
test object of `IsHilbertWeaklyUniversalOnFiniteFrames`, whose `πA` is not
assumed to be a `ℤ_ℓ`-algebra map. -/
lemma hilbertRingHom_padicInt_ext_finite {ℓ : ℕ} [Fact ℓ.Prime]
    {A : Type*} [CommRing A] [Finite A] (f g : ℤ_[ℓ] →+* A) : f = g := by
  classical
  have key : ∀ h : ℤ_[ℓ] →+* A, ∃ n : ℕ, h ((ℓ : ℤ_[ℓ]) ^ n) = 0 := by
    intro h
    by_cases hb : RingHom.ker h = ⊥
    · exfalso
      haveI : Finite ℤ_[ℓ] :=
        Finite.of_injective h ((RingHom.injective_iff_ker_eq_bot h).mpr hb)
      exact _root_.not_finite ℤ_[ℓ]
    · obtain ⟨n, hn⟩ := PadicInt.ideal_eq_span_pow_p hb
      refine ⟨n, RingHom.mem_ker.mp ?_⟩
      rw [hn]
      exact Ideal.mem_span_singleton_self _
  obtain ⟨n, hn⟩ := key f
  obtain ⟨m, hm⟩ := key g
  set N := max n m with hN
  have hfN : f ((ℓ : ℤ_[ℓ]) ^ N) = 0 := by
    have hsplit : (ℓ : ℤ_[ℓ]) ^ N = (ℓ : ℤ_[ℓ]) ^ n * (ℓ : ℤ_[ℓ]) ^ (N - n) := by
      rw [← pow_add]; congr 1; omega
    rw [hsplit, map_mul, hn, zero_mul]
  have hgN : g ((ℓ : ℤ_[ℓ]) ^ N) = 0 := by
    have hsplit : (ℓ : ℤ_[ℓ]) ^ N = (ℓ : ℤ_[ℓ]) ^ m * (ℓ : ℤ_[ℓ]) ^ (N - m) := by
      rw [← pow_add]; congr 1; omega
    rw [hsplit, map_mul, hm, zero_mul]
  ext x
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.mp (PadicInt.appr_spec N x)
  have hf : f x = ((PadicInt.appr x N : ℕ) : A) := by
    have hfx := congrArg f hc
    rw [map_sub, map_mul, hfN, zero_mul, sub_eq_zero, map_natCast] at hfx
    exact hfx
  have hg : g x = ((PadicInt.appr x N : ℕ) : A) := by
    have hgx := congrArg g hc
    rw [map_sub, map_mul, hgN, zero_mul, sub_eq_zero, map_natCast] at hgx
    exact hgx
  rw [hf, hg]

/-- **The matrix of a pushed-forward frame is the entrywise image**
(PROVEN; the `F`-level twin of `Deformation.lean`'s
`toMatrix'_pushforwardFrame`, deliberately given a DIFFERENT name because
that module `public import`s this one into the same namespace).

The proof reads the `(i,j)` entry off `framePushforward_apply` at the
standard basis vector `Pi.single j 1`, whose `ψ`-image is again
`Pi.single j 1`; so the framing identification `A ⊗_B B² ≅ A²` never has to
be inverted. -/
lemma toMatrix'_framePushforward {F : Type u} [Field F] [NumberField F]
    {B : Type u} [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
    {A : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    (ψ : B →+* A) (hψ : Continuous ψ) (ρ : FramedGaloisRep F B (Fin 2))
    (g : Γ F) :
    LinearMap.toMatrix' (framePushforward ψ hψ ρ g) =
      (LinearMap.toMatrix' (ρ g)).map ⇑ψ := by
  ext i j
  have hsingle : (fun l => ψ ((Pi.single j (1 : B) : Fin 2 → B) l)) =
      (Pi.single j (1 : A) : Fin 2 → A) := by
    funext l
    simp [Pi.single_apply, apply_ite ψ]
  have hkey := congrFun (framePushforward_apply ψ hψ ρ g (Pi.single j (1 : B))) i
  rw [hsingle] at hkey
  rw [LinearMap.toMatrix'_apply, Matrix.map_apply, LinearMap.toMatrix'_apply]
  exact hkey

/-- **The charpoly of a framed representation is the charpoly of its
matrix** (PROVEN, pure bookkeeping): `LinearMap.charpoly` is basis-free and
`Matrix.toLin'` inverts `LinearMap.toMatrix'`.

This is the dictionary between the two languages the construction uses:
`HilbertDeformationDatum` and `IsHilbertWeaklyUniversalOnFiniteFrames`
speak of `LinearMap.charpoly`, while the level system carries MATRICES. -/
lemma charpoly_eq_charpoly_toMatrix' {F : Type u} [Field F] [NumberField F]
    {A : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    (ρ : FramedGaloisRep F A (Fin 2)) (g : Γ F) :
    (ρ g).charpoly = (LinearMap.toMatrix' (ρ g)).charpoly := by
  rw [← Matrix.charpoly_toLin', Matrix.toLin'_toMatrix']

/-! #### The `F`-level tautological frame ring (the CONSTRUCTION, 2026-07-26)

The declarations in this section are the `F`-level copy of
`Deformation.lean`'s `FrameRing` section. They may not be imported —
`Deformation.lean` is DOWNSTREAM of this module (it `public import`s it) —
so, as with the eight other helpers this module already re-derives for the
same reason, they are re-derived rather than shared. The copy is
mechanical: the construction is generic in the indexing GROUP, and the
only change is `Γ ℚ ↝ Γ F` throughout, together with the residual model
becoming `(ρbar.map (algebraMap ℚ F)).conj e0` rather than `ρbar.conj e0`.

THE HONEST REPAIR, recorded so it is not lost: this construction depends
on nothing about `ℚ` or `F` beyond the group, so the right fix is ONE
group-generic development in a module upstream of both this file and
`Deformation.lean`, consumed twice. That is a refactor of another owner's
file and is not taken here.

WHAT THIS BUYS. `exists_hilbertLevelIdealSystem_of_clauses` below was a
single opaque leaf carrying the whole Schlessinger/de Smit–Lenstra
construction. It is now an ASSEMBLY, proven outright, over exactly four
sharp leaves — and EVERY ONE of the four has a PROVEN `ℚ`-level twin in
`Deformation.lean`, so each is a mechanical port rather than new
mathematics:

| leaf here | proven `ℚ`-level twin |
| --- | --- |
| `hilbertFrameLevels_nonempty` | `frameLevels_nonempty` |
| `hilbertFrameLevels_directed` | `frameLevels_directed` |
| `hilbertFrameLevels_classification` | `frameLevels_classification` |
| `hilbertFrameRing_rigid` | `frameRing_rigid` |

Three of the eight conclusion clauses (`hker`, `hlev`, `hrep`) are
DEFINITIONAL for `hilbertFrameLevels`, and the residual charpoly clause is
`hilbertFrameMat_map_frameEv` followed by `LinearEquiv.charpoly_conj` —
which is where the charpoly-only formulation of
`IsHilbertWeaklyUniversalOnFiniteFrames` pays off, exactly as the section
preamble above predicted. -/

section HilbertFrameRing

-- The tautological ring and its evaluation maps are PURE ALGEBRA: they need
-- only the coefficient instances. The arithmetic instances (`NumberField F`,
-- and the finiteness/topology on `k`) are introduced further down, at the
-- first declaration that actually uses them, so that the unused-section-
-- variable linter stays quiet.
variable (ℓ : ℕ) [Fact ℓ.Prime] (F : Type u) [Field F]
variable (k : Type u) [Field k] [Algebra ℤ_[ℓ] k]

/-- Generator index of the `F`-level tautological frame ring. -/
abbrev HilbertFrameGen : Type u := (Γ F × Fin 2 × Fin 2) ⊕ k

/-- The free `F`-level tautological ring `ℤ_ℓ[X_{g,i,j}, T_x]`. -/
abbrev hilbertFramePoly : Type u := MvPolynomial (HilbertFrameGen F k) ℤ_[ℓ]

/-- The tautological matrix of `g` in the free ring. -/
noncomputable def hilbertFramePolyMat (g : Γ F) :
    Matrix (Fin 2) (Fin 2) (hilbertFramePoly ℓ F k) :=
  Matrix.of fun i j => MvPolynomial.X (Sum.inl (g, i, j))

/-- The tautological relations: Teichmüller multiplicativity and matrix
multiplicativity. -/
noncomputable def hilbertFrameRel : Ideal (hilbertFramePoly ℓ F k) :=
  Ideal.span
    ((Set.range fun q : k × k =>
        MvPolynomial.X (Sum.inr q.1) * MvPolynomial.X (Sum.inr q.2) -
          MvPolynomial.X (Sum.inr (q.1 * q.2))) ∪
      {MvPolynomial.X (Sum.inr (0 : k))} ∪
      {MvPolynomial.X (Sum.inr (1 : k)) - 1} ∪
      (Set.range fun q : Γ F × Γ F × Fin 2 × Fin 2 =>
        hilbertFramePolyMat ℓ F k (q.1 * q.2.1) q.2.2.1 q.2.2.2 -
          (hilbertFramePolyMat ℓ F k q.1 * hilbertFramePolyMat ℓ F k q.2.1)
            q.2.2.1 q.2.2.2) ∪
      (Set.range fun q : Fin 2 × Fin 2 =>
        hilbertFramePolyMat ℓ F k 1 q.1 q.2 -
          (1 : Matrix (Fin 2) (Fin 2) (hilbertFramePoly ℓ F k)) q.1 q.2))

/-- The `F`-level tautological frame ring `P`. -/
abbrev hilbertFrameRing : Type u := hilbertFramePoly ℓ F k ⧸ hilbertFrameRel ℓ F k

/-- Evaluation of the free tautological ring at a matrix family and a
Teichmüller family. -/
noncomputable def hilbertFramePolyEval {A : Type*} [CommRing A] [Algebra ℤ_[ℓ] A]
    (N : Γ F → Matrix (Fin 2) (Fin 2) A) (t : k → A) :
    hilbertFramePoly ℓ F k →+* A :=
  MvPolynomial.eval₂Hom (algebraMap ℤ_[ℓ] A)
    (Sum.elim (fun q : Γ F × Fin 2 × Fin 2 => N q.1 q.2.1 q.2.2) t)

omit [Field k] [Algebra ℤ_[ℓ] k] in
@[simp] lemma hilbertFramePolyEval_X_inl {A : Type*} [CommRing A] [Algebra ℤ_[ℓ] A]
    (N : Γ F → Matrix (Fin 2) (Fin 2) A) (t : k → A) (g : Γ F) (i j : Fin 2) :
    hilbertFramePolyEval ℓ F k N t (MvPolynomial.X (Sum.inl (g, i, j))) = N g i j := by
  simp [hilbertFramePolyEval]

omit [Field k] [Algebra ℤ_[ℓ] k] in
@[simp] lemma hilbertFramePolyEval_X_inr {A : Type*} [CommRing A] [Algebra ℤ_[ℓ] A]
    (N : Γ F → Matrix (Fin 2) (Fin 2) A) (t : k → A) (x : k) :
    hilbertFramePolyEval ℓ F k N t (MvPolynomial.X (Sum.inr x)) = t x := by
  simp [hilbertFramePolyEval]

-- NOTE: the `ℚ`-level `framePolyEval_comp_algebraMap` has deliberately NOT
-- been ported. Its only `ℚ`-level consumer is `frameEv_comp_algebraMap`, and
-- the corresponding clause is ABSENT from this module's level system: `k` is
-- FINITE here, so it receives exactly one ring map from `ℤ_ℓ`
-- (`hilbertRingHom_padicInt_ext_finite`) and the compatibility is automatic.
-- Porting it now would be free-floating code. `hilbertFrameLevels_classification`
-- will need it when it is proven; it is six lines and is re-derived then.

omit [Algebra ℤ_[ℓ] k] in
/-- The relations are killed by any multiplicative pair `(N, t)`. -/
lemma hilbertFrameRel_le_ker{A : Type*} [CommRing A] [Algebra ℤ_[ℓ] A]
    (N : Γ F → Matrix (Fin 2) (Fin 2) A) (t : k → A)
    (hNmul : ∀ g h, N (g * h) = N g * N h) (hN1 : N 1 = 1)
    (htmul : ∀ x y : k, t x * t y = t (x * y)) (ht0 : t 0 = 0) (ht1 : t 1 = 1) :
    hilbertFrameRel ℓ F k ≤ RingHom.ker (hilbertFramePolyEval ℓ F k N t) := by
  rw [hilbertFrameRel, Ideal.span_le]
  rintro q ((((⟨⟨x, y⟩, rfl⟩ | rfl) | rfl) | ⟨⟨g, h, i, j⟩, rfl⟩) | ⟨⟨i, j⟩, rfl⟩)
  · simp [SetLike.mem_coe, RingHom.mem_ker, htmul]
  · simp [SetLike.mem_coe, RingHom.mem_ker, ht0]
  · simp [SetLike.mem_coe, RingHom.mem_ker, ht1]
  · simp only [SetLike.mem_coe, RingHom.mem_ker, map_sub, hilbertFramePolyMat,
      Matrix.of_apply, Matrix.mul_apply, map_sum, map_mul,
      hilbertFramePolyEval_X_inl, hNmul, sub_eq_zero]
  · simp only [SetLike.mem_coe, RingHom.mem_ker, map_sub, hilbertFramePolyMat,
      Matrix.of_apply, hilbertFramePolyEval_X_inl, hN1, sub_eq_zero, Matrix.one_apply]
    split <;> simp

/-- The induced map on the tautological frame ring. -/
noncomputable def hilbertFrameEval {A : Type*} [CommRing A] [Algebra ℤ_[ℓ] A]
    (N : Γ F → Matrix (Fin 2) (Fin 2) A) (t : k → A)
    (hrel : hilbertFrameRel ℓ F k ≤ RingHom.ker (hilbertFramePolyEval ℓ F k N t)) :
    hilbertFrameRing ℓ F k →+* A :=
  Ideal.Quotient.lift _ (hilbertFramePolyEval ℓ F k N t)
    fun _ ha => RingHom.mem_ker.mp (hrel ha)

omit [Algebra ℤ_[ℓ] k] in
@[simp] lemma hilbertFrameEval_mk {A : Type*} [CommRing A] [Algebra ℤ_[ℓ] A]
    {N : Γ F → Matrix (Fin 2) (Fin 2) A} {t : k → A}
    (hrel : hilbertFrameRel ℓ F k ≤ RingHom.ker (hilbertFramePolyEval ℓ F k N t))
    (x : hilbertFramePoly ℓ F k) :
    hilbertFrameEval ℓ F k N t hrel (Ideal.Quotient.mk (hilbertFrameRel ℓ F k) x) =
      hilbertFramePolyEval ℓ F k N t x :=
  Ideal.Quotient.lift_mk _ _ _

/-- The matrix family `M : Γ F → M₂(P)` of the level system. -/
noncomputable def hilbertFrameMat (g : Γ F) :
    Matrix (Fin 2) (Fin 2) (hilbertFrameRing ℓ F k) :=
  (hilbertFramePolyMat ℓ F k g).map (Ideal.Quotient.mk (hilbertFrameRel ℓ F k))

variable [NumberField F] [Finite k] [TopologicalSpace k] [DiscreteTopology k]
variable {V : Type v} [AddCommGroup V] [Module k V] [Module.Finite k V] [Module.Free k V]

/-- The matrices of the framed residual model `(ρbar|_{G_F}).conj e0`. -/
noncomputable def hilbertFrameResMat (ρbar : GaloisRep ℚ k V)
    (e0 : V ≃ₗ[k] (Fin 2 → k)) : Γ F → Matrix (Fin 2) (Fin 2) k :=
  fun g => LinearMap.toMatrix' (((ρbar.map (algebraMap ℚ F)).conj e0) g)

omit [Finite k] [DiscreteTopology k] [Module.Finite k V] [Module.Free k V] in
lemma hilbertFrameRel_le_ker_res (ρbar : GaloisRep ℚ k V)
    (e0 : V ≃ₗ[k] (Fin 2 → k)) :
    hilbertFrameRel ℓ F k ≤
      RingHom.ker (hilbertFramePolyEval ℓ F k (hilbertFrameResMat F k ρbar e0) id) := by
  refine hilbertFrameRel_le_ker ℓ F k _ _ ?_ ?_ (fun x y => rfl) rfl rfl
  · intro g h
    simp only [hilbertFrameResMat, map_mul, LinearMap.toMatrix'_mul]
  · simp only [hilbertFrameResMat, map_one, LinearMap.toMatrix'_one]

/-- The residue map `evbar : P → k`. -/
noncomputable def hilbertFrameEv (ρbar : GaloisRep ℚ k V)
    (e0 : V ≃ₗ[k] (Fin 2 → k)) : hilbertFrameRing ℓ F k →+* k :=
  hilbertFrameEval ℓ F k (hilbertFrameResMat F k ρbar e0) id
    (hilbertFrameRel_le_ker_res ℓ F k ρbar e0)

omit [Finite k] [DiscreteTopology k] [Module.Finite k V] [Module.Free k V] in
lemma hilbertFrameEv_surjective (ρbar : GaloisRep ℚ k V)
    (e0 : V ≃ₗ[k] (Fin 2 → k)) :
    Function.Surjective (hilbertFrameEv ℓ F k ρbar e0) :=
  fun x => ⟨Ideal.Quotient.mk (hilbertFrameRel ℓ F k) (MvPolynomial.X (Sum.inr x)), by
    simp [hilbertFrameEv]⟩

omit [Finite k] [DiscreteTopology k] [Module.Finite k V] [Module.Free k V] in
lemma hilbertFrameMat_map_frameEv (ρbar : GaloisRep ℚ k V)
    (e0 : V ≃ₗ[k] (Fin 2 → k)) (g : Γ F) :
    (hilbertFrameMat ℓ F k g).map ⇑(hilbertFrameEv ℓ F k ρbar e0) =
      LinearMap.toMatrix' (((ρbar.map (algebraMap ℚ F)).conj e0) g) := by
  ext i j
  simp [hilbertFrameMat, hilbertFramePolyMat, hilbertFrameEv, hilbertFrameResMat]

/-- The level ideals `𝒥` of the `F`-level tautological frame ring. -/
def hilbertFrameLevels (ρbar : GaloisRep ℚ k V) (e0 : V ≃ₗ[k] (Fin 2 → k)) :
    Set (Ideal (hilbertFrameRing ℓ F k)) :=
  {J | J ≤ RingHom.ker (hilbertFrameEv ℓ F k ρbar e0) ∧
    Finite (hilbertFrameRing ℓ F k ⧸ J) ∧ IsLocalRing (hilbertFrameRing ℓ F k ⧸ J) ∧
    ∀ [Finite (hilbertFrameRing ℓ F k ⧸ J)] [IsLocalRing (hilbertFrameRing ℓ F k ⧸ J)]
      [TopologicalSpace (hilbertFrameRing ℓ F k ⧸ J)]
      [DiscreteTopology (hilbertFrameRing ℓ F k ⧸ J)]
      [IsTopologicalRing (hilbertFrameRing ℓ F k ⧸ J)],
      ∃ ρJ : FramedGaloisRep F (hilbertFrameRing ℓ F k ⧸ J) (Fin 2),
        (∀ g : Γ F, LinearMap.toMatrix' (ρJ g) =
          (hilbertFrameMat ℓ F k g).map ⇑(Ideal.Quotient.mk J)) ∧
        IsHilbertHardlyRamified ℓ F (rank_finTwoPi (hilbertFrameRing ℓ F k ⧸ J)) ρJ}

/-! ### The four leaves of the F-level construction -/

theorem hilbertFrameLevels_nonempty {ρbar : GaloisRep ℚ k V}
    (𝒟₀ : HilbertDeformationDatum ℓ F ρbar) (hbase : IsHilbertBaseChangeClause ℓ F)
    (e0 : V ≃ₗ[k] (Fin 2 → k)) :
    (hilbertFrameLevels ℓ F k ρbar e0).Nonempty :=
  sorry

theorem hilbertFrameLevels_directed {ρbar : GaloisRep ℚ k V}
    (hglue : IsHilbertFibreProductClause ℓ F) (e0 : V ≃ₗ[k] (Fin 2 → k)) :
    ∀ J₁ ∈ hilbertFrameLevels ℓ F k ρbar e0, ∀ J₂ ∈ hilbertFrameLevels ℓ F k ρbar e0,
      ∃ J ∈ hilbertFrameLevels ℓ F k ρbar e0, J ≤ J₁ ⊓ J₂ :=
  sorry

theorem hilbertFrameLevels_classification {ρbar : GaloisRep ℚ k V}
    (hirrF : (ρbar.map (algebraMap ℚ F)).IsIrreducible)
    (𝒟₀ : HilbertDeformationDatum ℓ F ρbar)
    (hbase : IsHilbertBaseChangeClause ℓ F) (hglue : IsHilbertFibreProductClause ℓ F)
    (hfin : IsHilbertFiniteFramesClause ℓ F)
    (hrig : IsHilbertResidualRigidityClause F ρbar)
    (e0 : V ≃ₗ[k] (Fin 2 → k)) :
    ∀ (A : Type u) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
      [IsLocalRing A] [Algebra ℤ_[ℓ] A] [Finite A] [DiscreteTopology A]
      (πA : A →+* k), Function.Surjective πA →
      ∀ (ρA : FramedGaloisRep F A (Fin 2)),
      IsHilbertHardlyRamified ℓ F (rank_finTwoPi A) ρA →
      πA.comp (algebraMap ℤ_[ℓ] A) = algebraMap ℤ_[ℓ] k →
      (∀ g : Γ F, ((ρA g).charpoly).map πA =
        ((ρbar.map (algebraMap ℚ F)) g).charpoly) →
      ∃ f : hilbertFrameRing ℓ F k →+* A,
        f.comp (algebraMap ℤ_[ℓ] (hilbertFrameRing ℓ F k)) = algebraMap ℤ_[ℓ] A ∧
        πA.comp f = hilbertFrameEv ℓ F k ρbar e0 ∧
        (∀ g : Γ F, ((hilbertFrameMat ℓ F k g).map ⇑f).charpoly =
          (LinearMap.toMatrix' (ρA g)).charpoly) ∧
        ∃ J ∈ hilbertFrameLevels ℓ F k ρbar e0, J ≤ RingHom.ker f :=
  sorry

theorem hilbertFrameRing_rigid {ρbar : GaloisRep ℚ k V}
    (e0 : V ≃ₗ[k] (Fin 2 → k))
    (A : Type u) [CommRing A] [IsLocalRing A] [Finite A]
    (πA : A →+* k) (f₁ f₂ : hilbertFrameRing ℓ F k →+* A)
    (h₁ : πA.comp f₁ = hilbertFrameEv ℓ F k ρbar e0)
    (h₂ : πA.comp f₂ = hilbertFrameEv ℓ F k ρbar e0)
    (hM : ∀ g : Γ F, (hilbertFrameMat ℓ F k g).map ⇑f₁ =
      (hilbertFrameMat ℓ F k g).map ⇑f₂) :
    f₁ = f₂ :=
  sorry

end HilbertFrameRing

/-- **A LEVEL SYSTEM for the `F`-level hardly ramified problem** (PROVEN
2026-07-26 as an ASSEMBLY — it was a single opaque leaf until then; the
`F`-level twin of `Deformation.lean`'s
`exists_levelIdealSystem_of_deformationCondition`, with every matrix
equation replaced by the corresponding CHARPOLY equation).

**HOW IT IS NOW PROVEN, and what is left.** The witnesses are the
`F`-level tautological frame ring and its level ideals, constructed in the
`HilbertFrameRing` section immediately above:
`P := hilbertFrameRing ℓ F k`, `evbar := hilbertFrameEv`,
`M := hilbertFrameMat`, `𝒥 := hilbertFrameLevels`. Of the eight
conclusion clauses, FOUR are discharged outright here — `hker`, `hlev`
and `hrep` are definitional for `hilbertFrameLevels`, and the residual
charpoly clause is `hilbertFrameMat_map_frameEv` followed by
`LinearEquiv.charpoly_conj`. The remaining four are the four leaves of
that section, each of which has a PROVEN `ℚ`-level twin in
`Deformation.lean` and is therefore a mechanical port, not new
mathematics: `hilbertFrameLevels_nonempty`, `hilbertFrameLevels_directed`,
`hilbertFrameLevels_classification` and `hilbertFrameRing_rigid`.

So the Schlessinger content has not been discharged — it has been
LOCALISED. What was one leaf whose statement quantified over every test
object is now four leaves with named `ℚ`-level models, and the plumbing
between them is compiled rather than assumed.

Everything Schlessinger's inductive small-extension argument produces,
BEFORE any passage to a limit: a single coefficient ring `P`, a
tautological family of matrices `M : Γ F → M₂(P)`, and a downward-directed
family `𝒥` of ideals of `P` whose quotients are the FINITE LOCAL levels of
the construction. Explicitly:

* `hne`, `hdir` — `𝒥` is nonempty and downward directed. Directedness is
  Schlessinger's H1/H2, supplied by `hglue`: a pair of levels is dominated
  by their fibre product, which is again a level.
* `hker`, `hlev` — every level is a finite local ring, and `evbar`
  descends to it.
* `hres` — the tautological matrices reduce, under `evbar`, to matrices
  with the characteristic polynomials of `ρbar|_{G_F}`. This is where `𝒟₀`
  is spent: it is Schlessinger's "`F(k)` is a point", i.e. the
  nonemptiness of the category, and it is what pins `Module.rank k V = 2`
  (through `rank_eq_two_of_hilbertDeformationDatum`, which is what feeds
  `hrig`).
* `hrep` — each level carries a hardly ramified framed representation whose
  matrices are `M mod J`. This is where `hbase` and `hfin` are spent.
* `hclass` — the universal property at the level of `P`: any finite
  discrete hardly ramified test object with the right residual charpolys is
  classified by a ring map out of `P` killing some level ideal. This is
  where `hirrF` and `hrig` are spent — the test object's residual frame is
  only charpoly-identified with `ρbar|_{G_F}`, and Brauer–Nesbitt is what
  conjugates it onto the model frame that `M` deforms.
* `hsep` — rigidity: a map out of `P` into a finite local ring is
  determined by its residue and by the images of the matrix entries. This
  is minimality, and it is what the limit's `hinj` clause is read off.

ONE CLAUSE OF THE `ℚ`-LEVEL TWIN IS DELIBERATELY ABSENT: the compatibility
`evbar.comp (algebraMap ℤ_[ℓ] P) = algebraMap ℤ_[ℓ] k`. Here `k` is FINITE,
so it receives exactly ONE ring map from `ℤ_ℓ`
(`hilbertRingHom_padicInt_ext_finite`) and the clause is automatic; asking
for it would be asking the leaf to reprove a lemma this module already has.
The `ℚ`-level twin states it because its `k` carries no finiteness binder.

CIRCULARITY GUARD (inherited): nothing from `Family.lean`, `Lift.lean`,
`Modularity/*` or `Deformation.lean` may be imported to discharge this; in
particular the odd-prime dichotomy
`not_isIrreducible_of_isHardlyRamified_of_five_le`, under whose hypotheses
this node would be vacuous, is proven over pillar α, which is proven over
this node.

References: Schlessinger, *Functors of Artin rings*, Trans. AMS 130 (1968),
Thm. 2.11; Mazur, *Deforming Galois representations*, MSRI Publ. 16 (1989),
§1.2; de Smit–Lenstra, *Explicit construction of universal deformation
rings*, Prop. 2.3. The three design constraints on `P` that a naive attempt
gets wrong — the generators must include the residue field, those extra
generators must satisfy the TEICHMÜLLER relations, and the level ideals must
be the kernels of the classifying maps rather than an abstract cofinal
system — are spelled out in full in the docstring of the `ℚ`-level twin,
and they apply here verbatim. -/
theorem exists_hilbertLevelIdealSystem_of_clauses
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
    ∃ (P : Type u) (_ : CommRing P) (_ : Algebra ℤ_[ℓ] P)
      (evbar : P →+* k) (_ : Function.Surjective evbar)
      (M : Γ F → Matrix (Fin 2) (Fin 2) P)
      (𝒥 : Set (Ideal P)),
      𝒥.Nonempty ∧
      (∀ J₁ ∈ 𝒥, ∀ J₂ ∈ 𝒥, ∃ J ∈ 𝒥, J ≤ J₁ ⊓ J₂) ∧
      (∀ J ∈ 𝒥, J ≤ RingHom.ker evbar) ∧
      (∀ J ∈ 𝒥, Finite (P ⧸ J) ∧ IsLocalRing (P ⧸ J)) ∧
      (∀ g : Γ F, ((M g).map ⇑evbar).charpoly =
        ((ρbar.map (algebraMap ℚ F)) g).charpoly) ∧
      (∀ J : Ideal P, J ∈ 𝒥 → ∀ [Finite (P ⧸ J)] [IsLocalRing (P ⧸ J)]
        [TopologicalSpace (P ⧸ J)] [DiscreteTopology (P ⧸ J)]
        [IsTopologicalRing (P ⧸ J)],
        ∃ ρJ : FramedGaloisRep F (P ⧸ J) (Fin 2),
          (∀ g : Γ F, LinearMap.toMatrix' (ρJ g) =
            (M g).map ⇑(Ideal.Quotient.mk J)) ∧
          IsHilbertHardlyRamified ℓ F (rank_finTwoPi (P ⧸ J)) ρJ) ∧
      (∀ (A : Type u) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
        [IsLocalRing A] [Algebra ℤ_[ℓ] A] [Finite A] [DiscreteTopology A]
        (πA : A →+* k), Function.Surjective πA →
        ∀ (ρA : FramedGaloisRep F A (Fin 2)),
        IsHilbertHardlyRamified ℓ F (rank_finTwoPi A) ρA →
        πA.comp (algebraMap ℤ_[ℓ] A) = algebraMap ℤ_[ℓ] k →
        (∀ g : Γ F, ((ρA g).charpoly).map πA =
          ((ρbar.map (algebraMap ℚ F)) g).charpoly) →
        ∃ f : P →+* A, f.comp (algebraMap ℤ_[ℓ] P) = algebraMap ℤ_[ℓ] A ∧
          πA.comp f = evbar ∧
          (∀ g : Γ F, ((M g).map ⇑f).charpoly =
            (LinearMap.toMatrix' (ρA g)).charpoly) ∧
          ∃ J ∈ 𝒥, J ≤ RingHom.ker f) ∧
      (∀ (A : Type u) [CommRing A] [IsLocalRing A] [Finite A]
        (πA : A →+* k) (f₁ f₂ : P →+* A),
        πA.comp f₁ = evbar → πA.comp f₂ = evbar →
        (∀ g : Γ F, (M g).map ⇑f₁ = (M g).map ⇑f₂) →
        f₁ = f₂) := by
  classical
  have hrk : Module.rank k V = 2 := rank_eq_two_of_hilbertDeformationDatum 𝒟₀
  have hfr : Module.finrank k V = 2 :=
    Module.finrank_eq_of_rank_eq (by exact_mod_cast hrk)
  set e0 : V ≃ₗ[k] (Fin 2 → k) :=
    (Module.finBasisOfFinrankEq k V hfr).equivFun with he0
  refine ⟨hilbertFrameRing ℓ F k, inferInstance, inferInstance,
    hilbertFrameEv ℓ F k ρbar e0, hilbertFrameEv_surjective ℓ F k ρbar e0,
    hilbertFrameMat ℓ F k, hilbertFrameLevels ℓ F k ρbar e0,
    hilbertFrameLevels_nonempty ℓ F k 𝒟₀ hbase e0,
    hilbertFrameLevels_directed ℓ F k hglue e0,
    fun J hJ => hJ.1, fun J hJ => ⟨hJ.2.1, hJ.2.2.1⟩,
    ?_,
    fun J hJ _ _ _ _ _ => hJ.2.2.2,
    hilbertFrameLevels_classification ℓ F k hirrF 𝒟₀ hbase hglue hfin hrig e0,
    fun A _ _ _ πA f₁ f₂ h₁ h₂ hM =>
      hilbertFrameRing_rigid ℓ F k e0 A πA f₁ f₂ h₁ h₂ hM⟩
  intro g
  rw [hilbertFrameMat_map_frameEv ℓ F k ρbar e0 g,
    ← charpoly_eq_charpoly_toMatrix' ((ρbar.map (algebraMap ℚ F)).conj e0) g,
    GaloisRep.conj_apply, LinearEquiv.charpoly_conj]


open scoped TensorProduct in
/-- **The profinite limit of a level system is the universal frame**
(PROVEN 2026-07-26 — the arithmetic-free half of the construction cut; the
`F`-level twin of `Deformation.lean`'s
`exists_universalFrame_profinite_of_levelIdealSystem`).

Given the level system of the leaf above, `R = lim_{J ∈ 𝒥} P ⧸ J` (built in
`LevelLimit.lean`) carries all five conclusion clauses, and every one of
them is limit bookkeeping:

* PROFINITE — `LevelLimit.compactSpace_limit` and `LevelLimit.t2Space_limit`;
  the open-ideal neighbourhood basis of `0` is
  `LevelLimit.exists_ker_proj_subset`, i.e. the cofinality of the projection
  kernels, which is where downward directedness of `𝒥` is spent.
* LOCAL — `LevelLimit.isUnit_of_forall_isUnit` together with the residue
  map to the field `k`: an element with nonzero residue is a unit at every
  level, hence a unit.
* the RESIDUAL charpoly clause — `hres` read through `Matrix.charpoly_map`.
* `hquot` — `LevelLimit.exists_factor` says a continuous map into a finite
  DISCRETE ring factors through a single level, and then `hbase` applies to
  the level representation `ρJ`.
* `hinj` — `hsep` (rigidity at the level of `P`) transported along the
  DENSE range of `LevelLimit.ofP`.
* weak universality — `hclass` produces a classifying map out of `P`
  killing a level ideal, which extends continuously to the limit. This is
  the clause that costs `Deformation.lean` a separate leaf and costs
  nothing here, for the charpoly reason recorded in the section preamble.

The `ℤ_ℓ`-compatibility that `hclass` demands of a test object's `πA` is not
a hypothesis of `IsHilbertWeaklyUniversalOnFiniteFrames` and is derived on
the spot from `hilbertRingHom_padicInt_ext_finite`: `k` is finite, so it
receives exactly one ring map from `ℤ_ℓ`. -/
theorem exists_universalFrame_profinite_hilbert_of_levelIdealSystem
    (ℓ : ℕ) [Fact ℓ.Prime] (F : Type u) [Field F] [NumberField F]
    {k : Type u} [Field k] [Finite k] [TopologicalSpace k]
    [DiscreteTopology k] [Algebra ℤ_[ℓ] k]
    {V : Type v} [AddCommGroup V] [Module k V] [Module.Finite k V]
    [Module.Free k V]
    {ρbar : GaloisRep ℚ k V}
    (hbase : IsHilbertBaseChangeClause ℓ F)
    {P : Type u} [CommRing P] [Algebra ℤ_[ℓ] P]
    (evbar : P →+* k) (hevsurj : Function.Surjective evbar)
    (M : Γ F → Matrix (Fin 2) (Fin 2) P)
    (𝒥 : Set (Ideal P)) (hne : 𝒥.Nonempty)
    (hdir : ∀ J₁ ∈ 𝒥, ∀ J₂ ∈ 𝒥, ∃ J ∈ 𝒥, J ≤ J₁ ⊓ J₂)
    (hker : ∀ J ∈ 𝒥, J ≤ RingHom.ker evbar)
    (hlev : ∀ J ∈ 𝒥, Finite (P ⧸ J) ∧ IsLocalRing (P ⧸ J))
    (hres : ∀ g : Γ F, ((M g).map ⇑evbar).charpoly =
      ((ρbar.map (algebraMap ℚ F)) g).charpoly)
    (hrep : ∀ J : Ideal P, J ∈ 𝒥 → ∀ [Finite (P ⧸ J)] [IsLocalRing (P ⧸ J)]
      [TopologicalSpace (P ⧸ J)] [DiscreteTopology (P ⧸ J)]
      [IsTopologicalRing (P ⧸ J)],
      ∃ ρJ : FramedGaloisRep F (P ⧸ J) (Fin 2),
        (∀ g : Γ F, LinearMap.toMatrix' (ρJ g) =
          (M g).map ⇑(Ideal.Quotient.mk J)) ∧
        IsHilbertHardlyRamified ℓ F (rank_finTwoPi (P ⧸ J)) ρJ)
    (hclass : ∀ (A : Type u) [CommRing A] [TopologicalSpace A]
      [IsTopologicalRing A] [IsLocalRing A] [Algebra ℤ_[ℓ] A] [Finite A]
      [DiscreteTopology A] (πA : A →+* k), Function.Surjective πA →
      ∀ (ρA : FramedGaloisRep F A (Fin 2)),
      IsHilbertHardlyRamified ℓ F (rank_finTwoPi A) ρA →
      πA.comp (algebraMap ℤ_[ℓ] A) = algebraMap ℤ_[ℓ] k →
      (∀ g : Γ F, ((ρA g).charpoly).map πA =
        ((ρbar.map (algebraMap ℚ F)) g).charpoly) →
      ∃ f : P →+* A, f.comp (algebraMap ℤ_[ℓ] P) = algebraMap ℤ_[ℓ] A ∧
        πA.comp f = evbar ∧
        (∀ g : Γ F, ((M g).map ⇑f).charpoly =
          (LinearMap.toMatrix' (ρA g)).charpoly) ∧
        ∃ J ∈ 𝒥, J ≤ RingHom.ker f)
    (hsep : ∀ (A : Type u) [CommRing A] [IsLocalRing A] [Finite A]
      (πA : A →+* k) (f₁ f₂ : P →+* A),
      πA.comp f₁ = evbar → πA.comp f₂ = evbar →
      (∀ g : Γ F, (M g).map ⇑f₁ = (M g).map ⇑f₂) →
      f₁ = f₂) :
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
      IsHilbertWeaklyUniversalOnFiniteFrames ℓ F ρbar ρuniv πuniv := by
  classical
  -- ## the levels, with their discrete topologies
  letI ltop : ∀ J : 𝒥, TopologicalSpace (P ⧸ (J : Ideal P)) := fun _ => ⊥
  haveI ldisc : ∀ J : 𝒥, DiscreteTopology (P ⧸ (J : Ideal P)) := fun _ => ⟨rfl⟩
  haveI lfin : ∀ J : 𝒥, Finite (P ⧸ (J : Ideal P)) :=
    fun J => (hlev (J : Ideal P) J.2).1
  haveI lloc : ∀ J : 𝒥, IsLocalRing (P ⧸ (J : Ideal P)) :=
    fun J => (hlev (J : Ideal P) J.2).2
  haveI ltr : ∀ J : 𝒥, IsTopologicalRing (P ⧸ (J : Ideal P)) :=
    fun _ => LevelLimit.isTopologicalRing_of_discrete
  -- ## the limit ring `R = lim_{J ∈ 𝒥} P ⧸ J`
  haveI itr : IsTopologicalRing (LevelLimit.Limit 𝒥) :=
    LevelLimit.isTopologicalRing_limit 𝒥
  haveI icp : CompactSpace (LevelLimit.Limit 𝒥) := LevelLimit.compactSpace_limit 𝒥
  haveI it2 : T2Space (LevelLimit.Limit 𝒥) := LevelLimit.t2Space_limit 𝒥
  letI ialg : Algebra ℤ_[ℓ] (LevelLimit.Limit 𝒥) :=
    ((LevelLimit.ofP 𝒥).comp (algebraMap ℤ_[ℓ] P)).toAlgebra
  have halgR : (algebraMap ℤ_[ℓ] (LevelLimit.Limit 𝒥)) =
      (LevelLimit.ofP 𝒥).comp (algebraMap ℤ_[ℓ] P) := RingHom.algebraMap_toAlgebra _
  have hext : ∀ {x y : LevelLimit.Limit 𝒥},
      (∀ J : 𝒥, LevelLimit.proj 𝒥 J x = LevelLimit.proj 𝒥 J y) → x = y :=
    fun h => Subtype.ext (funext h)
  -- ## the residue map of each level: `evbar` descends because `J ≤ ker evbar`
  have hkerJ : ∀ (J : 𝒥) (a : P), a ∈ (J : Ideal P) → evbar a = 0 := by
    intro J a ha
    have h := hker (J : Ideal P) J.2 ha
    rwa [RingHom.mem_ker] at h
  have hevJex : ∀ J : 𝒥, ∃ f : (P ⧸ (J : Ideal P)) →+* k,
      ∀ p : P, f (Ideal.Quotient.mk (J : Ideal P) p) = evbar p := fun J =>
    ⟨Ideal.Quotient.lift (J : Ideal P) evbar (hkerJ J), fun _ => rfl⟩
  choose evJ hevJmk using hevJex
  have hevJfac : ∀ (J₁ J₂ : 𝒥) (h : (J₁ : Ideal P) ≤ (J₂ : Ideal P))
      (x : P ⧸ (J₁ : Ideal P)), evJ J₂ (Ideal.Quotient.factor h x) = evJ J₁ x := by
    intro J₁ J₂ h x
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [Ideal.Quotient.factor_mk, hevJmk, hevJmk]
  -- ## the residue map of the limit: any level computes it, by directedness
  obtain ⟨J₀, hJ₀⟩ := id hne
  set πuniv : (LevelLimit.Limit 𝒥) →+* k :=
    (evJ ⟨J₀, hJ₀⟩).comp (LevelLimit.proj 𝒥 ⟨J₀, hJ₀⟩) with hπdef
  have hπ0 : ∀ x, πuniv x = evJ ⟨J₀, hJ₀⟩ (LevelLimit.proj 𝒥 ⟨J₀, hJ₀⟩ x) :=
    fun x => by rw [hπdef]; rfl
  have hπproj : ∀ (J : 𝒥) (x : LevelLimit.Limit 𝒥),
      evJ J (LevelLimit.proj 𝒥 J x) = πuniv x := by
    intro J x
    obtain ⟨J', hJ', hJ'le⟩ := hdir (J : Ideal P) J.2 J₀ hJ₀
    have key : ∀ (K : 𝒥), J' ≤ (K : Ideal P) →
        evJ K (LevelLimit.proj 𝒥 K x) =
          evJ ⟨J', hJ'⟩ (LevelLimit.proj 𝒥 ⟨J', hJ'⟩ x) := by
      intro K hle
      rw [← LevelLimit.proj_compat 𝒥 x ⟨J', hJ'⟩ K hle]
      exact hevJfac ⟨J', hJ'⟩ K hle (LevelLimit.proj 𝒥 ⟨J', hJ'⟩ x)
    rw [key J (hJ'le.trans inf_le_left), hπ0, key ⟨J₀, hJ₀⟩ (hJ'le.trans inf_le_right)]
  have hπι : ∀ p : P, πuniv (LevelLimit.ofP 𝒥 p) = evbar p := by
    intro p
    rw [hπ0, LevelLimit.proj_ofP, hevJmk]
  have hπsurj : Function.Surjective πuniv := by
    intro c
    obtain ⟨p, rfl⟩ := hevsurj c
    exact ⟨LevelLimit.ofP 𝒥 p, hπι p⟩
  have hπcont : Continuous πuniv := by
    have h1 : Continuous (⇑(evJ ⟨J₀, hJ₀⟩) ∘ ⇑(LevelLimit.proj 𝒥 ⟨J₀, hJ₀⟩)) :=
      continuous_of_discreteTopology.comp (LevelLimit.continuous_proj 𝒥 ⟨J₀, hJ₀⟩)
    have heq : (⇑πuniv) =
        ⇑(evJ ⟨J₀, hJ₀⟩) ∘ ⇑(LevelLimit.proj 𝒥 ⟨J₀, hJ₀⟩) := funext hπ0
    rw [heq]
    exact h1
  -- ## the limit is LOCAL: a unit at every level is a unit
  haveI hntR : Nontrivial (LevelLimit.Limit 𝒥) := by
    rcases exists_pair_ne k with ⟨a, b, hab⟩
    obtain ⟨x, hx⟩ := hπsurj a
    obtain ⟨y, hy⟩ := hπsurj b
    exact ⟨x, y, fun h => hab (by rw [← hx, ← hy, h])⟩
  have hunitJ : ∀ (J : 𝒥) (u : P ⧸ (J : Ideal P)), evJ J u ≠ 0 → IsUnit u := by
    intro J u hu
    have hsurjJ : Function.Surjective (evJ J) := by
      intro c
      obtain ⟨p, rfl⟩ := hevsurj c
      exact ⟨Ideal.Quotient.mk (J : Ideal P) p, hevJmk J p⟩
    have hmax : (RingHom.ker (evJ J)).IsMaximal :=
      RingHom.ker_isMaximal_of_surjective (evJ J) hsurjJ
    have hkm : RingHom.ker (evJ J) = IsLocalRing.maximalIdeal (P ⧸ (J : Ideal P)) :=
      IsLocalRing.eq_maximalIdeal hmax
    refine IsLocalRing.notMem_maximalIdeal.mp ?_
    rw [← hkm, RingHom.mem_ker]
    exact hu
  haveI hlocR : IsLocalRing (LevelLimit.Limit 𝒥) := by
    refine IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun a => ?_
    by_cases ha : πuniv a = 0
    · right
      refine LevelLimit.isUnit_of_forall_isUnit 𝒥 _ fun J => hunitJ J _ ?_
      have h1 : πuniv (1 - a) = 1 := by rw [map_sub, map_one, ha, sub_zero]
      rw [hπproj J (1 - a), h1]
      exact one_ne_zero
    · left
      exact LevelLimit.isUnit_of_forall_isUnit 𝒥 _ fun J =>
        hunitJ J _ (by rw [hπproj]; exact ha)
  -- ## the level representations, and the matrices they share
  have hrepJex : ∀ J : 𝒥, ∃ ρJ : FramedGaloisRep F (P ⧸ (J : Ideal P)) (Fin 2),
      (∀ g : Γ F, LinearMap.toMatrix' (ρJ g) =
        (M g).map ⇑(Ideal.Quotient.mk (J : Ideal P))) ∧
      IsHilbertHardlyRamified ℓ F (rank_finTwoPi (P ⧸ (J : Ideal P))) ρJ :=
    fun J => hrep (J : Ideal P) J.2
  choose ρJ hρJmat hρJhr using hrepJex
  set mat : Γ F → Matrix (Fin 2) (Fin 2) (LevelLimit.Limit 𝒥) :=
    fun g => (M g).map ⇑(LevelLimit.ofP 𝒥)
  have hprojmat : ∀ (J : 𝒥) (g : Γ F) (i j : Fin 2),
      LevelLimit.proj 𝒥 J (mat g i j) =
        (M g).map ⇑(Ideal.Quotient.mk (J : Ideal P)) i j := fun _ _ _ _ => rfl
  have honeJ : ∀ J : 𝒥, (M 1).map ⇑(Ideal.Quotient.mk (J : Ideal P)) = 1 := by
    intro J
    rw [← hρJmat J 1, map_one, LinearMap.toMatrix'_one]
  have hmulJ : ∀ (J : 𝒥) (g h : Γ F),
      (M (g * h)).map ⇑(Ideal.Quotient.mk (J : Ideal P)) =
        ((M g).map ⇑(Ideal.Quotient.mk (J : Ideal P))) *
          ((M h).map ⇑(Ideal.Quotient.mk (J : Ideal P))) := by
    intro J g h
    rw [← hρJmat J (g * h), ← hρJmat J g, ← hρJmat J h, map_mul,
      LinearMap.toMatrix'_mul]
  have hone : mat 1 = 1 := by
    refine Matrix.ext fun i j => hext fun J => ?_
    by_cases hij : i = j
    · subst hij
      rw [hprojmat, honeJ, Matrix.one_apply_eq, Matrix.one_apply_eq, map_one]
    · rw [hprojmat, honeJ, Matrix.one_apply_ne hij, Matrix.one_apply_ne hij, map_zero]
  have hmul : ∀ g h, mat (g * h) = mat g * mat h := by
    intro g h
    refine Matrix.ext fun i j => hext fun J => ?_
    have hL : LevelLimit.proj 𝒥 J (mat (g * h) i j) =
        ∑ l, (LevelLimit.proj 𝒥 J (mat g i l)) * (LevelLimit.proj 𝒥 J (mat h l j)) := by
      rw [hprojmat, hmulJ, Matrix.mul_apply]
      exact Finset.sum_congr rfl fun l _ => by rw [hprojmat, hprojmat]
    have hR : LevelLimit.proj 𝒥 J ((mat g * mat h) i j) =
        ∑ l, (LevelLimit.proj 𝒥 J (mat g i l)) * (LevelLimit.proj 𝒥 J (mat h l j)) := by
      rw [Matrix.mul_apply, map_sum]
      exact Finset.sum_congr rfl fun l _ => map_mul _ _ _
    rw [hL, hR]
  have hcont : Continuous mat := by
    refine continuous_pi fun i => continuous_pi fun j => ?_
    refine continuous_induced_rng.2 (continuous_pi fun J => ?_)
    show Continuous fun g => Ideal.Quotient.mk (J : Ideal P) (M g i j)
    have hJ := LevelLimit.continuous_toMatrix' (ρJ J)
    have h2 : Continuous (fun g => LinearMap.toMatrix' (ρJ J g) i j) :=
      (continuous_apply j).comp ((continuous_apply i).comp hJ)
    have heq : (fun g => LinearMap.toMatrix' (ρJ J g) i j)
        = fun g => Ideal.Quotient.mk (J : Ideal P) (M g i j) := by
      funext g
      rw [hρJmat J g]
      rfl
    rwa [heq] at h2
  set ρuniv : FramedGaloisRep F (LevelLimit.Limit 𝒥) (Fin 2) :=
    LevelLimit.framedOfMatrices mat hone hmul hcont with hρunivdef
  have hρmat : ∀ g, LinearMap.toMatrix' (ρuniv g) = (M g).map ⇑(LevelLimit.ofP 𝒥) := by
    intro g
    rw [hρunivdef]
    exact LevelLimit.toMatrix'_framedOfMatrices mat hone hmul hcont g
  have hpush : ∀ {A : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
      (ψ : (LevelLimit.Limit 𝒥) →+* A) (hψ : Continuous ψ) (g : Γ F),
      LinearMap.toMatrix' (framePushforward ψ hψ ρuniv g) =
        (M g).map (⇑ψ ∘ ⇑(LevelLimit.ofP 𝒥)) := by
    intro A _ _ _ ψ hψ g
    rw [toMatrix'_framePushforward, hρmat, Matrix.map_map]
  -- ## a map out of `P` killing a level ideal extends continuously to the limit
  have hlift : ∀ (A : Type u) [CommRing A] [TopologicalSpace A]
      [IsTopologicalRing A] [Finite A] [DiscreteTopology A] (f : P →+* A),
      (∃ J ∈ 𝒥, J ≤ RingHom.ker f) →
      ∃ ψ : (LevelLimit.Limit 𝒥) →+* A, Continuous ψ ∧
        ∀ p : P, ψ (LevelLimit.ofP 𝒥 p) = f p := by
    intro A _ _ _ _ _ f hf
    obtain ⟨J, hJ, hJf⟩ := hf
    have hkill : ∀ a ∈ J, f a = 0 := by
      intro a ha
      have hmem := hJf ha
      rwa [RingHom.mem_ker] at hmem
    letI : TopologicalSpace (P ⧸ J) := ltop ⟨J, hJ⟩
    haveI : DiscreteTopology (P ⧸ J) := ldisc ⟨J, hJ⟩
    refine ⟨(Ideal.Quotient.lift J f hkill).comp (LevelLimit.proj 𝒥 ⟨J, hJ⟩), ?_, ?_⟩
    · have h1 : Continuous (⇑(Ideal.Quotient.lift J f hkill) ∘
          ⇑(LevelLimit.proj 𝒥 ⟨J, hJ⟩)) :=
        continuous_of_discreteTopology.comp (LevelLimit.continuous_proj 𝒥 ⟨J, hJ⟩)
      exact h1
    · intro p; rfl
  refine ⟨LevelLimit.Limit 𝒥, inferInstance, inferInstance, itr, hlocR, ialg, icp, it2,
    ρuniv, πuniv, hπsurj, hπcont, ?_, ?_, ?_, ?_, ?_⟩
  · -- open ideals are cofinal in the neighbourhood filter of `0`
    intro U hU
    obtain ⟨J, hJ⟩ := LevelLimit.exists_ker_proj_subset 𝒥 hne hdir hU
    exact ⟨RingHom.ker (LevelLimit.proj 𝒥 J), LevelLimit.isOpen_ker_proj 𝒥 J, hJ⟩
  · -- the residual charpoly clause, read off `hres`
    intro g
    rw [charpoly_eq_charpoly_toMatrix', hρmat, ← Matrix.charpoly_map, Matrix.map_map,
      show (⇑πuniv ∘ ⇑(LevelLimit.ofP 𝒥)) = ⇑evbar from funext hπι]
    exact hres g
  · -- `hquot`: factor through one level, then apply `hbase`
    intro A _ _ _ _ _ _ _ φ hφ halg
    obtain ⟨J, f, hfmk, -⟩ := LevelLimit.exists_factor 𝒥 hne hdir φ hφ
    have hfcont : Continuous f := continuous_of_discreteTopology
    have hfalg : f.comp (algebraMap ℤ_[ℓ] (P ⧸ (J : Ideal P))) = algebraMap ℤ_[ℓ] A := by
      ext z
      have h1 : (algebraMap ℤ_[ℓ] (P ⧸ (J : Ideal P))) z =
          Ideal.Quotient.mk (J : Ideal P) (algebraMap ℤ_[ℓ] P z) := rfl
      have h2 : (algebraMap ℤ_[ℓ] (LevelLimit.Limit 𝒥)) z =
          LevelLimit.ofP 𝒥 (algebraMap ℤ_[ℓ] P z) := by rw [halgR]; rfl
      rw [RingHom.comp_apply, h1, hfmk, ← h2, ← RingHom.comp_apply, halg]
    have hpfeq : framePushforward φ hφ ρuniv = framePushforward f hfcont (ρJ J) := by
      refine GaloisRep.ext fun g => LinearMap.toMatrix'.injective ?_
      rw [hpush φ hφ g, toMatrix'_framePushforward, hρJmat J g, Matrix.map_map,
        show (⇑φ ∘ ⇑(LevelLimit.ofP 𝒥)) =
          (⇑f ∘ ⇑(Ideal.Quotient.mk (J : Ideal P))) from
          funext fun p => (hfmk p).symm]
    rw [hpfeq]
    exact hbase f hfcont hfalg (hρJhr J)
  · -- `hinj`: rigidity of `P`, transported by the density of its image
    intro A _ _ _ _ _ _ _ πA φ₁ φ₂ hφ₁ hφ₂ h1 h2 hpfeq
    have hg : (φ₁.comp (LevelLimit.ofP 𝒥)) = (φ₂.comp (LevelLimit.ofP 𝒥)) := by
      refine hsep A πA _ _ ?_ ?_ ?_
      · ext p
        show πA (φ₁ (LevelLimit.ofP 𝒥 p)) = evbar p
        rw [show πA (φ₁ (LevelLimit.ofP 𝒥 p)) = (πA.comp φ₁) (LevelLimit.ofP 𝒥 p) from rfl,
          h1]
        exact hπι p
      · ext p
        show πA (φ₂ (LevelLimit.ofP 𝒥 p)) = evbar p
        rw [show πA (φ₂ (LevelLimit.ofP 𝒥 p)) = (πA.comp φ₂) (LevelLimit.ofP 𝒥 p) from rfl,
          h2]
        exact hπι p
      · intro g
        have hm : LinearMap.toMatrix' (framePushforward φ₁ hφ₁ ρuniv g) =
            LinearMap.toMatrix' (framePushforward φ₂ hφ₂ ρuniv g) := by rw [hpfeq]
        rw [hpush φ₁ hφ₁ g, hpush φ₂ hφ₂ g] at hm
        exact hm
    refine DFunLike.coe_injective (Continuous.ext_on
      (LevelLimit.dense_range_ofP 𝒥 hne hdir) hφ₁ hφ₂ ?_)
    rintro x ⟨p, rfl⟩
    exact RingHom.congr_fun hg p
  · -- weak universality: `hclass` plus the continuous extension `hlift`
    intro A _ _ _ _ _ _ _ ρA hρA πA hπAsurj hcp
    have hπAalg : πA.comp (algebraMap ℤ_[ℓ] A) = algebraMap ℤ_[ℓ] k :=
      hilbertRingHom_padicInt_ext_finite _ _
    obtain ⟨f, hfalg, hfπ, hfcp, hfJ⟩ := hclass A πA hπAsurj ρA hρA hπAalg hcp
    obtain ⟨ψ, hψcont, hψι⟩ := hlift A f hfJ
    refine ⟨ψ, hψcont, ?_, ?_, ?_⟩
    · ext z
      show ψ ((algebraMap ℤ_[ℓ] (LevelLimit.Limit 𝒥)) z) = algebraMap ℤ_[ℓ] A z
      rw [halgR]
      show ψ (LevelLimit.ofP 𝒥 (algebraMap ℤ_[ℓ] P z)) = algebraMap ℤ_[ℓ] A z
      rw [hψι]
      exact congrFun (congrArg (fun h : ℤ_[ℓ] →+* A => (h : ℤ_[ℓ] → A)) hfalg) z
    · have hπAcont : Continuous (⇑πA : A → k) := continuous_of_discreteTopology
      have hcomp : Continuous (⇑(πA.comp ψ) : LevelLimit.Limit 𝒥 → k) :=
        hπAcont.comp hψcont
      refine DFunLike.coe_injective (Continuous.ext_on
        (LevelLimit.dense_range_ofP 𝒥 hne hdir) hcomp hπcont ?_)
      rintro x ⟨p, rfl⟩
      show πA (ψ (LevelLimit.ofP 𝒥 p)) = πuniv (LevelLimit.ofP 𝒥 p)
      rw [hψι, hπι,
        show πA (f p) = (πA.comp f) p from rfl, hfπ]
    · intro g
      rw [charpoly_eq_charpoly_toMatrix' ρuniv g, hρmat, ← Matrix.charpoly_map,
        Matrix.map_map,
        show (⇑ψ ∘ ⇑(LevelLimit.ofP 𝒥)) = ⇑f from funext hψι,
        charpoly_eq_charpoly_toMatrix' ρA g]
      exact hfcp g

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
      IsHilbertWeaklyUniversalOnFiniteFrames ℓ F ρbar ρuniv πuniv := by
  obtain ⟨P, iP, iPalg, evbar, hevsurj, M, 𝒥, hne, hdir, hker, hlev,
      hres, hrep, hclass, hsep⟩ :=
    exists_hilbertLevelIdealSystem_of_clauses ℓ F hirrF 𝒟₀ hbase hglue hfin hrig
  letI := iP
  letI := iPalg
  exact exists_universalFrame_profinite_hilbert_of_levelIdealSystem ℓ F hbase
    evbar hevsurj M 𝒥 hne hdir hker hlev hres hrep hclass hsep

/-! #### The three helpers of the limit passage

All three are local to this module and DELIBERATELY NAMED APART from the
`ℚ`-level originals they transcribe: `Deformation.lean` is DOWNSTREAM of
this file and reopens the same `GaloisRepresentation` namespace, so a
name collision here silently rebinds the name there (that is how a
duplicated `det_pushforwardFrame` once broke that module). -/

open scoped TensorProduct in
/-- **Characteristic polynomials push forward by coefficient extension**
(PROVEN; the `F`-level twin of `Deformation.lean`'s
`charpoly_pushforwardFrame`, and the exact charpoly analogue of
`det_framePushforward` above).

`LinearEquiv.charpoly_conj` absorbs the framing identification and
`LinearMap.charpoly_baseChange` turns the base-changed characteristic
polynomial into the `algebraMap B A`-image of the original, which is `ψ`
by `RingHom.algebraMap_toAlgebra`.

This is what lets the limit passage feed a datum's FINITE LEVELS to a
charpoly-only universality hypothesis and read the answer back over the
original ring. -/
lemma charpoly_framePushforward {F : Type u} [Field F] [NumberField F]
    {B : Type u} [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
    {A : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    (ψ : B →+* A) (hψ : Continuous ψ) (ρ : FramedGaloisRep F B (Fin 2))
    (g : Γ F) :
    ((framePushforward ψ hψ ρ) g).charpoly = ((ρ g).charpoly).map ψ := by
  letI : Algebra B A := ψ.toAlgebra
  letI : ContinuousSMul B A := continuousSMul_of_algebraMap B A
    (by rw [RingHom.algebraMap_toAlgebra]; exact hψ)
  show ((((ρ.baseChange A).conj
    (TensorProduct.piScalarRight B A A (Fin 2))) g)).charpoly = _
  rw [GaloisRep.conj_apply, LinearEquiv.charpoly_conj]
  show ((Module.End.baseChangeHom B A (Fin 2 → B)) (ρ g)).charpoly = _
  rw [show (Module.End.baseChangeHom B A (Fin 2 → B)) (ρ g) =
    LinearMap.baseChange A (ρ g) from rfl, LinearMap.charpoly_baseChange,
    RingHom.algebraMap_toAlgebra]

/-- **Finiteness from `𝔪`-primarity** (PROVEN, pure commutative algebra —
no arithmetic content; the local twin of `Deformation.lean`'s
`finite_quotient_of_maximalIdeal_pow_le`, which lives downstream): a
Noetherian local ring `R` with FINITE residue field `k` has finite
quotient by any ideal `I` containing a power of the maximal ideal.

`ker π` is the maximal ideal (`π` is a surjection onto a field), so
`R ⧸ 𝔪 ≃ k` is finite; `𝔪` is finitely generated, so `R ⧸ 𝔪 ^ n` is
finite by the successive-quotients dévissage `Ideal.finite_quotient_pow`;
and `R ⧸ I` is a quotient of `R ⧸ 𝔪 ^ n` once `𝔪 ^ n ≤ I`. -/
lemma finite_quotient_of_pow_maximalIdeal_le {R : Type*} [CommRing R]
    [IsLocalRing R] [IsNoetherianRing R] {k : Type*} [Field k] [Finite k]
    {I : Ideal R} (π : R →+* k) (hπsurj : Function.Surjective π)
    (hn : ∃ n : ℕ, IsLocalRing.maximalIdeal R ^ n ≤ I) :
    Finite (R ⧸ I) := by
  obtain ⟨n, hnle⟩ := hn
  have hker : RingHom.ker π = IsLocalRing.maximalIdeal R :=
    IsLocalRing.eq_maximalIdeal
      (RingHom.ker_isMaximal_of_surjective π hπsurj)
  haveI : Finite (R ⧸ IsLocalRing.maximalIdeal R) := by
    rw [← hker]
    exact Finite.of_equiv k
      (RingHom.quotientKerEquivOfSurjective hπsurj).symm.toEquiv
  haveI : Finite (R ⧸ IsLocalRing.maximalIdeal R ^ n) :=
    Ideal.finite_quotient_pow (IsNoetherian.noetherian _) n
  exact Finite.of_surjective (Ideal.Quotient.factor hnle)
    (Ideal.Quotient.factor_surjective hnle)

open CategoryTheory in
/-- **Kőnig's lemma plus adic assembly, for RING MAPS** (PROVEN, pure
commutative algebra): let `A` be `I`-adically complete and separated and
let `X n` be, for each `n`, a NONEMPTY FINITE set of ring homomorphisms
`R →+* A ⧸ Iⁿ` STABLE under the transition maps `A ⧸ Iᵐ →+* A ⧸ Iⁿ`
(`n ≤ m`) by postcomposition. Then a single `ψ : R →+* A` has all of its
level-`n` reductions in `X n`.

This is the ring-map-only shadow of `Deformation.lean`'s
`exists_ringHom_matrix_of_forall_quotient_mem`, and it is all that is
needed here: this module's `IsWeaklyUniversal` is CHARPOLY-ONLY, so the
classifying datum at level `n` is a bare ring homomorphism — an element
of a type that does not depend on anything — rather than the `ℚ`-level
Σ-type of a map together with a conjugation. That is exactly why no
matrix avatar has to be introduced.

Proof: the `X n` with the postcomposition transitions form an inverse
system of nonempty finite sets over `ℕᵒᵖ` (functoriality is
`Ideal.Quotient.factor_mk` twice over), so Kőnig's lemma
(`nonempty_sections_of_finite_inverse_system`) gives a compatible tower
`(ψₙ)`, and `IsAdicComplete.liftRingHom` — the universal property of
adic completeness for ring maps — assembles it. -/
lemma exists_ringHom_of_forall_quotientPow_mem
    {A : Type*} [CommRing A] (I : Ideal A) [IsAdicComplete I A]
    {R : Type*} [CommRing R]
    (X : ∀ n : ℕ, Set (R →+* A ⧸ I ^ n))
    (hfin : ∀ n : ℕ, (X n).Finite) (hne : ∀ n : ℕ, (X n).Nonempty)
    (hstab : ∀ (m n : ℕ) (hmn : n ≤ m) (p : R →+* A ⧸ I ^ m), p ∈ X m →
      (Ideal.Quotient.factorPow I hmn).comp p ∈ X n) :
    ∃ ψ : R →+* A, ∀ n : ℕ, (Ideal.Quotient.mk (I ^ n)).comp ψ ∈ X n := by
  classical
  -- functoriality of the transition maps
  have hfacComp : ∀ {a b c : ℕ} (h1 : a ≤ b) (h2 : b ≤ c) (y : A ⧸ I ^ c),
      Ideal.Quotient.factorPow I h1 (Ideal.Quotient.factorPow I h2 y) =
        Ideal.Quotient.factorPow I (h1.trans h2) y := by
    intro a b c h1 h2 y
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
    rw [Ideal.Quotient.factor_mk, Ideal.Quotient.factor_mk,
      Ideal.Quotient.factor_mk]
  -- the inverse system of nonempty finite sets of classifying maps
  let Fsys : ℕᵒᵖ ⥤ Type _ :=
    { obj := fun j => ↥(X j.unop)
      map := fun {j j'} f =>
        ↾(fun p : ↥(X j.unop) =>
          (⟨(Ideal.Quotient.factorPow I (leOfHom f.unop)).comp p.1,
            hstab j.unop j'.unop (leOfHom f.unop) p.1 p.2⟩ : ↥(X j'.unop)))
      map_id := fun j => by ext p; simp
      map_comp := fun {j₁ j₂ j₃} f g => by ext p; simp [hfacComp] }
  haveI : ∀ j : ℕᵒᵖ, Finite (Fsys.obj j) := fun j => (hfin j.unop).to_subtype
  haveI : ∀ j : ℕᵒᵖ, Nonempty (Fsys.obj j) := fun j => (hne j.unop).to_subtype
  obtain ⟨s, hs⟩ := nonempty_sections_of_finite_inverse_system Fsys
  set f : ∀ n : ℕ, R →+* A ⧸ I ^ n := fun n => (s (Opposite.op n)).1 with hf
  have hcompat : ∀ {m n : ℕ} (hle : m ≤ n),
      (Ideal.Quotient.factorPow I hle).comp (f n) = f m := by
    intro m n hle
    exact congrArg Subtype.val (hs (homOfLE hle).op)
  refine ⟨IsAdicComplete.liftRingHom I f hcompat, fun n => ?_⟩
  rw [IsAdicComplete.mk_comp_liftRingHom I f hcompat n, hf]
  exact (s (Opposite.op n)).2

/-- **From the finite discrete levels to the whole of Mazur's category**
(PROVEN 2026-07-26 — the LIMIT half of the 2026-07-26 cut; the `F`-level
twin of `Deformation.lean`'s `isWeaklyUniversalOnIdentifiedFrames_of_finite`):
a datum that classifies every FINITE DISCRETE framed test object classifies
every datum.

THE ARGUMENT, which is the one that file's docstring lays out, simplified
by this module's charpoly-only formulation. Let `𝒟'` be an arbitrary
datum and `J = 𝔪_{𝒟'.R}`.

1. Each level `𝒟'.R ⧸ Jⁿ` is FINITE — `𝒟'.π` is a surjection onto the
   finite `k` with kernel `J`, so `natCast`-counting gives `|𝒟'.R ⧸ Jⁿ| ≤
   |k|ⁿ` (`finite_quotient_of_pow_maximalIdeal_le` above) — and DISCRETE,
   because `𝒟'.isAdic` makes `Jⁿ` open and the quotient map is open. It is
   local, a `ℤ_ℓ`-algebra, and it carries the pushforward of `𝒟'.ρ`, which
   is hardly ramified by the functoriality clause `hbase` and reduces to
   `ρbar|_{G_F}` because `𝒟'.resid` does (transported by
   `charpoly_framePushforward` above).
2. So the hypothesis produces, for each `n`, a nonempty FINITE set of
   classifying maps `ψ : 𝒟.R →+* 𝒟'.R ⧸ Jⁿ`. Finiteness: a `ψ` compatible
   with the reductions is LOCAL, so it kills `𝔪_{𝒟.R}ⁿ` (the maximal ideal
   of `𝒟'.R ⧸ Jⁿ` has vanishing `n`-th power) and therefore factors through
   the finite ring `𝒟.R ⧸ 𝔪ⁿ`.
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

Steps 3 and 4 are packaged as `exists_ringHom_of_forall_quotientPow_mem`
above, the ring-map-only shadow of `Deformation.lean`'s
`exists_ringHom_matrix_of_forall_quotient_mem`. NO matrix avatar and no
`framePushforward`-transport lemma is needed here, which is exactly the
simplification the charpoly-only `IsWeaklyUniversal` buys.

WHAT IS AND IS NOT SPENT. `hbase` is the ONLY clause consumed, and it is
consumed once, at step 1, to know that the finite levels of an arbitrary
datum are hardly ramified. Nothing else about `IsHilbertHardlyRamified` is
touched: the rest is pure commutative algebra plus the charpoly dictionary.
No continuity of the assembled `f` is asserted or needed —
`HilbertDeformationDatum.IsWeaklyUniversal` is a bare ring-map statement.

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
    𝒟.IsWeaklyUniversal := by
  classical
  intro 𝒟'
  -- the maximal-adic tower of the coefficient ring of `𝒟'`
  set J : Ideal 𝒟'.R := IsLocalRing.maximalIdeal 𝒟'.R with hJ
  haveI : IsAdicComplete J 𝒟'.R := 𝒟'.isAdicComplete
  have hkerπ : RingHom.ker 𝒟'.π = J :=
    IsLocalRing.eq_maximalIdeal
      (RingHom.ker_isMaximal_of_surjective 𝒟'.π 𝒟'.π_surjective)
  have hkerD : RingHom.ker 𝒟.π = IsLocalRing.maximalIdeal 𝒟.R :=
    IsLocalRing.eq_maximalIdeal
      (RingHom.ker_isMaximal_of_surjective 𝒟.π 𝒟.π_surjective)
  have hJne : J ≠ ⊤ := (IsLocalRing.maximalIdeal.isMaximal 𝒟'.R).ne_top
  have hJpowne : ∀ n : ℕ, n ≠ 0 → J ^ n ≠ ⊤ := by
    intro n hn htop
    exact hJne (top_le_iff.mp (htop ▸ Ideal.pow_le_self hn))
  have hπpow : ∀ (n : ℕ), n ≠ 0 → ∀ a ∈ J ^ n, 𝒟'.π a = 0 := by
    intro n hn a ha
    have hmem : a ∈ RingHom.ker 𝒟'.π := by
      rw [hkerπ]
      exact Ideal.pow_le_self hn ha
    exact hmem
  -- step 1a: every level is FINITE (`𝒟'.π` is onto the finite `k`, with
  -- kernel `J`, so `|𝒟'.R ⧸ Jⁿ| ≤ |k|ⁿ`)
  have hfinlev : ∀ n : ℕ, Finite (𝒟'.R ⧸ J ^ n) := fun n =>
    finite_quotient_of_pow_maximalIdeal_le 𝒟'.π 𝒟'.π_surjective ⟨n, le_rfl⟩
  -- step 1b: every level is DISCRETE (`Jⁿ` is open by `𝒟'.isAdic`, and the
  -- quotient map is an open map)
  have hJopen : ∀ n : ℕ, IsOpen ((J ^ n : Ideal 𝒟'.R) : Set 𝒟'.R) := fun n =>
    (isAdic_iff.mp 𝒟'.isAdic).1 n
  have hmkcont : ∀ n : ℕ, Continuous (Ideal.Quotient.mk (J ^ n)) := fun n =>
    (QuotientRing.isOpenQuotientMap_mk (J ^ n)).continuous
  have hdisc : ∀ n : ℕ, DiscreteTopology (𝒟'.R ⧸ J ^ n) := by
    intro n
    rw [discreteTopology_iff_isOpen_singleton_zero]
    have himg : (Ideal.Quotient.mk (J ^ n)) ''
        ((J ^ n : Ideal 𝒟'.R) : Set 𝒟'.R) = {0} := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact Ideal.Quotient.eq_zero_iff_mem.mpr hy
      · rintro rfl
        exact ⟨0, (J ^ n).zero_mem, map_zero _⟩
    rw [← himg]
    exact (QuotientRing.isOpenQuotientMap_mk (J ^ n)).isOpenMap _ (hJopen n)
  -- adic separatedness of `𝒟'.R`: an element is pinned by its reductions
  have hsep : ∀ x : 𝒟'.R, (∀ n : ℕ, x ∈ J ^ n) → x = 0 := by
    intro x hx
    refine IsHausdorff.haus (I := J) (M := 𝒟'.R) inferInstance x fun n => ?_
    rw [SModEq.sub_mem, sub_zero]
    have hsm : (J ^ n : Ideal 𝒟'.R) ≤ (J ^ n) • (⊤ : Submodule 𝒟'.R 𝒟'.R) := by
      intro r hr
      have hmem : r • (1 : 𝒟'.R) ∈ (J ^ n) • (⊤ : Submodule 𝒟'.R 𝒟'.R) :=
        Submodule.smul_mem_smul hr Submodule.mem_top
      simpa using hmem
    exact hsm (hx n)
  have heq : ∀ a b : 𝒟'.R,
      (∀ n : ℕ, Ideal.Quotient.mk (J ^ n) a = Ideal.Quotient.mk (J ^ n) b) →
      a = b := by
    intro a b hab
    have h0 : a - b = 0 := hsep _ fun n => Ideal.Quotient.eq.mp (hab n)
    exact sub_eq_zero.mp h0
  -- step 2, finiteness half: an admissible `ψ` is local, hence kills
  -- `𝔪_{𝒟.R}ⁿ`, hence factors through the FINITE ring `𝒟.R ⧸ 𝔪ⁿ`
  have hfinhom : ∀ (n : ℕ) (hn : n ≠ 0),
      {ψ : 𝒟.R →+* 𝒟'.R ⧸ J ^ n |
        (Ideal.Quotient.lift (J ^ n) 𝒟'.π (hπpow n hn)).comp ψ = 𝒟.π}.Finite := by
    intro n hn
    set Jq : Ideal (𝒟'.R ⧸ J ^ n) := J.map (Ideal.Quotient.mk (J ^ n)) with hJq
    have hkerlift : ∀ y : 𝒟'.R ⧸ J ^ n,
        (Ideal.Quotient.lift (J ^ n) 𝒟'.π (hπpow n hn)) y = 0 → y ∈ Jq := by
      intro y hy
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective y
      rw [Ideal.Quotient.lift_mk] at hy
      exact Ideal.mem_map_of_mem _ (by rw [← hkerπ]; exact hy)
    have hJqpow : Jq ^ n = ⊥ := by
      rw [hJq, ← Ideal.map_pow, Ideal.map_quotient_self]
    have hkill : ∀ ψ : 𝒟.R →+* 𝒟'.R ⧸ J ^ n,
        (Ideal.Quotient.lift (J ^ n) 𝒟'.π (hπpow n hn)).comp ψ = 𝒟.π →
        ∀ x ∈ (IsLocalRing.maximalIdeal 𝒟.R) ^ n, ψ x = 0 := by
      intro ψ hψ x hx
      have hmR : IsLocalRing.maximalIdeal 𝒟.R ≤ Ideal.comap ψ Jq := by
        intro y hy
        refine hkerlift _ ?_
        rw [← RingHom.comp_apply, hψ]
        rw [← hkerD] at hy
        exact hy
      have hpow : ∀ j : ℕ,
          (IsLocalRing.maximalIdeal 𝒟.R) ^ j ≤ Ideal.comap ψ (Jq ^ j) := by
        intro j
        induction j with
        | zero => simp
        | succ j ih =>
          rw [pow_succ, pow_succ]
          refine le_trans (Ideal.mul_mono ih hmR) ?_
          rw [Ideal.mul_le]
          intro r hr s hs
          have hr' : ψ r ∈ Jq ^ j := hr
          have hs' : ψ s ∈ Jq := hs
          show ψ (r * s) ∈ Jq ^ j * Jq
          rw [map_mul]
          exact Ideal.mul_mem_mul hr' hs'
      have hmem : ψ x ∈ Jq ^ n := hpow n hx
      rw [hJqpow] at hmem
      exact hmem
    haveI : Finite (𝒟.R ⧸ (IsLocalRing.maximalIdeal 𝒟.R) ^ n) :=
      finite_quotient_of_pow_maximalIdeal_le 𝒟.π 𝒟.π_surjective ⟨n, le_rfl⟩
    haveI := hfinlev n
    haveI : Finite ((𝒟.R ⧸ (IsLocalRing.maximalIdeal 𝒟.R) ^ n) →+*
        𝒟'.R ⧸ J ^ n) :=
      Finite.of_injective
        (fun g : (𝒟.R ⧸ (IsLocalRing.maximalIdeal 𝒟.R) ^ n) →+* 𝒟'.R ⧸ J ^ n =>
          (g : (𝒟.R ⧸ (IsLocalRing.maximalIdeal 𝒟.R) ^ n) → 𝒟'.R ⧸ J ^ n))
        DFunLike.coe_injective
    refine Set.Finite.subset (Set.finite_range
      (fun g : (𝒟.R ⧸ (IsLocalRing.maximalIdeal 𝒟.R) ^ n) →+* 𝒟'.R ⧸ J ^ n =>
        g.comp (Ideal.Quotient.mk ((IsLocalRing.maximalIdeal 𝒟.R) ^ n)))) ?_
    intro ψ hψ
    exact ⟨Ideal.Quotient.lift _ ψ (hkill ψ hψ), RingHom.ext fun _ => rfl⟩
  -- the level-`n` sets of classifying maps: a BARE ring homomorphism, subject
  -- to the `ℤ_ℓ`-clause, the reduction clause and the charpoly clause
  set X : ∀ n : ℕ, Set (𝒟.R →+* 𝒟'.R ⧸ J ^ n) := fun n =>
    {ψ | (ψ.comp (algebraMap ℤ_[ℓ] 𝒟.R) =
            (Ideal.Quotient.mk (J ^ n)).comp (algebraMap ℤ_[ℓ] 𝒟'.R)) ∧
         (∀ hn : n ≠ 0,
            (Ideal.Quotient.lift (J ^ n) 𝒟'.π (hπpow n hn)).comp ψ = 𝒟.π) ∧
         (∀ g : Γ F, ((𝒟.ρ g).charpoly).map ψ =
            ((𝒟'.ρ g).charpoly).map (Ideal.Quotient.mk (J ^ n)))}
    with hX
  -- the transition maps of the tower
  have hfacmk : ∀ (m n : ℕ) (hmn : n ≤ m) (a : 𝒟'.R),
      Ideal.Quotient.factorPow J hmn (Ideal.Quotient.mk (J ^ m) a) =
        Ideal.Quotient.mk (J ^ n) a := fun _ _ _ a =>
    Ideal.Quotient.factor_mk _ a
  have hliftfac : ∀ (m n : ℕ) (hmn : n ≤ m) (hn : n ≠ 0) (hm : m ≠ 0)
      (y : 𝒟'.R ⧸ J ^ m),
      (Ideal.Quotient.lift (J ^ n) 𝒟'.π (hπpow n hn))
          (Ideal.Quotient.factorPow J hmn y) =
        (Ideal.Quotient.lift (J ^ m) 𝒟'.π (hπpow m hm)) y := by
    intro m n hmn _ _ y
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective y
    rw [hfacmk m n hmn a, Ideal.Quotient.lift_mk, Ideal.Quotient.lift_mk]
  -- step 3, stability half
  have hXstab : ∀ (m n : ℕ) (hmn : n ≤ m) (p : 𝒟.R →+* 𝒟'.R ⧸ J ^ m),
      p ∈ X m → (Ideal.Quotient.factorPow J hmn).comp p ∈ X n := by
    intro m n hmn p hp
    simp only [hX, Set.mem_setOf_eq] at hp ⊢
    obtain ⟨h1, h2, h3⟩ := hp
    refine ⟨?_, ?_, ?_⟩
    · refine RingHom.ext fun x => ?_
      have h1x := RingHom.congr_fun h1 x
      simp only [RingHom.comp_apply] at h1x ⊢
      rw [h1x, hfacmk m n hmn]
    · intro hn
      have hm : m ≠ 0 := by omega
      refine RingHom.ext fun r => ?_
      have h2x := RingHom.congr_fun (h2 hm) r
      simp only [RingHom.comp_apply] at h2x ⊢
      rw [hliftfac m n hmn hn hm, h2x]
    · intro g
      rw [← Polynomial.map_map, h3 g, Polynomial.map_map,
        Ideal.Quotient.factor_comp_mk]
  -- step 1: the positive levels are nonempty. `𝒟'.R ⧸ Jⁿ` is a FINITE
  -- DISCRETE local `ℤ_ℓ`-algebra carrying a hardly ramified frame (by the
  -- functoriality clause `hbase`) that reduces to `ρbar|_{G_F}` (because
  -- `𝒟'.resid` does), so the hypothesis classifies it.
  have hXne_pos : ∀ n : ℕ, n ≠ 0 → (X n).Nonempty := by
    intro n hn
    haveI : Nontrivial (𝒟'.R ⧸ J ^ n) := by
      rw [← not_subsingleton_iff_nontrivial, Ideal.Quotient.subsingleton_iff]
      exact hJpowne n hn
    haveI : IsLocalRing (𝒟'.R ⧸ J ^ n) :=
      IsLocalRing.of_surjective' (Ideal.Quotient.mk (J ^ n))
        Ideal.Quotient.mk_surjective
    haveI := hfinlev n
    haveI := hdisc n
    have halgQ : (Ideal.Quotient.mk (J ^ n)).comp (algebraMap ℤ_[ℓ] 𝒟'.R) =
        algebraMap ℤ_[ℓ] (𝒟'.R ⧸ J ^ n) := rfl
    have hπQmk : (Ideal.Quotient.lift (J ^ n) 𝒟'.π (hπpow n hn)).comp
        (Ideal.Quotient.mk (J ^ n)) = 𝒟'.π := rfl
    have hHR : IsHilbertHardlyRamified ℓ F (rank_finTwoPi (𝒟'.R ⧸ J ^ n))
        (framePushforward (Ideal.Quotient.mk (J ^ n)) (hmkcont n) 𝒟'.ρ) :=
      hbase (Ideal.Quotient.mk (J ^ n)) (hmkcont n) halgQ
        𝒟'.isHilbertHardlyRamified
    have hπQsurj :
        Function.Surjective (Ideal.Quotient.lift (J ^ n) 𝒟'.π (hπpow n hn)) := by
      intro y
      obtain ⟨x, hx⟩ := 𝒟'.π_surjective y
      exact ⟨Ideal.Quotient.mk (J ^ n) x, hx⟩
    have hresQ : ∀ g : Γ F,
        (((framePushforward (Ideal.Quotient.mk (J ^ n)) (hmkcont n) 𝒟'.ρ) g).charpoly).map
            (Ideal.Quotient.lift (J ^ n) 𝒟'.π (hπpow n hn)) =
          ((ρbar.map (algebraMap ℚ F)) g).charpoly := by
      intro g
      rw [charpoly_framePushforward, Polynomial.map_map, hπQmk]
      exact 𝒟'.resid g
    obtain ⟨ψ, _hcont, halg, hπ, hcp⟩ :=
      h𝒟 (𝒟'.R ⧸ J ^ n) _ hHR _ hπQsurj hresQ
    refine ⟨ψ, ?_, ?_, ?_⟩
    · rw [halg, ← halgQ]
    · exact fun _ => hπ
    · intro g
      rw [hcp g, charpoly_framePushforward]
  have hXne : ∀ n : ℕ, (X n).Nonempty := by
    intro n
    rcases eq_or_ne n 0 with rfl | hn
    · obtain ⟨p, hp⟩ := hXne_pos 1 one_ne_zero
      exact ⟨_, hXstab 1 0 (Nat.zero_le 1) p hp⟩
    · exact hXne_pos n hn
  have hXfin : ∀ n : ℕ, (X n).Finite := by
    intro n
    rcases eq_or_ne n 0 with rfl | hn
    · haveI : Subsingleton (𝒟'.R ⧸ J ^ 0) := by
        rw [Ideal.Quotient.subsingleton_iff, pow_zero, Ideal.one_eq_top]
      exact Set.Subsingleton.finite fun a _ b _ =>
        RingHom.ext fun _ => Subsingleton.elim _ _
    · exact (hfinhom n hn).subset fun ψ hψ => hψ.2.1 hn
  -- steps 3 and 4: Kőnig, then adic assembly
  obtain ⟨f, hf⟩ :=
    exists_ringHom_of_forall_quotientPow_mem J X hXfin hXne hXstab
  simp only [hX, Set.mem_setOf_eq] at hf
  refine ⟨f, ?_, ?_, ?_⟩
  -- the `ℤ_ℓ`-clause holds modulo every level, hence holds by separatedness
  · refine RingHom.ext fun x => ?_
    refine heq _ _ fun n => ?_
    have hn := RingHom.congr_fun (hf n).1 x
    simpa using hn
  -- the reduction clause is already visible at the first level
  · refine RingHom.ext fun r => ?_
    have h1 := RingHom.congr_fun ((hf 1).2.1 one_ne_zero) r
    simpa using h1
  -- the charpoly clause holds modulo every level, coefficient by coefficient
  · intro g
    refine Polynomial.ext fun i => ?_
    rw [Polynomial.coeff_map]
    refine heq _ _ fun n => ?_
    have hn := congrArg
      (fun q : Polynomial (𝒟'.R ⧸ J ^ n) => q.coeff i) ((hf n).2.2 g)
    simpa [Polynomial.coeff_map] using hn

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
    (hw2 : ∀ w : HeightOneSpectrum (𝓞 F), ((2 : ℕ) : 𝓞 F) ∈ w.asIdeal →
      ¬ ((ℓ : ℤ) ∣ ((Nat.card (𝓞 F ⧸ w.asIdeal) : ℤ) ^ 2 - 1)))
    {k : Type u} [Field k] [Finite k] [TopologicalSpace k]
    [DiscreteTopology k] [Algebra ℤ_[ℓ] k]
    {V : Type v} [AddCommGroup V] [Module k V] [Module.Finite k V]
    [Module.Free k V]
    {ρbar : GaloisRep ℚ k V}
    (hirrF : (ρbar.map (algebraMap ℚ F)).IsIrreducible)
    (𝒟₀ : HilbertDeformationDatum ℓ F ρbar) :
    ∃ 𝒟 : HilbertDeformationDatum ℓ F ρbar, 𝒟.IsWeaklyUniversal :=
  exists_isWeaklyUniversal_hilbertDeformationDatum_of_clauses ℓ F hirrF 𝒟₀
    (isHilbertBaseChangeClause ℓ F) (isHilbertFibreProductClause ℓ hℓ5 F hw2)
    (isHilbertFiniteFramesClause ℓ F)
    (isHilbertProLimitClause ℓ ((Fact.out : ℓ.Prime).odd_of_ne_two (by omega)) F)
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

No non-degeneracy clause is imposed on `bad`. **The reason given here
before 2026-07-26 was wrong**, and it is worth recording both the error and
the correct reason, because the false version was used downstream to license
the production leaf `nonempty_potentialHeckeDatum_of_five_le` enlarging `bad`
at will. It read: *"every statement here quantifies over places OUTSIDE
`bad`, so a larger bad set is a weaker datum"*. That conflates two quantifier
POSITIONS, and the two clauses mentioning `bad` move in OPPOSITE directions:

* `charFrobT : ∀ w ∉ bad, …` is a hypothesis, so it does weaken as `bad`
  grows;
* `adjoin_heckeT` has `heckeT '' {w | w ∉ bad}` in **generating-set**
  position, so it SHRINKS as `bad` grows and `= ⊤` gets strictly HARDER.

So the datum is not monotone in `bad` in either direction, and no purely
formal argument licenses enlarging `bad`.

**The conclusion nevertheless survives, for a different and non-formal
reason** (audit 2026-07-26, by the owner of the production leaf): enlarging
`bad` by any FINITE set is harmless, because of `moduleFinite` plus
Chebotarev.

* `A := Algebra.adjoin ℤ_[ℓ] (teichmüller roots ∪ heckeT '' {w ∉ bad})` is in
  particular a `ℤ_[ℓ]`-SUBMODULE of `T`; `T` is module-finite over the
  Noetherian ring `ℤ_[ℓ]`, so `A` is finitely generated, and a finitely
  generated submodule of a finitely generated module over a complete
  Noetherian local ring is CLOSED. Hence `A` is closed in `T`.
* By Chebotarev the Frobenii at the places outside any finite set are still
  DENSE in `Γ F`; `charFrobT` identifies `heckeT w` with `−(ρT.charFrob w).coeff 1`,
  i.e. with a trace of `ρT`, and `ρT` is continuous. So the closed set `A`
  contains every trace of `ρT`, whatever finite `bad` is.

Classically `𝕋_𝔪` is generated over `ℤ_[ℓ]` by exactly those traces and the
Teichmüller roots supply the `W(k)` factor, so `adjoin_heckeT` holds for
every finite `bad` — but as a THEOREM about the classical object, not as a
formal consequence of the interface. `moduleFinite` is load-bearing for it:
without it the algebraic `Algebra.adjoin` and the closure of the traces come
apart, and `adjoin_heckeT` would be a strictly topological statement that a
dense subalgebra need not satisfy.

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
under both changes, and its statement is again unchanged.

## INTERFACE REPAIR (2026-07-26, third pass) — the topology of `T` is now PINNED

The two fields `isAdic` and `isAdicComplete` were added on 2026-07-26 by the
owner of `exists_hilbertHeckeDatum_of_hilbertHeckeAlgebra`, which is the leaf
that has to present a `HilbertHeckeAlgebra` as an object of the `F`-level
deformation CATEGORY. That leaf's own docstring had already diagnosed the
defect and prescribed exactly this repair ("the honest fix, if this leaf is
ever attacked, is to pin the topology in `HilbertHeckeAlgebra`, as
`Modularity/Patching.lean` does with `[IsModuleTopology ℤ_[p] T]`, and
re-derive `isHilbertHardlyRamified`"); here is why nothing weaker works.

`GaloisRep K A M` is a CONTINUOUS monoid hom into `Module.End A M` carrying
`moduleTopology A (Module.End A M)`, so the type of `ρT` — and the meaning of
every clause of `IsHilbertHardlyRamified`, `IsUnramifiedAt` and `IsFlatAt`
included — depends on the topology `T` carries. `HilbertDeformationDatum`
demands `IsAdic (maximalIdeal R)` and `IsAdicComplete`. Two topologies on one
carrier therefore give two DIFFERENT and incomparable continuity conditions:
retopologizing `T` adically does not transport `isHilbertHardlyRamified`, and
no arithmetic input can bridge the gap, because the gap is not arithmetic.
Pinning the topology here makes the two interfaces agree on the nose, and
`isHilbertHardlyRamified` is then literally the deformation category's own
local condition rather than a homonym of it.

`IsNoetherianRing T`, the third thing a datum wants, is NOT added as a field:
it follows from `moduleFinite` by `IsNoetherianRing.of_finite ℤ_[ℓ] T`.

Cost to the production leaf `nonempty_potentialHeckeDatum_of_five_le`: none
mathematically — see the two docstrings there — and its statement is once
again unchanged. -/
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
  /-- **The topology of `T` is the maximal-adic one.** Added 2026-07-26 by
  the INTERFACE REPAIR below: without it the topology `T` carries is
  arbitrary, `isHilbertHardlyRamified` (which is a statement about
  continuity for THAT topology) says nothing about the adic one, and
  `exists_hilbertHeckeDatum_of_hilbertHeckeAlgebra` — which has to hand `T`
  to `HilbertDeformationDatum`, where `IsAdic` is demanded — is not provable
  from any amount of arithmetic. Classically this is no constraint at all:
  the localized Hecke algebra is finite free over `ℤ_[ℓ]` and carries the
  `ℓ`-adic topology, which is its maximal-adic topology because `T/ℓT` is
  Artinian local. -/
  isAdic : IsAdic (IsLocalRing.maximalIdeal T)
  /-- **`T` is maximal-adically complete and separated.** Added 2026-07-26
  with `isAdic`, and for the same reason. Classically automatic from
  `moduleFinite` + `moduleFree`: `T ≅ ℤ_[ℓ] ^ n` as a `ℤ_[ℓ]`-module is
  `ℓ`-adically complete, and the `ℓ`-adic and maximal-adic filtrations are
  cofinal in each other. -/
  isAdicComplete : IsAdicComplete (IsLocalRing.maximalIdeal T) T
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
  /-- **Every place of `F` over `2` has residue field `𝔽₂`** — i.e. `2`
  has residue degree `1` in `F` at every place above it.

  ADDED 2026-07-26, AND LOAD-BEARING. This is what makes the tame-at-`2`
  gluing clause of the `F`-level deformation problem TRUE: that clause
  needs `ℓ ∤ N(w)² − 1` at every `w ∣ 2` (see the refutation block above
  `isHilbertTameAtTwo_of_fibreProduct`, where a machine-verified
  counterexample at `ℓ = 5`, `F = ℚ(μ₅)`, `N(w) = 16` is recorded), and
  `N(w) = 2` turns that into `ℓ ∤ 3`, which is `5 ≤ ℓ`.

  It costs nothing in Taylor's argument: Moret–Bailly's theorem lets one
  prescribe the behaviour of `F` at any finite set `S` of places, and
  demanding that `2 ∈ S` — hence that `2` split completely in `F` — is the
  standard way to keep the local condition at `2` rigid. Under `hbar` the
  ramification of `ρbar` is confined to `{2, ℓ}`, so `2` is in `S` already;
  what the field genuinely costs the citation is the nonemptiness of the
  local point set `Ω_2 ⊆ X(ℚ_2)`. See THE CITATION, STATED IN FULL in the
  docstring of `nonempty_potentialHeckeDatum_of_five_le`.

  Note that it does NOT ask `F/ℚ` to be unramified at `2` — only that the
  residue extension be trivial; complete splitting supplies both.

  It is INDEPENDENT of `totallyReal` and `galoisF`: `F = ℚ(√5)` satisfies
  both and has `2` inert, `N(w) = 4`, `N(w)² − 1 = 15`, which `ℓ = 5`
  divides. (The `ℚ(μ₅)` counterexample cited above refutes
  `isHilbertTameAtTwo_of_fibreProduct`, but is CM and so cannot witness
  independence here.) -/
  residueCardTwo : ∀ w : HeightOneSpectrum (𝓞 F), ((2 : ℕ) : 𝓞 F) ∈ w.asIdeal →
    Nat.card (𝓞 F ⧸ w.asIdeal) = 2
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

## SECOND AUDIT (2026-07-26, later the same day): STRENGTHENED TWICE, STILL TRUE

Two further repairs to `HilbertHeckeAlgebra` landed after the audit above was
written, and both STRENGTHEN what this leaf must produce while changing not
one character of its statement — which is exactly the shape of change a
reader of a leaf's own docstring would otherwise never see. They are the
Teichmüller half of `adjoin_heckeT` and the new field `πT_surjective`. Their
joint effect is that the ring this leaf must exhibit is no longer the
classical `ℤ_ℓ`-Hecke algebra `𝕋_𝔪` but its unramified base change to
`W(k)`.

**The leaf survives them.** Clause by clause against the CURRENT field list
— read it, not any prose — the classical witness is the local factor `T` of
`𝕋_𝔪 ⊗_{ℤ_[ℓ]} W(k)` cut out by a chosen embedding of the residue field
`𝔽 = 𝕋_𝔪 / 𝔪` into `k` (`𝔽` is the trace field of `ρbar|_{G_F}`, so
`𝔽 ⊆ k` and such an embedding exists):

* `[IsLocalRing T]` — a finite `ℤ_[ℓ]`-algebra is a finite product of local
  rings and `T` is one of the factors.
* `[Module.Finite ℤ_[ℓ] T]` — `𝕋_𝔪` and `W(k)` are both finite over
  `ℤ_[ℓ]`; this is the classical finiteness of the space of Hilbert modular
  forms of fixed weight and level.
* `[Module.Free ℤ_[ℓ] T]` — `𝕋` is a subring of `End(M)` for an `ℓ`-adic
  lattice `M` of Hilbert cusp forms, hence `ℤ_[ℓ]`-torsion-free, hence free;
  `W(k)` is free; and a ring direct factor is a module direct summand, so `T`
  is a finitely generated projective, hence free, module over the PID
  `ℤ_[ℓ]`.
* `adjoin_heckeT`, in its Teichmüller form — `W(k) = ℤ_[ℓ][μ_{|k|−1}]` is
  generated over `ℤ_[ℓ]` by elements satisfying `x ^ ℓ ^ d = x`
  (`d = [k : 𝔽_ℓ]`), i.e. by members of `teichmullerRootSet ℓ`; `𝕋_𝔪` is
  generated over `ℤ_[ℓ]` by the good-place Hecke operators; ring
  homomorphisms carry Teichmüller roots to Teichmüller roots
  (`map_mem_teichmullerRootSet` below) and the projection onto the local
  factor is surjective, so both generating sets descend to `T`. Note the
  adjoin is ALGEBRAIC, not topological, and that is exactly what the
  classical object supplies: `𝕋` is BY DEFINITION the `ℤ_[ℓ]`-subalgebra of
  `End(M)` generated by the Hecke operators.
* `πT_surjective` — the residue field of the chosen local factor is the
  compositum of `𝔽` and `k` inside `k`, i.e. `k` itself. This is the clause
  the Teichmüller weakening was made to leave room for: over `ℤ_[ℓ]` and the
  Hecke operators alone the residue field is `𝔽`, and the `R_F = T_F` leaf
  below is then false whenever `𝔽 ⊊ k`.
* `ρT`, `charFrobT`, `residT` — the Carayol–Taylor representation attached
  to the eigensystem of `𝔪`, pushed forward along `𝕋_𝔪 → T`. Carayol's
  construction of a `GL₂(𝕋_𝔪)`-valued representation (as opposed to a
  pseudo-representation) needs `ρbar|_{G_F}` ABSOLUTELY irreducible; the
  next section shows that `hbar` and `hirr` already give it.
* `[TopologicalSpace T]`, `[IsTopologicalRing T]`, `bad`, `heckeT` — these
  are FIELDS, so this leaf chooses them: the `ℓ`-adic topology; `bad` the
  places dividing the level, `2` or `ℓ`; `heckeT` the Hecke operators.
  **Two things about this bullet were stale and are corrected here**
  (2026-07-26):
  - It said the interface "does not PIN the topology to the adic one". It
    does now — `isAdic` and `isAdicComplete` were added by the INTERFACE
    REPAIR recorded in `HilbertHeckeAlgebra`'s docstring. The choice of
    topology is therefore no longer free; it costs this leaf the two facts
    listed under WHAT REMAINS below, both of which the classical witness
    supplies (`T ≅ ℤ_[ℓ] ^ n` as a module, `T/ℓT` Artinian local).
  - It counted `bad` as free on the strength of the monotonicity claim in
    `HilbertHeckeAlgebra`'s docstring, which was FALSE — `bad` sits in
    generating-set position in `adjoin_heckeT`, where enlarging it makes the
    clause harder. `bad` is still effectively free, but by Chebotarev plus
    the closedness of `ℤ_[ℓ]`-submodules of `T`, not by quantifier
    monotonicity; the corrected argument is written out there.
* `isHilbertHardlyRamified` — the deep clause; see WHAT REMAINS below.

## `hbar` + `hirr` ALREADY GIVE ABSOLUTE IRREDUCIBILITY

`GaloisRep.IsIrreducible` is irreducibility over `k`, whereas Carayol's
theorem, level lowering and every `R = T` argument want it over `k̄`. There
is no gap here, and the reason is worth recording because it is what stops
this leaf from being false at the `k` / `k̄` boundary:

an ODD `ρbar` cannot be `k`-irreducible without being `k̄`-irreducible. If
`ρbar ⊗ k̄` were reducible while `ρbar` is `k`-irreducible, its two
characters would be conjugate over a quadratic extension `k'/k` and the
image of `ρbar` would lie in the nonsplit torus `k'ˣ ⊆ GL₂(k)`, hence be
ABELIAN. Complex conjugation then satisfies `ρbar c ∈ k'ˣ` and
`(ρbar c)² = 1`, so `ρbar c = ±1` and `det (ρbar c) = N_{k'/k}(±1) = 1`;
but `hbar`'s determinant clause forces `det (ρbar c) = χ̄_ℓ(c) = −1`, and
`−1 ≠ 1` since `ℓ` is odd. So the hypotheses this leaf carries are the
classical ones and nothing needs to be added to them.

## THE CITATION, STATED IN FULL (2026-07-26)

Everything above audits the leaf. This section is the leaf's positive
content: WHAT is cited, WHERE, and WHY each hypothesis in the Lean statement
is the hypothesis the cited theorem asks for. It is written out because a
citation that names only an author is not checkable, and because the
`residueCardTwo` field (added later than the two audits above) had no
justification recorded anywhere.

### The two theorems

**(MB) Moret–Bailly**, *Groupes de Picard et problèmes de Skolem II*, Ann.
Sci. É.N.S. (4) **22** (1989), 181–194, **Théorème 1.3**. Let `K` be a
number field, `X/K` a smooth geometrically irreducible quasi-projective
variety, `S` a FINITE set of places of `K`, and for each `v ∈ S` a nonempty
open `Ω_v ⊆ X(K_v)`. Then there is a finite extension `F/K` — which may be
taken GALOIS over `K`, and totally real when `K` is totally real and the
archimedean `Ω_v` are chosen inside `X(ℝ)` — in which **every `v ∈ S`
splits completely**, together with a point of `X(F)` lying in `Ω_v` above
each `v ∈ S`. The only input the theorem needs about `S` is that it be
finite and that each `Ω_v` be nonempty.

**(T) Taylor**, *Remarks on a conjecture of Fontaine and Mazur*, J. Inst.
Math. Jussieu **1** (2002), 125–143, **Theorem B** (proof in §§2–3). Let
`ℓ ≥ 5` and let `ρbar : G_ℚ → GL₂(k)`, `k` finite of characteristic `ℓ`, be
irreducible and odd. Then `ρbar` is POTENTIALLY MODULAR: there is a totally
real `F`, Galois over `ℚ` and linearly disjoint from the splitting field of
`ρbar`, such that `ρbar|_{G_F}` is the residual representation of a Hilbert
newform over `F` of parallel weight `2`. The proof applies (MB) to a twisted
Hilbert–Blumenthal moduli variety to produce an abelian variety over `F`
whose `ℓ`-torsion realizes `ρbar|_{G_F}` and whose torsion at an auxiliary
prime is residually dihedral, hence modular (theta series / Jacquet–Langlands,
*Automorphic Forms on GL(2)*, LNM **114**, 1970); a modularity lifting
theorem over totally real fields at that auxiliary prime (Fujiwara,
*Deformation rings and Hecke algebras in the totally real case*;
Skinner–Wiles, *Nearly ordinary deformations of irreducible residual
representations*, Ann. Fac. Sci. Toulouse **10** (2001)) then transfers
modularity to `ρbar|_{G_F}`.

The Hecke side of the datum is a THIRD body of work, cited for the fields of
`HilbertHeckeAlgebra`:

**(C) Carayol**, *Sur les représentations `ℓ`-adiques associées aux formes
modulaires de Hilbert*, Ann. Sci. É.N.S. **19** (1986), 409–468, together
with **Taylor**, *On Galois representations associated to Hilbert modular
forms*, Invent. Math. **98** (1989), 265–280 — existence and local–global
compatibility of the Galois representation attached to a Hilbert newform;
and **Carayol**, *Formes modulaires et représentations galoisiennes à
valeurs dans un anneau local complet*, Contemp. Math. **165** (1994),
213–237 — the upgrade from a pseudo-representation to a genuine
`GL₂(𝕋_𝔪)`-valued `ρT`, which is what needs `ρbar|_{G_F}` ABSOLUTELY
irreducible (supplied above from `hbar` + `hirr`, no extra hypothesis).

**(LL) Level lowering over totally real fields** — Fujiwara (op. cit.);
Jarvis, *Mazur's principle for totally real fields of odd degree*,
Compositio **116** (1999), 39–79, and *Level lowering for modular mod `ℓ`
representations over totally real fields*, Math. Ann. **313** (1999),
141–160; Rajaei, *On the levels of mod `ℓ` Hilbert modular forms*, J. Reine
Angew. Math. **537** (2001), 33–65. The newform (T) produces has SOME level;
`isHilbertHardlyRamified` demands the MINIMAL one, and (LL) is what closes
that gap.

### Hypothesis-by-hypothesis match

| Lean hypothesis | what the citation uses it for |
| --- | --- |
| `hℓ5 : 5 ≤ ℓ` | (T)'s standing `ℓ ≥ 5`, and — see below — `ℓ ∤ 3` for the consumer's tame-at-`2` gluing |
| `hℓOdd : Odd ℓ` | absolute irreducibility (via `det (ρbar c) = −1 ≠ 1`), and the unique square root `ε^{1/2}` of the nebentypus |
| `[Finite k]`, `[Algebra ℤ_[ℓ] k]` | forces `char k = ℓ` (a nonzero kernel, else `ℚ_ℓ ⊆ k`), so `k` is a finite field of characteristic `ℓ` and `W(k)` is defined — this is the lemma `natCast_eq_zero_of_finite_algebra` the consumer already uses |
| `hdim : Module.rank k V = 2` | `GL₂`, i.e. that `ρbar` is a two-dimensional representation at all |
| `hirr` | (T)'s irreducibility hypothesis, and (C)'s absolute irreducibility after the argument below |
| `hbar.det = χ̄_ℓ` | oddness of `ρbar` (evaluate at complex conjugation), which (T) requires; and it forces the nebentypus to be trivial mod `ℓ` |
| `hbar.isUnramified`, `hbar.isFlat`, `hbar.isTameAtTwo` | the MINIMAL level and weight of the newform, i.e. what (LL) lowers to and what `isHilbertHardlyRamified` then asserts of `ρT` |

### Field-by-field, on the `PotentialHeckeDatum` side

`F`, `totallyReal`, `galoisF` and `irreducibleF` are (T) verbatim; `hecke`
is (C) + (LL), audited clause by clause in the SECOND AUDIT above. That
leaves the one field neither audit covers:

**`residueCardTwo : ∀ w ∣ 2, Nat.card (𝓞 F ⧸ w.asIdeal) = 2`.** It is
supplied by putting `2` into the set `S` of (MB): a place that splits
completely has `e = f = 1`, so `N(w) = 2^{f(w|2)} = 2` at every `w ∣ 2`.
Three things make this the right reading rather than an extra assumption:

* **`S` is at the citation's disposal.** (MB) constrains `S` only by
  finiteness, and (T) already prescribes behaviour at the archimedean
  places, at `ℓ`, at the auxiliary prime, and at the primes where `ρbar`
  ramifies. Under `hbar` the ramification of `ρbar` is confined to `{2, ℓ}`,
  so **`2` is already in `S`** in any version of the argument that pins the
  local behaviour at every ramified prime. The field costs the citation
  nothing it was not already paying.
* **What it does cost is one nonemptiness**, `Ω_2 ≠ ∅`, i.e. a `ℚ_2`-point
  of the twisted Hilbert–Blumenthal variety. That is precisely the kind of
  local condition (MB) exists to absorb, and it is part of (T)'s own set-up
  at every place of `S`; but it is an obligation, not a freebie, and it is
  recorded here so that nobody discharging this leaf assumes `S` is free.
* **Complete splitting at `2` over-delivers**, and usefully: it gives
  `e(w|2) = 1` as well, and it makes `ρbar|_{G_{F_w}} = ρbar|_{G_{ℚ_2}}`, so
  the tame-at-`2` clause of `hbar` descends to `F` verbatim rather than
  merely surviving.

**`residueCardTwo` is INDEPENDENT of the other fields** — it is not
derivable from `totallyReal` + `galoisF`, and the counterexample recorded
above the refuted `isHilbertTameAtTwo_of_fibreProduct` (`ℓ = 5`,
`F = ℚ(μ₅)`, `N(w) = 16`) **cannot** be used to see this, because `ℚ(μ₅)`
is a CM field and so fails `totallyReal`. A witness that does the job:

> `F = ℚ(√5)` is totally real (signature `[2, 0]`, discriminant `5`) and
> Galois over `ℚ`, and `2` is INERT in it — one place `w ∣ 2`, `e = 1`,
> `f = 2`, `N(w) = 4`. Then `N(w)² − 1 = 15` and `5 ∣ 15`, so at `ℓ = 5`
> the tame-at-`2` gluing clause fails for a field satisfying every other
> field of `PotentialHeckeDatum`. (Machine-checked in PARI/GP.)

Nor is it derivable from `hecke`: `IsHilbertHardlyRamified.isTameAtTwo` is a
condition on `ρT` at the places over `2` and holds for every residue degree.
The two are about different things — `isTameAtTwo` says the DATUM is tame at
`2`, `residueCardTwo` says the deformation problem is CLOSED UNDER FIBRE
PRODUCTS there — which is why the consumer
`exists_finiteIndex_isIntegral_charpolyCoeff_of_isHardlyRamified` needs both.

### One obligation that IS discharged from another

`adjoin_heckeT` does not have to be checked for the particular `bad` this
leaf chooses. It follows from `moduleFinite` for EVERY finite `bad`, by
Chebotarev plus the closedness of `ℤ_[ℓ]`-submodules of a module-finite
`ℤ_[ℓ]`-algebra; the argument is written out in `HilbertHeckeAlgebra`'s
docstring, where it replaces a monotonicity claim that was false. So the
`bad`-dependence of the interface, which looked like a trap, is not one.

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

  **This bullet is where the level lowering of the whole cluster lives, and
  it is the ONLY place it lives** (audit 2026-07-26, by the owner of
  `exists_hilbertHeckeDatum_of_hilbertHeckeAlgebra`). That leaf's docstring
  used to advertise itself as the level-lowering step; it is not, because
  `HilbertHeckeAlgebra` pins the minimal level by fiat and there is
  therefore no non-minimal Hecke algebra for it to lower. See the
  FORMAL-CONTENT AUDIT there.
* **The topology of `T`** — `isAdic` and `isAdicComplete`, added to
  `HilbertHeckeAlgebra` on 2026-07-26 by the same audit. Classically these
  cost this leaf NOTHING: the localized Hecke algebra of a fixed weight and
  level is finite free over `ℤ_[ℓ]` and carries the `ℓ`-adic topology, which
  is its maximal-adic topology (`T/ℓT` is Artinian local) and for which it is
  complete and separated (`T ≅ ℤ_[ℓ] ^ n` as a module). They are stated
  because `IsHilbertHardlyRamified` is a continuity condition and so depends
  on which topology `T` carries; producing `ρT` continuous for an
  unspecified topology would have recorded nothing.

One further component hides inside `isHilbertHardlyRamified.det`, which asks
for the cyclotomic determinant ON THE NOSE. A parallel-weight-`2` Hilbert
newform has `det ρ_f = χ_ℓ · ε` with `ε` the nebentypus; `ε` is trivial mod
`ℓ` because `det ρbar = χ̄_ℓ`, so `ε` has `ℓ`-power order, and for odd `ℓ`
it has a unique square root `ε^{1/2}` of `ℓ`-power order. Twisting `ρT` by
`ε^{−1/2}` restores `det = χ_ℓ` and changes neither the residual
representation nor `Module.Finite`/`Module.Free`. So the clause is
satisfiable; it is not a hidden falsity, but it is one more thing the
citation quietly assumes.

Neither theorem is reachable at this mathlib pin. A survey by the owner of
the neighbouring `PotentialModularityWitness` interface established that
there is NO Weil group anywhere in mathlib or in the reference FLT project,
no local class field theory, no smooth or admissible representations, and a
54-line ramification-group development with a TODO for the higher groups.

## THREE REFUTED CUTS — none of them may be rebuilt

1. **`F = ℚ`, i.e. decoupling `F` from the Hecke algebra.** Splitting this
   leaf into "there is a totally real Galois `F` with `ρbar|_{G_F}`
   irreducible" and "for such an `F` a `HilbertHeckeAlgebra` exists" is
   UNSOUND, not merely useless. The first half is discharged by `F = ℚ`
   (collapse (2) of the audit above), and the second half then reads as
   `ℚ`-level modularity of `ρbar` — the statement pillar α proves OVER this
   leaf. The coupling between the choice of `F` and the existence of the
   newform over it IS the content, and every cut that breaks it manufactures
   a circularity.
2. **The piecewise / Brauer route.** Solvable base change does not preserve
   unramifiedness downwards, and `Ind` of an unramified representation is
   unramified at `p` only when `p` is unramified in the intermediate field —
   classically the pieces' ramification cancels in the VIRTUAL SUM, which is
   invisible piecewise. The citation has to be taken on the sum.
3. **Descent to a residually dihedral restriction.** The one cheap route to
   a characteristic-zero lift is to choose `F` so that `ρbar|_{G_F}` becomes
   dihedral, and then induce a lift of a Hecke character. It does not work
   uniformly, and the obstruction is exactly Dickson's classification.
   `PotentialHeckeDatum` demands `IsGalois ℚ F`, i.e. `G_F ⊴ Γ ℚ`, so the
   projective image `N` of `ρbar|_{G_F}` must be NORMAL in the projective
   image `P` of `ρbar`; and `irreducibleF` forbids `N` cyclic. When
   `P ⊇ PSL₂(𝔽_q)`, `q ≥ 5` — the generic case — the normal subgroups of `P`
   are `1`, `PSL₂(𝔽_q)` and `P`, none of them dihedral of order `≥ 4`, so
   the route is blocked outright. It succeeds only in small exceptional
   cases (`P ≅ A₄`, where `N = V₄` is normal and dihedral and contains the
   involution `ρbar c`, so the fixed field is totally real of degree `3`),
   and when `ρbar` is already dihedral over `ℚ`. So the hard core of this
   leaf is precisely the Dickson-large case, and no collapse reaches it.

Together these are why no cut of this leaf into smaller Lean statements
reduces what is assumed; it would only rename it.

## NARROWINGS IDENTIFIED, AND WHY THEY ARE NOT MADE HERE

Three genuine reductions of what this leaf assumes exist. All three are
edits to `HilbertHeckeAlgebra`, which had THREE concurrent owners on
2026-07-26 (`exists_hilbertHeckeDatum_of_hilbertHeckeAlgebra`,
`surjective_classifyingMap_hilbertHeckeDatum`,
`injective_classifyingMap_hilbertHeckeDatum` were all in flight), so they
are recorded rather than made:

* **`heckeT` and `charFrobT` are a redundant pair.** `charFrobT` says
  `heckeT w = −(ρT.charFrob w).coeff 1` for every good `w`, i.e. it DEFINES
  `heckeT` off `ρT`. Making `heckeT` a `def` on the structure and
  `charFrobT` a `rfl`-level lemma of the same names would delete two
  obligations from this leaf and break no consumer.
* **Level minimality is charged TWICE.** `isHilbertHardlyRamified` is the
  minimal-level condition, so this leaf already performs level lowering —
  and `exists_hilbertHeckeDatum_of_hilbertHeckeAlgebra`, whose whole stated
  job is to produce "the Hecke algebra of the MATCHING level", is charged
  with it again. The interface has no vocabulary for a Hecke algebra "of
  some level", which is why the double charge cannot be removed from this
  side. The honest repair is on the structure.
* **The `W(k)` base change should be PROVEN, not cited.** `πT_surjective`
  plus the Teichmüller half of `adjoin_heckeT` is precisely the assertion
  that `T` is the local factor of `𝕋_𝔪 ⊗_{ℤ_[ℓ]} W(k)`. That passage is
  pure commutative algebra — Witt vectors of a finite field, an unramified
  base change, and the splitting of a finite algebra over a complete local
  ring into local factors — and formalizing it would return this leaf to the
  classical `ℤ_ℓ`-Hecke algebra. It is a substantial construction at this
  pin (mathlib has `WittVector` but not the idempotent decomposition of a
  finite algebra over `ℤ_[ℓ]` in usable form), so it is named here as the
  next real reduction rather than attempted.

TERMINALITY VERDICT (2026-07-26): the arithmetic residue — Moret–Bailly /
Taylor, plus Carayol / Taylor with level lowering — is IRREDUCIBLY a
citation at this pin. What is reducible is the packaging, and all of it
lives in `HilbertHeckeAlgebra`. -/
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
| `exists_isLocalRing_traceSubring` | `exists_isLocalRing_hilbertTraceSubring` | PROVEN |
| `fg_comap_maximalIdeal_traceSubring` | `fg_comap_maximalIdeal_hilbertTraceSubring` | LEAF |
| `exists_framedGaloisRep_traceSubring` | `exists_framedGaloisRep_hilbertTraceSubring` | PROVEN |
| `exists_framedGaloisRep_baseChange_traceSubring` | `exists_framedGaloisRep_baseChange_hilbertTraceSubring` | LEAF |
| `isFlatAt_of_baseChange_traceSubring` | `isFlatAt_of_subring_baseChange_of_numberField` | PROVEN over a Raynaud LEAF |
| `isTameAtTwo_of_baseChange_traceSubring` | `isHilbertTameAtTwo_of_baseChange_hilbertTraceSubring` | PROVEN over a retraction LEAF |
| — (no `ℚ`-level counterpart) | `exists_ringHom_retraction_hilbertTraceSubring` | LEAF |
| `traceSubring_eq_top_of_charFrob_map` | `hilbertTraceSubring_eq_top_of_charpoly_map` | PROVEN |
| `exists_isTraceGenerated_ringHom_of_forall_trace_mem` | `exists_hilbertTraceDescent` | PROVEN |
| `exists_isWeaklyUniversal_isTraceGenerated_of_isWeaklyUniversal` | the target below | PROVEN |

**ONE `F`-LEVEL LEAF HAS NO `ℚ`-LEVEL COUNTERPART, AND THAT ONE IS NOT A
SIMPLIFICATION BUT A REPAIR** (2026-07-26).
`exists_ringHom_retraction_hilbertTraceSubring` is new at this level because
the `ℚ`-level tame descent buys the corresponding content from ARITHMETIC —
some `g₀ ∈ Γ ℚ_2` has `χ_ℓ(g₀) ≢ 1 (mod ℓ)`, so the two residual characters
at `2` are distinct and the eigen-projector is defined over `R'`. Over a
general `F_w ∣ 2` that input is simply false (`F = ℚ(ζ₇)⁺`, `ℓ = 7`), and
the tame descent is then FALSE without a retraction; the full refutation,
with an explicit witness, is in the FALSITY AUDIT of
`isHilbertTameAtTwo_of_baseChange_hilbertTraceSubring`. So the `F` level
needs one leaf that the `ℚ` level does not.

**ONE `ℚ`-LEVEL LEAF HAS NO `F`-LEVEL COUNTERPART, AND THAT ONE IS A REAL
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

**THE COMMUTATIVE-ALGEBRA HELPERS BELOW ARE LOCAL COPIES**, for the
same reason as `rank_finTwoPi`, `teichmullerRootSet` and `framePushforward`
above: their originals are in `Deformation.lean`, which is DOWNSTREAM. Two
further copies (`charpoly_baseChange_conj_hilbert`, `one_tmul_injective_hilbert`)
came with `exists_framedGaloisRep_hilbertTraceSubring`, three more
(`isUnit_of_isClosed_subring_of_notMem_maximalIdeal`,
`isLocalRing_of_isClosed_subring_of_finite_residueField`,
`maximalIdeal_eq_comap_of_isClosed_subring_of_finite_residueField`) with
`exists_isLocalRing_hilbertTraceSubring`, and one more
(`exists_frameCoords_of_baseChange_conj_hilbert`) with the repaired
`isHilbertTameAtTwo_of_baseChange_hilbertTraceSubring` — all three proofs
landing 2026-07-26.
That makes FOURTEEN duplicated helpers in this module now.  The three
`_hilbert`-suffixed ones (`charpoly_baseChange_conj_hilbert`,
`one_tmul_injective_hilbert`, `exists_frameCoords_of_baseChange_conj_hilbert`)
carry names DIFFERENT from their `ℚ`-level originals on purpose, both files
living in namespace `GaloisRepresentation`. Hoisting the shared
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

/-- **The residual field of an `F`-level datum has characteristic `ℓ`**
(PROVEN, elementary): the coefficient ring of a `HilbertDeformationDatum`
is a `ℤ_ℓ`-algebra surjecting onto `k`, so `k` receives `ℤ_ℓ` as well, and
a FINITE field receiving `ℤ_ℓ` has characteristic `ℓ`
(`natCast_eq_zero_of_finite_algebra`).

This is what lets `exists_isLocalRing_hilbertTraceSubring` below feed the
side condition `hlk` to its arithmetic leaf without carrying an
`[Algebra ℤ_[ℓ] k]` binder of its own: the datum already supplies one. -/
lemma natCast_eq_zero_of_hilbertDeformationDatum (ℓ : ℕ) [Fact ℓ.Prime]
    {F : Type u} [Field F] [NumberField F]
    {k : Type u} [Field k] [Finite k] [TopologicalSpace k]
    {V : Type v} [AddCommGroup V] [Module k V] [Module.Finite k V]
    [Module.Free k V]
    {ρbar : GaloisRep ℚ k V} (𝒟 : HilbertDeformationDatum ℓ F ρbar) :
    ((ℓ : ℕ) : k) = 0 := by
  letI : Algebra ℤ_[ℓ] k := (𝒟.π.comp (algebraMap ℤ_[ℓ] 𝒟.R)).toAlgebra
  exact natCast_eq_zero_of_finite_algebra ℓ k

open Filter Topology in
/-- **A closed subring of an adically topologized local ring with finite
residue field contains the inverse of every element of its own outside
`𝔪`** (PROVEN; NINTH local copy of a `Deformation.lean` helper — the
original is `isUnit_of_isClosed_of_notMem_maximalIdeal`, which lives
DOWNSTREAM of this module and so cannot be imported. The name differs from
the `ℚ`-level one deliberately: both files live in namespace
`GaloisRepresentation`, and a silently colliding duplicate has broken
`Deformation.lean` through the re-exported namespace once already.)

The residue of `x` is a nonzero element of the FINITE field `A ⧸ 𝔪`, so
`x ^ (q − 1) = 1 − y` with `q = |A ⧸ 𝔪|` and `y ∈ 𝔪 ∩ C`; the geometric
series `∑ yⁱ`, whose partial sums all lie in `C`, converges in `A` to the
inverse of `1 − y`, because `y ^ N ∈ 𝔪 ^ N → 0` for the adic topology.
`C` is closed, so that inverse lies in `C`, and
`x⁻¹ = x ^ (q − 2) · (x ^ (q − 1))⁻¹`.

No completeness of `A` is used: the limit is exhibited as an inverse that
already exists in the LOCAL ring `A`. -/
theorem isUnit_of_isClosed_subring_of_notMem_maximalIdeal {A : Type*}
    [CommRing A] [TopologicalSpace A] [IsLocalRing A]
    [Finite (IsLocalRing.ResidueField A)]
    (hadic : IsAdic (IsLocalRing.maximalIdeal A))
    {C : Subring A} (hC : IsClosed (C : Set A)) (x : C)
    (hx : (x : A) ∉ IsLocalRing.maximalIdeal A) : IsUnit x := by
  classical
  haveI : Fintype (IsLocalRing.ResidueField A) := Fintype.ofFinite _
  set q := Fintype.card (IsLocalRing.ResidueField A)
  have hq1 : 0 < q - 1 := Nat.sub_pos_of_lt Fintype.one_lt_card
  -- `x ^ (q - 1) = 1 - y` with `y ∈ 𝔪 ∩ C`
  have hres : IsLocalRing.residue A ((x : A) ^ (q - 1)) = 1 := by
    rw [map_pow]
    exact FiniteField.pow_card_sub_one_eq_one _
      (fun hz => hx ((IsLocalRing.residue_eq_zero_iff _).mp hz))
  set y : C := 1 - x ^ (q - 1) with hy
  have hyc : ((y : C) : A) = 1 - (x : A) ^ (q - 1) := by rw [hy]; push_cast; ring
  have hyR : (y : A) ∈ IsLocalRing.maximalIdeal A := by
    rw [← IsLocalRing.residue_eq_zero_iff, hyc, map_sub, hres, map_one, sub_self]
  have hone : (1 : A) - (y : A) = (x : A) ^ (q - 1) := by rw [hyc]; ring
  -- the inverse of `1 - y` in `A`
  have hu : IsUnit ((1 : A) - (y : A)) := by
    rw [← IsLocalRing.notMem_maximalIdeal, hone]
    intro hmem
    exact hx ((Ideal.IsPrime.pow_mem_iff_mem
      ((IsLocalRing.maximalIdeal.isMaximal A).isPrime) _ hq1).mp hmem)
  set u := hu.unit
  set L : A := ((u⁻¹ : Aˣ) : A) with hL
  have huL : ((1 : A) - (y : A)) * L = 1 := by
    rw [hL, show ((1 : A) - (y : A)) = (u : A) from (hu.unit_spec).symm]
    exact u.mul_inv
  -- the partial sums of the geometric series lie in `C`
  set s : ℕ → C := fun N => ∑ i ∈ Finset.range N, y ^ i with hs
  have hsc : ∀ N, ((s N : C) : A) = ∑ i ∈ Finset.range N, (y : A) ^ i := by
    intro N
    rw [hs]
    push_cast
    rfl
  have hsL : ∀ N, L - ((s N : C) : A) = L * (y : A) ^ N := by
    intro N
    have h1 : ((1 : A) - (y : A)) * ((s N : C) : A) = 1 - (y : A) ^ N := by
      rw [hsc]; exact mul_neg_geom_sum _ _
    have h2 : ((s N : C) : A) = L * (1 - (y : A) ^ N) := by
      calc ((s N : C) : A) = (L * ((1 : A) - (y : A))) * ((s N : C) : A) := by
            rw [mul_comm L, huL, one_mul]
        _ = L * (((1 : A) - (y : A)) * ((s N : C) : A)) := by ring
        _ = L * (1 - (y : A) ^ N) := by rw [h1]
    rw [h2]; ring
  -- so their limit `L` lies in `C`
  have htend : Tendsto (fun N => ((s N : C) : A)) atTop (𝓝 L) := by
    rw [(hadic.hasBasis_nhds L).tendsto_right_iff]
    intro n _
    filter_upwards [eventually_ge_atTop n] with N hN
    refine ⟨-(L * (y : A) ^ N), ?_, ?_⟩
    · refine Ideal.pow_le_pow_right hN ?_
      exact neg_mem (Ideal.mul_mem_left _ _ (Ideal.pow_mem_pow hyR N))
    · rw [← hsL N]; ring
  have hLC : L ∈ C := hC.mem_of_tendsto htend (.of_forall fun N => (s N).2)
  -- hence `1 - y = x ^ (q - 1)` is a unit of `C`, and therefore so is `x`
  have hunit : IsUnit (1 - y : C) := by
    refine ⟨⟨1 - y, ⟨L, hLC⟩, ?_, ?_⟩, rfl⟩
    · ext
      push_cast
      exact huL
    · ext
      push_cast
      rw [mul_comm]
      exact huL
  have hxq : IsUnit (x ^ (q - 1) : C) := by
    have hxy : (1 - y : C) = x ^ (q - 1) := by rw [hy]; ring
    rwa [hxy] at hunit
  refine isUnit_of_mul_isUnit_left (y := x ^ (q - 1 - 1)) ?_
  have hpow : x * x ^ (q - 1 - 1) = x ^ (q - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  rw [hpow]
  exact hxq

/-- **A closed subring of a local ring with finite residue field and adic
topology is LOCAL** (PROVEN; local copy of `Deformation.lean`'s
`isLocalRing_of_isClosed_subring`, under a distinct name — see the note on
the previous lemma): the nonunits of `C` are exactly `𝔪 ∩ C` by
`isUnit_of_isClosed_subring_of_notMem_maximalIdeal`, and that is an
ideal. -/
theorem isLocalRing_of_isClosed_subring_of_finite_residueField {A : Type*}
    [CommRing A] [TopologicalSpace A] [IsLocalRing A]
    [Finite (IsLocalRing.ResidueField A)]
    (hadic : IsAdic (IsLocalRing.maximalIdeal A))
    {C : Subring A} (hC : IsClosed (C : Set A)) : IsLocalRing C := by
  haveI : Nontrivial C := ⟨⟨0, 1, fun hz => zero_ne_one (congrArg Subtype.val hz)⟩⟩
  refine IsLocalRing.of_nonunits_add ?_
  intro a b ha hb
  have hmem : ∀ c : C, c ∈ nonunits C → (c : A) ∈ IsLocalRing.maximalIdeal A := by
    intro c hc
    by_contra hcm
    exact hc (isUnit_of_isClosed_subring_of_notMem_maximalIdeal hadic hC c hcm)
  intro hab
  have hsum : ((a : A) + (b : A)) ∈ IsLocalRing.maximalIdeal A :=
    Ideal.add_mem _ (hmem a ha) (hmem b hb)
  have hunit : IsUnit ((a : A) + (b : A)) := by simpa using hab.map C.subtype
  exact IsLocalRing.notMem_maximalIdeal.mpr hunit hsum

/-- **The maximal ideal of such a closed subring is `𝔪 ∩ C`** (PROVEN;
local copy of `Deformation.lean`'s
`maximalIdeal_eq_comap_of_isClosed_subring`, under a distinct name). -/
theorem maximalIdeal_eq_comap_of_isClosed_subring_of_finite_residueField
    {A : Type*} [CommRing A] [TopologicalSpace A] [IsLocalRing A]
    [Finite (IsLocalRing.ResidueField A)]
    (hadic : IsAdic (IsLocalRing.maximalIdeal A))
    {C : Subring A} (hC : IsClosed (C : Set A)) [IsLocalRing C] :
    IsLocalRing.maximalIdeal C =
      Ideal.comap C.subtype (IsLocalRing.maximalIdeal A) := by
  ext a
  rw [IsLocalRing.mem_maximalIdeal, Ideal.mem_comap]
  constructor
  · intro ha
    by_contra hcm
    exact ha (isUnit_of_isClosed_subring_of_notMem_maximalIdeal hadic hC a hcm)
  · intro ha hu
    have hunit : IsUnit (a : A) := by simpa using hu.map C.subtype
    exact IsLocalRing.notMem_maximalIdeal.mpr hunit ha

/-- **A uniform generator bound from level-wise surjections** (PROVEN,
pure commutative algebra with no arithmetic input; another local copy of
a `Deformation.lean` helper — `exists_uniform_span_maximalIdeal_of_forall_surjective`
— which lives DOWNSTREAM of this module and so is unusable here; see the
duplication-debt note in the "Formal prerequisites (local copies)"
subsection above).

If ONE fixed Noetherian local ring `S` surjects onto every quotient
`C ⧸ J n` of a local ring `C`, then the number `r` of generators of
`𝔪_S` bounds, UNIFORMLY in `n`, the number of elements of `𝔪_C` needed
to generate it modulo `J n`. The proof is the obvious one: pull a
generating family of `𝔪_S` through the surjection `S ↠ C ⧸ J n`, lift it
along `C ↠ C ⧸ J n`, and note that the maximal ideal of a local ring maps
onto the maximal ideal of any surjective image
(`IsLocalRing.map_maximalIdeal_of_surjective`). The level `J n = ⊤` is
handled separately, with the empty span. -/
theorem exists_uniform_span_maximalIdeal_of_forall_surjective_hilbert
    {C : Type*} [CommRing C] [IsLocalRing C]
    {S : Type*} [CommRing S] [IsLocalRing S] [IsNoetherianRing S]
    (J : ℕ → Ideal C)
    (hf : ∀ n : ℕ, ∃ f : S →+* (C ⧸ J n), Function.Surjective f) :
    ∃ r : ℕ, ∀ n : ℕ, ∃ z : Fin r → C,
      Ideal.span (Set.range z) ≤ IsLocalRing.maximalIdeal C ∧
        IsLocalRing.maximalIdeal C ≤ Ideal.span (Set.range z) ⊔ J n := by
  obtain ⟨r, s, hs⟩ :=
    Submodule.fg_iff_exists_fin_generating_family.mp
      (IsNoetherian.noetherian (IsLocalRing.maximalIdeal S))
  refine ⟨r, fun n => ?_⟩
  by_cases hJ : J n = ⊤
  · refine ⟨fun _ => 0, ?_, ?_⟩
    · exact Ideal.span_le.mpr (by rintro x ⟨i, rfl⟩; exact Submodule.zero_mem _)
    · rw [hJ, sup_top_eq]
      exact le_top
  · haveI : Nontrivial (C ⧸ J n) := Ideal.Quotient.nontrivial_iff.mpr hJ
    obtain ⟨f, hfsurj⟩ := hf n
    haveI : IsLocalRing (C ⧸ J n) := IsLocalRing.of_surjective' f hfsurj
    have hq : Function.Surjective (Ideal.Quotient.mk (J n)) :=
      Ideal.Quotient.mk_surjective
    have hmapS : Ideal.map f (IsLocalRing.maximalIdeal S) =
        IsLocalRing.maximalIdeal (C ⧸ J n) :=
      IsLocalRing.map_maximalIdeal_of_surjective f hfsurj
    have hmapC : Ideal.map (Ideal.Quotient.mk (J n)) (IsLocalRing.maximalIdeal C) =
        IsLocalRing.maximalIdeal (C ⧸ J n) :=
      IsLocalRing.map_maximalIdeal_of_surjective _ hq
    have hmem : ∀ i : Fin r, f (s i) ∈
        Ideal.map (Ideal.Quotient.mk (J n)) (IsLocalRing.maximalIdeal C) := by
      intro i
      rw [hmapC, ← hmapS]
      exact Ideal.mem_map_of_mem f (by rw [← hs]; exact Ideal.subset_span ⟨i, rfl⟩)
    choose z hz hzq using fun i => Ideal.mem_map_iff_of_surjective _ hq |>.mp (hmem i)
    refine ⟨z, Ideal.span_le.mpr ?_, ?_⟩
    · rintro x ⟨i, rfl⟩; exact hz i
    · intro x hx
      have hx' : (Ideal.Quotient.mk (J n)) x ∈
          Ideal.map (Ideal.Quotient.mk (J n)) (Ideal.span (Set.range z)) := by
        have h1 : Ideal.map (Ideal.Quotient.mk (J n)) (Ideal.span (Set.range z)) =
            Ideal.span (Set.range (fun i => (Ideal.Quotient.mk (J n)) (z i))) := by
          rw [Ideal.map_span, ← Set.range_comp]; rfl
        have h2 : Ideal.span (Set.range (fun i => (Ideal.Quotient.mk (J n)) (z i))) =
            IsLocalRing.maximalIdeal (C ⧸ J n) := by
          rw [show (fun i => (Ideal.Quotient.mk (J n)) (z i)) = fun i => f (s i) from
            funext hzq, ← hmapS, ← hs, Ideal.map_span, ← Set.range_comp]
          rfl
        rw [h1, h2, ← hmapC]
        exact Ideal.mem_map_of_mem _ hx
      have hcm := (Ideal.comap_map_of_surjective _ hq (Ideal.span (Set.range z))) ▸
        (Ideal.mem_comap.mpr hx')
      rwa [← RingHom.ker_eq_comap_bot, Ideal.mk_ker] at hcm

/-- **Carayol's Théorème 1 at each FINITE level, over `F`** (LEAF — new
2026-07-26; the SOLE arithmetic input of
`fg_comap_maximalIdeal_hilbertTraceSubring` below, which is now PROVEN
over it): ONE fixed Noetherian local ring `S` surjects onto EVERY level
quotient `R' ⧸ (𝔪 ^ n ∩ R')` of Carayol's trace subring.

This is step 1 of the `ℚ`-level route that the leaf's docstring below
records, and it is the `F`-level twin of `Deformation.lean`'s PROVEN
`exists_noetherianLocal_surjective_quotient_traceSubring`. The witness
there is the WEAKLY UNIVERSAL ring of the deformation problem, which
surjects onto every finite level because at a FINITE level the trace
subring carries no ring-theoretic burden at all — it is finite, hence
Noetherian; closed, hence local; and its maximal ideal is nilpotent,
hence adic and complete. Level `0` is separate: the quotient is the zero
ring.

NOT CIRCULAR. The finite-level conjugation input is the sibling leaf
`exists_framedGaloisRep_hilbertTraceSubring`, which takes the locality of
the trace subring as its HYPOTHESIS `hloc` rather than proving it; at
finite level that locality is free, which is exactly why the two may be
used in this order.

WHY THIS AND NOT THE WHOLE LEAF. Everything else in
`fg_comap_maximalIdeal_hilbertTraceSubring` is formal and is now written
out below: the uniform generator bound is
`exists_uniform_span_maximalIdeal_of_forall_surjective_hilbert` above
(pure commutative algebra), and the passage from level-wise tuples to a
SINGLE tuple is `ProfiniteLocal.fg_comap_of_uniform_span`, already
UPSTREAM of this module. So this leaf is where the counterexample
`k[[x, xy, xy², …]] ⊂ k[[x,y]]` bites, and the Carayol hypotheses
(`hℓ5`, irreducibility of `ρbar|_{G_F}`, and the local conditions inside
`𝒟.isHilbertHardlyRamified`) are load-bearing HERE and nowhere else in
the package.

**ROUTE AUDIT 2026-07-26 (flt-lean-133): "port the `ℚ`-level proof" is NOT
available under the hypotheses as stated. Read this before being dispatched
here.** The route recorded above is right about the MATHEMATICS and wrong
about the availability, on two independent counts, both checked by reading
the declarations rather than inferred:

1. *The first step of the `ℚ` proof has no usable `F`-level twin under these
   hypotheses.* `Deformation.lean`'s proof opens with
   `obtain ⟨Du, hDu⟩ := exists_isWeaklyUniversal …` and takes `Du.R` as the
   witness `S`. The `F`-level twin is
   `exists_isWeaklyUniversal_hilbertDeformationDatum` above — PROVEN, but it
   carries **`hw2`** (`∀ w ∣ 2, ℓ ∤ (Nw ^ 2 − 1)`, through
   `isHilbertFibreProductClause`) and the binders
   `[DiscreteTopology k] [Algebra ℤ_[ℓ] k]`. This leaf has NONE of the three:
   it has `hlk : (ℓ : k) = 0` and `[Finite k]` only. So the witness cannot be
   produced without either adding `hw2` (and the two `k`-binders) to this
   statement — a CUT-LEVEL change, since `fg_comap_maximalIdeal_hilbertTraceSubring`
   and everything above it would have to carry them too — or finding a
   witness that is not the weakly universal ring.
2. *Three of the finite-level helpers the `ℚ` proof consumes have no `F`-level
   twin at all* — there is no `quotientHilbertDeformationDatum` (the quotient
   of a datum by `𝔪 ^ n`, with its finiteness/openness/discreteness
   bookkeeping), no `exists_surjective_hilbertTraceSubring_of_finite`, and no
   `hilbertTraceSubring_map_of_discreteTopology`. Each is a declaration to be
   written here, not a name to be looked up. (`exists_framedGaloisRep_hilbertTraceSubring`
   is PROVEN but is a DIFFERENT statement: it produces a framed representation
   OVER `R'`, not a surjection ONTO a level quotient of `R'`.)

Consequence for whoever takes this next: the first decision is the
hypothesis question in (1), and it should be settled before any Lean is
written, because it changes the statement. Nothing in this audit contradicts
the mathematics recorded above; Carayol's Théorème 1 at finite level is still
the content, and the counterexample paragraph still explains why no purely
formal argument can work. -/
theorem exists_noetherianLocal_surjective_quotient_hilbertTraceSubring
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ5 : 5 ≤ ℓ) (F : Type u) [Field F] [NumberField F]
    {k : Type u} [Field k] [Finite k] [TopologicalSpace k]
    {V : Type v} [AddCommGroup V] [Module k V] [Module.Finite k V]
    [Module.Free k V]
    {ρbar : GaloisRep ℚ k V} (hlk : ((ℓ : ℕ) : k) = 0)
    (hirrF : (ρbar.map (algebraMap ℚ F)).IsIrreducible)
    (𝒟 : HilbertDeformationDatum ℓ F ρbar) :
    ∃ (S : Type u) (_ : CommRing S) (_ : IsLocalRing S) (_ : IsNoetherianRing S),
      ∀ n : ℕ, ∃ f : S →+* (hilbertTraceSubring ℓ 𝒟.ρ ⧸
          Ideal.comap (hilbertTraceSubring ℓ 𝒟.ρ).subtype
            ((IsLocalRing.maximalIdeal 𝒟.R) ^ n)),
        Function.Surjective f :=
  sorry

/-- **Finite generation of `𝔪' = 𝔪 ∩ R'`, at the `F` level** (PROVEN
2026-07-26 over the SINGLE arithmetic leaf
`exists_noetherianLocal_surjective_quotient_hilbertTraceSubring` above —
it was itself a leaf until then; the `F`-level twin of
`Deformation.lean`'s PROVEN `fg_comap_maximalIdeal_traceSubring`): the
maximal ideal of Carayol's closed trace subring
`R' = hilbertTraceSubring ℓ 𝒟.ρ` is finitely generated.

THE THREE-STEP ROUTE RECORDED BELOW IS NOW EXECUTED, and only step 1 is
left open. Step 1 is the leaf above; step 2 is
`exists_uniform_span_maximalIdeal_of_forall_surjective_hilbert`, proven
above as pure commutative algebra; step 3 is
`ProfiniteLocal.fg_comap_of_uniform_span`, already UPSTREAM. What this
proof adds is the profiniteness package the transfer needs: the residue
field of `𝒟.R` is `k`, hence finite, so every `𝒟.R ⧸ 𝔪 ^ n` is finite
and `𝒟.R` is compact (`compactSpace_of_isAdic_of_finite_quotient`) and
Hausdorff (`t2Space_of_isAdic_of_isHausdorff`); `R'` is a topological
closure, hence closed; and `𝔪' = 𝔪 ∩ R'`
(`maximalIdeal_eq_comap_of_isClosed_subring_of_finite_residueField`),
which is what lets the level-wise tuples of step 2 be read as tuples for
`𝔪'`.

**THIS IS THE WHOLE CONTENT of `exists_isLocalRing_hilbertTraceSubring`
below**, which is otherwise soft: `R'` is a closed subring of the
PROFINITE ring `𝒟.R`, hence profinite itself; it is local with
`𝔪' = 𝔪 ∩ R'` (`isLocalRing_of_isClosed_subring_of_finite_residueField`);
`𝔪'` is open; and a profinite local ring whose maximal ideal is open and
FINITELY GENERATED is adic, adically complete and — by Stacks 05GH —
Noetherian, which is
`ProfiniteLocalNoetherian.isAdic_isAdicComplete_of_isOpen_of_fg` plus
`CompleteLocalNoetherian.isNoetherianRing_of_isAdicComplete_of_fg`, both
UPSTREAM of this module. Note that this shape needs NO separate Lemme 1
leaf `∀ n, ∃ m, 𝔪 ^ m ∩ R' ⊆ 𝔪' ^ n`: over a profinite ring the two
filtrations are cofinal as soon as `𝔪'` is finitely generated, so the
`ℚ`-level pair of arithmetic leaves collapses to this single one here.

**WHY IT IS NOT FORMAL.** `C = k[[x, xy, xy², …]] ⊆ k[[x, y]]` is a closed
— indeed profinite — local subring of a complete Noetherian local ring
with the same finite residue field, whose maximal ideal is NOT finitely
generated (`𝔪_C ⧸ 𝔪_C ^ 2` is infinite dimensional, the `x y ⁿ` being
independent modulo `𝔪_C ^ 2 ⊆ (x ^ 2)`). So no argument using only
closedness can work, and the Carayol hypotheses — `hℓ5`, irreducibility of
`ρbar|_{G_F}`, and the local conditions bundled inside
`𝒟.isHilbertHardlyRamified` — are load-bearing here.

**THE `ℚ`-LEVEL ROUTE, which is the one to port**, and which is PROVEN
there in full:

1. `exists_noetherianLocal_surjective_quotient_traceSubring` — ONE fixed
   Noetherian local ring (the weakly universal ring) surjects onto EVERY
   level quotient `R' ⧸ (𝔪 ^ n ∩ R')`. This is Carayol's Théorème 1 run at
   each FINITE level `𝒟.R ⧸ 𝔪 ^ n`, where the trace subring carries no
   ring-theoretic burden at all — it is finite, hence Noetherian; closed,
   hence local; and its maximal ideal is nilpotent, hence adic and
   complete. The `F`-level conjugation input is the SIBLING leaf
   `exists_framedGaloisRep_hilbertTraceSubring`, which takes exactly that
   locality as its hypothesis `hloc`, so the use is NOT circular.
2. `exists_uniform_span_maximalIdeal_of_forall_surjective` (general
   commutative algebra, PROVEN in `Deformation.lean` and short enough to
   re-prove here) turns that into a UNIFORM bound: one `r`, the number of
   generators of the maximal ideal of that Noetherian ring, such that
   `𝔪'` is generated by `r` elements modulo every filtration step.
3. `ProfiniteLocal.fg_comap_of_uniform_span` (UPSTREAM, imported here)
   replaces the incompatible level-wise tuples by ONE tuple by compactness
   of `R' ^ r`, whence `𝔪'` is finitely generated outright.

`hlk` (`char k = ℓ`) is supplied by the consumer from the datum itself
(`natCast_eq_zero_of_hilbertDeformationDatum`); it is what makes the
Teichmüller roots of `𝒟.R` reduce ONTO `k`, hence what makes the residue
field of `R'` equal to `k` on the nose and the level quotients objects of
the `F`-level deformation category at all.

References: Carayol, *Formes modulaires et représentations galoisiennes à
valeurs dans un anneau local complet* (Contemp. Math. 165), Théorème 1 and
Lemme 1; Nyssen, *Pseudo-représentations*; Rouquier, *Caractérisation des
caractères et pseudo-caractères*; Mazur, *Deforming Galois
representations*, §1.6. -/
theorem fg_comap_maximalIdeal_hilbertTraceSubring
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ5 : 5 ≤ ℓ) (F : Type u) [Field F] [NumberField F]
    {k : Type u} [Field k] [Finite k] [TopologicalSpace k]
    {V : Type v} [AddCommGroup V] [Module k V] [Module.Finite k V]
    [Module.Free k V]
    {ρbar : GaloisRep ℚ k V} (hlk : ((ℓ : ℕ) : k) = 0)
    (hirrF : (ρbar.map (algebraMap ℚ F)).IsIrreducible)
    (𝒟 : HilbertDeformationDatum ℓ F ρbar) :
    (Ideal.comap (hilbertTraceSubring ℓ 𝒟.ρ).subtype
      (IsLocalRing.maximalIdeal 𝒟.R)).FG := by
  classical
  haveI : IsAdicComplete (IsLocalRing.maximalIdeal 𝒟.R) 𝒟.R := 𝒟.isAdicComplete
  haveI : IsHausdorff (IsLocalRing.maximalIdeal 𝒟.R) 𝒟.R :=
    (𝒟.isAdicComplete).toIsHausdorff
  -- the residue field of `𝒟.R` is `k`, hence FINITE
  have hker : RingHom.ker 𝒟.π = IsLocalRing.maximalIdeal 𝒟.R :=
    IsLocalRing.ker_eq_maximalIdeal 𝒟.π 𝒟.π_surjective
  haveI hresfin : Finite (IsLocalRing.ResidueField 𝒟.R) := by
    have hlift : IsLocalRing.ResidueField 𝒟.R →+* k :=
      Ideal.Quotient.lift (IsLocalRing.maximalIdeal 𝒟.R) 𝒟.π
        (fun a ha => by rwa [← RingHom.mem_ker, hker])
    exact Finite.of_injective hlift hlift.injective
  haveI hqfin : Finite (𝒟.R ⧸ IsLocalRing.maximalIdeal 𝒟.R) := hresfin
  -- **`𝒟.R` is profinite**, and `R'` is CLOSED in it
  haveI hT2 : T2Space 𝒟.R := t2Space_of_isAdic_of_isHausdorff 𝒟.isAdic
  have hmfg : (IsLocalRing.maximalIdeal 𝒟.R).FG :=
    IsNoetherian.noetherian (IsLocalRing.maximalIdeal 𝒟.R)
  haveI hcompact : CompactSpace 𝒟.R :=
    _root_.ProfiniteLocal.compactSpace_of_isAdic_of_finite_quotient 𝒟.isAdic
      (fun n => Ideal.finite_quotient_pow hmfg n)
  have hclosed : IsClosed ((hilbertTraceSubring ℓ 𝒟.ρ : Subring 𝒟.R) :
      Set 𝒟.R) := Subring.isClosed_topologicalClosure _
  haveI hloc : IsLocalRing (hilbertTraceSubring ℓ 𝒟.ρ) :=
    isLocalRing_of_isClosed_subring_of_finite_residueField 𝒟.isAdic hclosed
  have hmax : IsLocalRing.maximalIdeal (hilbertTraceSubring ℓ 𝒟.ρ) =
      Ideal.comap (hilbertTraceSubring ℓ 𝒟.ρ).subtype
        (IsLocalRing.maximalIdeal 𝒟.R) :=
    maximalIdeal_eq_comap_of_isClosed_subring_of_finite_residueField 𝒟.isAdic
      hclosed
  -- **the arithmetic input**: one Noetherian local ring onto every level
  obtain ⟨S, _, _, _, hS⟩ :=
    exists_noetherianLocal_surjective_quotient_hilbertTraceSubring ℓ hℓ5 F hlk
      hirrF 𝒟
  -- **the uniform bound**, then ONE tuple by compactness of `R'ʳ`
  obtain ⟨r, hr⟩ :=
    exists_uniform_span_maximalIdeal_of_forall_surjective_hilbert (S := S)
      (fun n => Ideal.comap (hilbertTraceSubring ℓ 𝒟.ρ).subtype
        ((IsLocalRing.maximalIdeal 𝒟.R) ^ n)) hS
  refine _root_.ProfiniteLocal.fg_comap_of_uniform_span 𝒟.isAdic _ hclosed
    (r := r) (fun n => ?_)
  obtain ⟨z, hz1, hz2⟩ := hr n
  rw [hmax] at hz1 hz2
  exact ⟨z, hz1, hz2⟩

/-- **Carayol's Lemme 1 at the `F` level** (PROVEN 2026-07-26 over
`fg_comap_maximalIdeal_hilbertTraceSubring` above — which is ITSELF now
proven, over the single arithmetic leaf
`exists_noetherianLocal_surjective_quotient_hilbertTraceSubring`;
the `F`-level twin of `Deformation.lean`'s `exists_isLocalRing_traceSubring`,
which is PROVEN there over its own four-way cut): the closed trace subring
`R' = hilbertTraceSubring ℓ 𝒟.ρ` is again a COEFFICIENT RING — local,
Noetherian, adically topologized and adically complete.

THE CONTENT IS NOETHERIANITY, and it is FALSE for a general closed subring
of a complete Noetherian local ring: `k[[x, xy, xy², …]]` inside `k[[x,y]]`
is a closed local subring with the same residue field and a
non-finitely-generated maximal ideal, and it also refutes Lemme 1. So the
Carayol hypotheses — `hℓ5`, irreducibility of `ρbar|_{G_F}`, and the local
conditions bundled inside `𝒟.isHilbertHardlyRamified` — are carried here
even though the SOFT HALF proven below consumes none of them. They are
passed, unspent, to the leaf, which is where that counterexample bites.

WHAT IS PROVEN HERE — the soft half, and it is shorter than the `ℚ`-level
one because this module has `ProfiniteLocalNoetherian.lean` UPSTREAM of it
where `Deformation.lean` does not:

* **`𝒟.R` is PROFINITE.** Its residue field is `k`, which is FINITE, so
  every `𝒟.R ⧸ 𝔪 ^ n` is finite (`Ideal.finite_quotient_pow`, over
  Noetherianity of `𝒟.R`); adic precompleteness then assembles the
  level-wise residues of an ultrafilter into a limit point
  (`ProfiniteLocal.compactSpace_of_isAdic_of_finite_quotient`), and adic
  separatedness gives Hausdorffness
  (`t2Space_of_isAdic_of_isHausdorff`).
* **`R'` is a CLOSED subring** of it, being a topological closure, hence
  compact and Hausdorff — profinite in its own right.
* **`R'` is LOCAL with `𝔪' = 𝔪 ∩ R'`**, outright and with no input from
  the trace data: `isLocalRing_of_isClosed_subring_of_finite_residueField`
  and `maximalIdeal_eq_comap_of_isClosed_subring_of_finite_residueField`.
* **`𝔪'` is OPEN** and the open ideals of `R'` are a neighbourhood basis
  of `0`, both by pulling the `𝔪`-adic basis of `𝒟.R` back along the
  (continuous, inducing) inclusion.
* **Adic, complete and Noetherian** then follow from FINITE GENERATION of
  `𝔪'` alone: `ProfiniteLocalNoetherian.isAdic_isAdicComplete_of_isOpen_of_fg`
  (a profinite local ring whose maximal ideal is open and finitely
  generated carries the `𝔪`-adic topology and is complete — the two
  filtrations are cofinal because `𝔪' ^ n` is then compact, hence closed,
  and of finite index, hence open) and
  `CompleteLocalNoetherian.isNoetherianRing_of_isAdicComplete_of_fg`
  (Stacks 05GH).

**THE `ℚ`-LEVEL PAIR OF ARITHMETIC LEAVES COLLAPSES TO ONE HERE.** Over
`ℚ` the same conclusion is assembled from BOTH
`fg_comap_maximalIdeal_traceSubring` and
`exists_pow_comap_le_pow_maximalIdeal_traceSubring` (Lemme 1 proper,
`∀ n, ∃ m, 𝔪 ^ m ∩ R' ⊆ 𝔪' ^ n`, by Chevalley's theorem in its
compactness form), because that file routes through
`isAdic_comap_maximalIdeal_of_forall_exists_le`, which needs the
cofinality as an input. Going through `isAdic_isAdicComplete_of_isOpen_of_fg`
instead derives the cofinality FROM finite generation, so only finite
generation is left to prove. The two `ℚ`-level leaves are of course
themselves proven over one arithmetic input; see the leaf's docstring for
the route to port.

The `[Finite k]` hypothesis is what makes the residue field of `𝒟.R`
finite, which the closed-subring machinery uses throughout; `char k = ℓ`
is not a hypothesis but a CONSEQUENCE of the datum
(`natCast_eq_zero_of_hilbertDeformationDatum`), and is passed to the leaf.

References: Carayol, *Formes modulaires et représentations galoisiennes à
valeurs dans un anneau local complet* (Contemp. Math. 165), Théorème 1 and
Lemme 1; Nyssen, *Pseudo-représentations*; Rouquier, *Caractérisation des
caractères et pseudo-caractères*; Stacks 05GH. -/
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
        (hilbertTraceSubring ℓ 𝒟.ρ) := by
  classical
  haveI : IsAdicComplete (IsLocalRing.maximalIdeal 𝒟.R) 𝒟.R := 𝒟.isAdicComplete
  haveI : IsHausdorff (IsLocalRing.maximalIdeal 𝒟.R) 𝒟.R :=
    (𝒟.isAdicComplete).toIsHausdorff
  -- **the residue field of `𝒟.R` is `k`**, hence finite
  have hker : RingHom.ker 𝒟.π = IsLocalRing.maximalIdeal 𝒟.R :=
    IsLocalRing.ker_eq_maximalIdeal 𝒟.π 𝒟.π_surjective
  haveI hresfin : Finite (IsLocalRing.ResidueField 𝒟.R) := by
    have hlift : IsLocalRing.ResidueField 𝒟.R →+* k :=
      Ideal.Quotient.lift (IsLocalRing.maximalIdeal 𝒟.R) 𝒟.π
        (fun a ha => by rwa [← RingHom.mem_ker, hker])
    exact Finite.of_injective hlift hlift.injective
  haveI hqfin : Finite (𝒟.R ⧸ IsLocalRing.maximalIdeal 𝒟.R) := hresfin
  -- **`𝒟.R` is profinite**: Hausdorff by adic separatedness, compact because
  -- every level `𝒟.R ⧸ 𝔪 ^ n` is finite and `𝒟.R` is adically precomplete
  haveI hT2 : T2Space 𝒟.R := t2Space_of_isAdic_of_isHausdorff 𝒟.isAdic
  have hmfg : (IsLocalRing.maximalIdeal 𝒟.R).FG :=
    IsNoetherian.noetherian (IsLocalRing.maximalIdeal 𝒟.R)
  haveI hcompact : CompactSpace 𝒟.R :=
    _root_.ProfiniteLocal.compactSpace_of_isAdic_of_finite_quotient 𝒟.isAdic
      (fun n => Ideal.finite_quotient_pow hmfg n)
  -- **`R'` is closed**, being a topological closure, hence profinite too
  have hclosed : IsClosed ((hilbertTraceSubring ℓ 𝒟.ρ : Subring 𝒟.R) :
      Set 𝒟.R) := Subring.isClosed_topologicalClosure _
  haveI : CompactSpace (hilbertTraceSubring ℓ 𝒟.ρ) :=
    isCompact_iff_compactSpace.mp hclosed.isCompact
  -- **`R'` is local**, with maximal ideal `𝔪 ∩ R'`
  haveI hloc : IsLocalRing (hilbertTraceSubring ℓ 𝒟.ρ) :=
    isLocalRing_of_isClosed_subring_of_finite_residueField 𝒟.isAdic hclosed
  have hmax : IsLocalRing.maximalIdeal (hilbertTraceSubring ℓ 𝒟.ρ) =
      Ideal.comap (hilbertTraceSubring ℓ 𝒟.ρ).subtype
        (IsLocalRing.maximalIdeal 𝒟.R) :=
    maximalIdeal_eq_comap_of_isClosed_subring_of_finite_residueField 𝒟.isAdic
      hclosed
  -- **the open ideals of `R'` are a neighbourhood basis of `0`**: pull the
  -- `𝔪`-adic basis of `𝒟.R` back along the inclusion, which is inducing
  have hcomapopen : ∀ n : ℕ, IsOpen ((Ideal.comap
      (hilbertTraceSubring ℓ 𝒟.ρ).subtype
        ((IsLocalRing.maximalIdeal 𝒟.R) ^ n) :
      Ideal (hilbertTraceSubring ℓ 𝒟.ρ)) :
      Set (hilbertTraceSubring ℓ 𝒟.ρ)) := by
    intro n
    exact ((isAdic_iff.mp 𝒟.isAdic).1 n).preimage continuous_subtype_val
  have hbasis : ∀ U ∈ nhds (0 : hilbertTraceSubring ℓ 𝒟.ρ),
      ∃ I : Ideal (hilbertTraceSubring ℓ 𝒟.ρ),
        IsOpen ((I : Ideal (hilbertTraceSubring ℓ 𝒟.ρ)) :
          Set (hilbertTraceSubring ℓ 𝒟.ρ)) ∧
        ((I : Ideal (hilbertTraceSubring ℓ 𝒟.ρ)) :
          Set (hilbertTraceSubring ℓ 𝒟.ρ)) ⊆ U := by
    intro U hU
    rw [nhds_induced, Filter.mem_comap] at hU
    obtain ⟨t, ht, hts⟩ := hU
    obtain ⟨n, hn⟩ := (isAdic_iff.mp 𝒟.isAdic).2 t (by simpa using ht)
    exact ⟨Ideal.comap (hilbertTraceSubring ℓ 𝒟.ρ).subtype
      ((IsLocalRing.maximalIdeal 𝒟.R) ^ n), hcomapopen n,
      fun z hz => hts (hn hz)⟩
  -- **`𝔪'` is open**, being the preimage of the open `𝔪`
  have hopen : IsOpen ((IsLocalRing.maximalIdeal (hilbertTraceSubring ℓ 𝒟.ρ) :
      Ideal (hilbertTraceSubring ℓ 𝒟.ρ)) :
      Set (hilbertTraceSubring ℓ 𝒟.ρ)) := by
    rw [hmax, ← pow_one (IsLocalRing.maximalIdeal 𝒟.R)]
    exact hcomapopen 1
  -- **`𝔪'` is finitely generated**: the arithmetic leaf, whose side condition
  -- `char k = ℓ` the datum itself supplies
  have hfg : (IsLocalRing.maximalIdeal (hilbertTraceSubring ℓ 𝒟.ρ)).FG := by
    rw [hmax]
    exact fg_comap_maximalIdeal_hilbertTraceSubring ℓ hℓ5 F
      (natCast_eq_zero_of_hilbertDeformationDatum ℓ 𝒟) hirrF 𝒟
  -- **assemble**: open + finitely generated maximal ideal in a profinite local
  -- ring gives adic and complete, and Stacks 05GH gives Noetherian
  obtain ⟨hadic', hcompl'⟩ :=
    _root_.ProfiniteLocalNoetherian.isAdic_isAdicComplete_of_isOpen_of_fg
      hbasis hopen hfg
  exact ⟨hloc, _root_.CompleteLocalNoetherian.isNoetherianRing_of_isAdicComplete_of_fg
    hcompl' hfg, hadic', hcompl'⟩

/-! #### Machinery for Carayol's Théorème 1 at the `F` level

`Deformation.lean` proves the `ℚ`-level twin
`exists_framedGaloisRep_traceSubring` over a THREE-way cut: the
Rouquier–Nyssen descent of the representation itself
(`exists_framedGaloisRep_baseChange_traceSubring`) and the two
local-condition descents `isFlatAt_of_baseChange_traceSubring`,
`isTameAtTwo_of_baseChange_traceSubring`; the determinant and
unramifiedness clauses are discharged formally in the assembly, from
injectivity of the inclusion `R' → 𝒟.R` and from the frame identity.

The same cut is taken here, with ONE improvement. The `ℚ`-level flat
descent is itself proven from the general `isFlatAt_of_subring_baseChange`
— a statement about an arbitrary subring of an `𝔪`-adic local ring, with
the Carayol package stripped away — whose proof transports verbatim to a
variable number field. Both are ported below and PROVEN, so what remains
open on the flat side is only the RAYNAUD sub-object closure
`hasFlatProlongationAt_of_injection_of_numberField`, the exact sibling of
the leaf `hasFlatProlongationAt_of_pi_surjection_of_numberField` already
present in this module. That is a strictly shallower leaf than a bespoke
"flatness descends to the trace subring" statement would be, and it is
reusable.

DUPLICATION NOTE (see the head of this file). `Deformation.lean` is
DOWNSTREAM of this module and cannot be imported from here, so the two
transport helpers below are LOCAL COPIES of originals there
(`charpoly_baseChange_conj`, `one_tmul_injective`), stated over a variable
base number field rather than over `ℚ`. They carry `_hilbert`-suffixed
names deliberately: a duplicated `det_pushforwardFrame` once silently
broke `Deformation.lean` through the re-exported namespace. -/

set_option backward.isDefEq.respectTransparency false in
open scoped TensorProduct in
/-- **Characteristic-polynomial transport through base change and framing**
(PROVEN; the local copy, over a VARIABLE base number field, of
`Deformation.lean`'s `charpoly_baseChange_conj`, which is stated at
`K = ℚ`): the descent identity `(τ ⊗ B)ᵉ = σ` identifies the
characteristic polynomials of `σ` with the images of those of `τ` under
the coefficient map.

`LinearEquiv.charpoly_conj` kills the framing and
`LinearMap.charpoly_baseChange` turns the base change into `Polynomial.map
(algebraMap A B)`; the intermediate `show` identifies
`GaloisRep.baseChange` — opaque across the module boundary — with
`LinearMap.baseChange`. -/
lemma charpoly_baseChange_conj_hilbert {K : Type u} [Field K] [NumberField K]
    {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    {B : Type*} [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
    [Algebra A B] [ContinuousSMul A B]
    {W : Type*} [AddCommGroup W] [Module A W] [Module.Finite A W]
    [Module.Free A W] {N : Type*} [AddCommGroup N] [Module B N]
    [Module.Finite B N] [Module.Free B N]
    (τ : GaloisRep K A W) (e : (B ⊗[A] W) ≃ₗ[B] N) (g : Γ K) :
    (((τ.baseChange B).conj e) g).charpoly =
      ((τ g).charpoly).map (algebraMap A B) := by
  rw [GaloisRep.conj_apply, LinearEquiv.charpoly_conj]
  show ((Module.End.baseChangeHom A B W) (τ g)).charpoly = _
  rw [show (Module.End.baseChangeHom A B W) (τ g) =
    LinearMap.baseChange B (τ g) from rfl, LinearMap.charpoly_baseChange]

open scoped TensorProduct in
/-- **`1 ⊗ ·` is injective on a standard frame** (PROVEN; the local copy of
`Deformation.lean`'s `one_tmul_injective`, verbatim — that statement
mentions no base field at all, and is duplicated here only because its home
module is downstream).

The witness is `TensorProduct.piScalarRightHom`, which carries `1 ⊗ₜ x` to
the entrywise image `fun j => algebraMap A B (x j)`; injectivity of the
structure map then recovers `x`. -/
lemma one_tmul_injective_hilbert {A : Type*} [CommRing A] {B : Type*}
    [CommRing B] [Algebra A B] (hinj : Function.Injective (algebraMap A B))
    (ι : Type*) : Function.Injective (fun x : ι → A => (1 : B) ⊗ₜ[A] x) := by
  intro x y hxy
  have h2 := congrArg (TensorProduct.piScalarRightHom A B B ι) hxy
  rw [TensorProduct.piScalarRightHom_tmul,
    TensorProduct.piScalarRightHom_tmul] at h2
  funext i
  have h3 := congrFun h2 i
  simp only [Algebra.smul_def, mul_one] at h3
  exact hinj h3

/-- **Raynaud closure for flat prolongations over a VARIABLE number field,
in plain SUBOBJECT form** (PROVEN 2026-07-26; the sub-object sibling of
`hasFlatProlongationAt_of_pi_surjection_of_numberField` above, and the
`K`-variable form of `Deformation.lean`'s PROVEN
`hasFlatProlongationAt_of_injection`): if the local space of `ρ₂` at a
place `w` of `K` is the geometric-point group of a finite flat group scheme
over `𝒪_w`, then so is every `Γ K_w`-equivariant additive SUBGROUP of it.

Mathematically this is closure of the essential image of the generic-fibre
functor (finite flat group schemes over the DVR `𝒪_w`) ⟶ (finite
`Γ K_w`-modules) under `Γ`-stable subgroups, by SCHEMATIC CLOSURE: the
closure of a closed subgroup scheme of the generic fibre inside the finite
flat model is again finite flat over the DVR. The EXISTENCE direction needs
no `e < ℓ − 1` bound; Raynaud's bound enters only for UNIQUENESS of the
prolongation, which is not asserted.

**HOW IT WAS CLOSED, AND WHY IT WAS OPEN FOR A DAY.** Word for word the
situation of the surjection sibling above, whose docstring carries the full
analysis. The fix prescribed there — hoist
`Deformations/RepresentationTheory/FlatPointsGroup.lean`'s
`variable (v : HeightOneSpectrum (𝓞 ℚ))` to a general number field — HAS
LANDED, and that file is now sorry-free at a variable `K`. So this is the
same three-line assembly as its sibling, over the same three PROVEN
ingredients: `hasFlatProlongationAt_iff_isFlatPointsGroupAt` to pass to the
representation-free carrier, `IsFlatPointsGroupAt.of_injective` for the
schematic closure of a `Γ K_w`-stable subgroup, and the `iff` again to come
back. Note it does NOT route through `Deformation.lean`'s `ℚ`-level
`hasFlatProlongationAt_of_prod_injection` corollary (which takes the same
object twice and kills the second coordinate, `x ↦ (j x, 0)`); that module
is DOWNSTREAM and unusable from here, and the direct subobject closure is
shorter anyway.

This leaf survived the hoist that was supposed to close it purely for a
bookkeeping reason worth recording: the hoist task was pointed at
`hasFlatProlongationAt_of_prod_injection_over_numberField`, **a name that
exists nowhere in this file**, so its sibling closed and this one did not.
A task aimed at a name that does not exist fails silently — it looks like a
completed task, not a missed one.

The import cost is nil: `FlatPointsGroup.lean` is already imported by this
module for the surjection sibling, and its Gelfand-duality closure was
audited there (38 `Fermat`-side modules, nothing from `HardlyRamified/`,
`Family.lean`, `Lift.lean`, `Deformation.lean` or `Modularity/*`), so the
circularity guard is intact.

No finiteness hypothesis on `M₁` is needed: it is forced, `M₁` injecting
into the finite `M₂`.

FAITHFULNESS: the hypotheses are exactly those of the `ℚ`-level theorem
with `ℚ` replaced by `K`, and the conclusion asks only for EXISTENCE of a
prolongation produced by a closure construction inside a model that already
exists — not for a descent of existence from `𝒪^nr`, so the `𝒪ᵥ`
discriminating rule does not bite.

References: Raynaud, *Schémas en groupes de type `(p,…,p)`*, Bull. SMF 102
(1974), §2–3; Tate, *Finite flat group schemes*, in
Cornell–Silverman–Stevens, §4. -/
theorem hasFlatProlongationAt_of_injection_of_numberField
    {K : Type u} [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K))
    {A₁ : Type*} [CommRing A₁] [TopologicalSpace A₁]
    {M₁ : Type*} [AddCommGroup M₁] [Module A₁ M₁]
    {A₂ : Type*} [CommRing A₂] [TopologicalSpace A₂]
    {M₂ : Type*} [AddCommGroup M₂] [Module A₂ M₂]
    {ρ₁ : GaloisRep K A₁ M₁} {ρ₂ : GaloisRep K A₂ M₂}
    (h : ρ₂.HasFlatProlongationAt w)
    (j : (ρ₁.toLocal w).Space →+ (ρ₂.toLocal w).Space)
    (hinj : Function.Injective j)
    (hequiv : ∀ (g : Γ (w.adicCompletion K))
        (x : (ρ₁.toLocal w).Space), j (g • x) = g • j x) :
    ρ₁.HasFlatProlongationAt w := by
  -- pass to the representation-free point-group carrier
  have h₂ : Modularity.IsFlatPointsGroupAt w (ρ₂.toLocal w).Space :=
    (Modularity.GaloisRep.hasFlatProlongationAt_iff_isFlatPointsGroupAt ρ₂).mp h
  -- subobjects: schematic closure over the DVR along the equivariant injection
  exact (Modularity.GaloisRep.hasFlatProlongationAt_iff_isFlatPointsGroupAt ρ₁).mpr
    (h₂.of_injective j hinj hequiv)

set_option backward.isDefEq.respectTransparency false in
open scoped TensorProduct in
/-- **Flatness at a place pulls back along a conjugation identity, over a
VARIABLE number field** (PROVEN 2026-07-26; the `K`-variable form of
`Deformation.lean`'s `isFlatAt_of_conj_eq`, whose proof this is verbatim):
if `ρ.conj e = τ` and `τ` is flat at `w`, then so is `ρ`.

This is the direction opposite to the flatness clause of
`isHilbertHardlyRamified_conj` above, and is what a *descent* hypothesis of
the shape `(ρ' ⊗ R)ᵉ = ρ` gives: the base-changed inverse framing
`(R ⧸ I) ⊗ e⁻¹` is an equivariant additive isomorphism of the two local
spaces, so `HasFlatProlongationAt.of_equiv` transports the Hopf-algebra
witness at every open ideal `I`. -/
theorem isFlatAt_of_conj_eq_of_numberField {K : Type u} [Field K]
    [NumberField K] (w : HeightOneSpectrum (𝓞 K))
    {R : Type*} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    [IsLocalRing R]
    {M : Type*} [AddCommGroup M] [Module R M] [Module.Finite R M]
    [Module.Free R M]
    {N : Type*} [AddCommGroup N] [Module R N] [Module.Finite R N]
    [Module.Free R N]
    {ρ : GaloisRep K R M} {τ : GaloisRep K R N} (e : M ≃ₗ[R] N)
    (he : ρ.conj e = τ) (h : τ.IsFlatAt w) : ρ.IsFlatAt w := by
  constructor
  intro I hI
  refine (h.cond I hI).of_equiv _
    (LinearEquiv.baseChange R (R ⧸ I) N M e.symm).toAddEquiv ?_
  intro g x
  show (LinearEquiv.baseChange R (R ⧸ I) N M e.symm)
      (((τ.baseChange (R ⧸ I)).toLocal w g) x) =
    ((ρ.baseChange (R ⧸ I)).toLocal w g)
      ((LinearEquiv.baseChange R (R ⧸ I) N M e.symm) x)
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => simp only [map_add, ha, hb]
  | tmul c m =>
    simp only [GaloisRep.toLocal_apply, GaloisRep.baseChange_tmul,
      LinearEquiv.baseChange_tmul]
    congr 1
    conv_lhs => rw [← he]
    rw [GaloisRep.conj_apply, LinearEquiv.conj_apply_apply,
      LinearEquiv.symm_apply_apply]

set_option backward.isDefEq.respectTransparency false in
open scoped TensorProduct in
/-- **Flatness at a place descends from a complete local ring to a subring
carrying the subspace topology, over a VARIABLE number field** (PROVEN
2026-07-26 over the two Raynaud closure leaves
`hasFlatProlongationAt_of_injection_of_numberField` and
`hasFlatProlongationAt_of_pi_surjection_of_numberField`; the `K`-variable
form of `Deformation.lean`'s `isFlatAt_of_subring_baseChange`, whose proof
this is verbatim): if `C` is a subring of an `𝔪`-adic local ring `A` and
the base change `τ ⊗ A` of a framed representation over `C` is flat at `w`,
then `τ` itself is flat at `w`.

NOTHING about `C` is used except that its topology is the subspace topology
(which is how `Subring` carries a topology) and that `A` is `𝔪`-adic. In
particular the Carayol arithmetic of the sibling leaf
`exists_isLocalRing_hilbertTraceSubring` is NOT consumed: flatness never
asks for the `𝔪'`-adic filtration of `C`, only for cofinality of *some*
family of open ideals, and the contracted ideals `𝔪ⁿ ∩ C` are cofinal in
the open ideals of `C` by the definition of the subspace topology alone.

ROUTE, in three steps, given an open ideal `I` of `C`.

1. *Cofinality.* `I` is a neighbourhood of `0` for the subspace topology,
   so `I ⊇ t ∩ C` for a neighbourhood `t` of `0` in `A`, and `isAdic_iff`
   gives `n` with `𝔪ⁿ ⊆ t`. Put `J := 𝔪ⁿ` and `J' := J ∩ C ≤ I`.
2. *Subobject.* `C ⧸ J' → A ⧸ J` is INJECTIVE — that is exactly
   `J' = J ∩ C` — and `N` is free, hence flat, over `C`, so
   `(C ⧸ J') ⊗_C N → (A ⧸ J) ⊗_C N` is injective. Composing with the
   inverse of `TensorProduct.AlgebraTensorModule.cancelBaseChange`, this
   is a `Γ K_w`-equivariant injection into a space with a finite flat
   prolongation, and the sub-object closure prolongs it.
3. *Quotient.* `J' ≤ I`, so `τ ⊗ C/I` is an equivariant QUOTIENT of
   `τ ⊗ C/J'`; the surjection closure at `n = 1` finishes.

Both closure steps are genuinely needed and neither subsumes the other:
`J'` is in general strictly smaller than `I`, so the subobject step alone
lands at the wrong level, and `C ⧸ I` need not embed in any `A ⧸ J`. -/
theorem isFlatAt_of_subring_baseChange_of_numberField {K : Type u} [Field K]
    [NumberField K] (w : HeightOneSpectrum (𝓞 K))
    {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [IsLocalRing A] (hadic : IsAdic (IsLocalRing.maximalIdeal A))
    {C : Subring A} [IsLocalRing C] [ContinuousSMul C A]
    {N : Type*} [AddCommGroup N] [Module C N] [Module.Finite C N]
    [Module.Free C N]
    {τ : GaloisRep K C N}
    (hflat : (τ.baseChange A).IsFlatAt w) :
    τ.IsFlatAt w := by
  classical
  constructor
  intro I hI
  -- STEP 1: an `𝔪`-adic open ideal of `A` contracting into `I`
  obtain ⟨n, hn⟩ : ∃ n : ℕ,
      Ideal.comap (algebraMap C A) ((IsLocalRing.maximalIdeal A) ^ n) ≤ I := by
    have hs : (I : Set C) ∈ nhds (0 : C) := hI.mem_nhds I.zero_mem
    rw [nhds_induced, Filter.mem_comap] at hs
    obtain ⟨t, ht, hts⟩ := hs
    obtain ⟨m, hm⟩ := (isAdic_iff.mp hadic).2 t (by simpa using ht)
    exact ⟨m, fun z hz => hts (hm hz)⟩
  set J : Ideal A := (IsLocalRing.maximalIdeal A) ^ n
  have hJopen : IsOpen (J : Set A) := (isAdic_iff.mp hadic).1 n
  set J' : Ideal C := Ideal.comap (algebraMap C A) J
  -- STEP 2: the `Γ`-stable subobject `C ⧸ J' ↪ A ⧸ J`
  let cmap : (C ⧸ J') →ₗ[C] (A ⧸ J) :=
    Submodule.liftQ J' (Algebra.linearMap C (A ⧸ J)) (by
      intro r hr
      show algebraMap C (A ⧸ J) r = 0
      rw [IsScalarTower.algebraMap_apply C A (A ⧸ J)]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr hr)
  have hcmap : ∀ r : C, cmap (Ideal.Quotient.mk J' r) = algebraMap C (A ⧸ J) r :=
    fun _ => rfl
  have hcmapinj : Function.Injective cmap := by
    refine (injective_iff_map_eq_zero cmap).mpr ?_
    intro x hx
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [hcmap r, IsScalarTower.algebraMap_apply C A (A ⧸ J),
      Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem] at hx
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hx
  let ι : ((C ⧸ J') ⊗[C] N) →ₗ[C] ((A ⧸ J) ⊗[C] N) := LinearMap.rTensor N cmap
  let can := TensorProduct.AlgebraTensorModule.cancelBaseChange C A (A ⧸ J) (A ⧸ J) N
  let jmap : ((τ.baseChange (C ⧸ J')).toLocal w).Space →+
      (((τ.baseChange A).baseChange (A ⧸ J)).toLocal w).Space :=
    (can.symm.toAddEquiv.toAddMonoidHom).comp (ι.toAddMonoidHom)
  have hsmall : (τ.baseChange (C ⧸ J')).HasFlatProlongationAt w := by
    refine hasFlatProlongationAt_of_injection_of_numberField w
      (hflat.cond J hJopen) jmap ?_ ?_
    · exact can.symm.injective.comp
        (Module.Flat.rTensor_preserves_injective_linearMap cmap hcmapinj)
    · intro g x
      show can.symm (ι (((τ.baseChange (C ⧸ J')).toLocal w) g x))
        = (((τ.baseChange A).baseChange (A ⧸ J)).toLocal w) g (can.symm (ι x))
      induction x using TensorProduct.induction_on with
      | zero => simp
      | add a b ha hb => simp only [map_add, ha, hb]
      | tmul c m => rfl
  -- STEP 3: the equivariant quotient `C ⧸ J' ↠ C ⧸ I`
  let qmap : (C ⧸ J') →ₗ[C] (C ⧸ I) :=
    Submodule.liftQ J' (Submodule.mkQ (I : Submodule C C))
      (by rw [Submodule.ker_mkQ]; exact hn)
  have hqsurj : Function.Surjective qmap := by
    intro z
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective z
    exact ⟨Ideal.Quotient.mk J' r, rfl⟩
  have hqkey : ∀ (g : Γ (w.adicCompletion K))
      (y : ((τ.baseChange (C ⧸ J')).toLocal w).Space),
      LinearMap.rTensor N qmap (((τ.baseChange (C ⧸ J')).toLocal w) g y)
        = ((τ.baseChange (C ⧸ I)).toLocal w) g (LinearMap.rTensor N qmap y) := by
    intro g y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | add a b ha hb => simp only [map_add, ha, hb]
    | tmul c m => rfl
  let pmap : (Fin 1 → ((τ.baseChange (C ⧸ J')).toLocal w).Space) →+
      ((τ.baseChange (C ⧸ I)).toLocal w).Space :=
    { toFun := fun x => LinearMap.rTensor N qmap (x 0)
      map_zero' := by simp
      map_add' := fun x y => by simp }
  refine hasFlatProlongationAt_of_pi_surjection_of_numberField w 1 hsmall
    pmap ?_ ?_
  · intro z
    obtain ⟨y, hy⟩ := LinearMap.rTensor_surjective N hqsurj z
    exact ⟨fun _ => y, hy⟩
  · intro g x
    exact hqkey g (x 0)

open scoped TensorProduct in
/-- **Rouquier–Nyssen at the `F` level: the descended representation
exists** (LEAF — new 2026-07-26; the `F`-level twin of `Deformation.lean`'s
`exists_framedGaloisRep_baseChange_traceSubring`, which is PROVEN there):
the deformation `𝒟.ρ` is, after a change of framing, the base change to
`𝒟.R` of a framed representation with coefficients in the closed trace
subring `R' = hilbertTraceSubring ℓ 𝒟.ρ`.

This is the representation-theoretic core of Carayol's Théorème 1 and the
only place where irreducibility of `ρbar|_{G_F}` is used. Mathematically:
`ρbar|_{G_F}` is absolutely irreducible (it is irreducible over the finite
field `k` and its determinant is the mod-`ℓ` cyclotomic character, so it is
odd, and an odd irreducible two-dimensional representation over a finite
field of odd characteristic is absolutely irreducible); by Nakayama the
`𝒟.R`-algebra generated by `𝒟.ρ(G_F)` is therefore all of `M₂(𝒟.R)`, so one
may choose `x, y ∈ G_F` with `{1, ρ(x), ρ(y), ρ(x)ρ(y)}` a `𝒟.R`-basis. In
the dual basis of the trace form every matrix entry of every `ρ(g)` is a
`ℤ`-linear combination of the traces `tr(ρ(g)·b)` with `b` a product of
`ρ(x)`'s and `ρ(y)`'s — and every such trace is a charpoly coefficient,
hence lies in `R'` BY CONSTRUCTION, since `hilbertTraceSubring` is
generated by the charpoly coefficients at EVERY `g : Γ F`. Equivalently:
Rouquier–Nyssen's theorem that a two-dimensional pseudo-character over a
local ring with absolutely irreducible residual representation is the
character of a true representation into `GL₂` of that ring. Conjugating by
the base-change matrix is the required change of framing.

WHY NO TRACE HYPOTHESIS IS NEEDED HERE, unlike at the `ℚ` level. The
`ℚ`-level statement carries a hypothesis `htr` saying that all traces lie
in `traceSubring ℓ D.ρ`, because THAT ring is generated by the Frobenius
charpolys at the GOOD primes only, so "trace at every `g`" is a genuine
extra input (supplied there by Chebotarev density plus Brauer–Nesbitt).
`hilbertTraceSubring` is generated at every `g : Γ F`, so the hypothesis is
`charpoly_coeff_mem_hilbertTraceSubring`, already proven above, and the
`ℚ`-level three-leaf cut becomes a two-leaf cut at this level.

Irreducibility is load-bearing and the statement is FALSE without it: a
reducible `ρ` whose extension class is not defined over `R'` cannot be
conjugated into `GL₂(R')`.

References: Carayol, *Formes modulaires et représentations galoisiennes à
valeurs dans un anneau local complet* (Contemp. Math. 165), Théorème 1;
Nyssen, *Pseudo-représentations* (Math. Ann. 306); Rouquier,
*Caractérisation des caractères et pseudo-caractères* (J. Algebra 180). -/
theorem exists_framedGaloisRep_baseChange_hilbertTraceSubring
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ5 : 5 ≤ ℓ) (F : Type u) [Field F] [NumberField F]
    {k : Type u} [Field k] [Finite k] [TopologicalSpace k]
    {V : Type v} [AddCommGroup V] [Module k V] [Module.Finite k V]
    [Module.Free k V]
    {ρbar : GaloisRep ℚ k V}
    (hirrF : (ρbar.map (algebraMap ℚ F)).IsIrreducible)
    (𝒟 : HilbertDeformationDatum ℓ F ρbar)
    (hloc : IsLocalRing (hilbertTraceSubring ℓ 𝒟.ρ)) :
    ∃ (ρ' : FramedGaloisRep F (hilbertTraceSubring ℓ 𝒟.ρ) (Fin 2))
      (e : (𝒟.R ⊗[hilbertTraceSubring ℓ 𝒟.ρ]
          (Fin 2 → hilbertTraceSubring ℓ 𝒟.ρ)) ≃ₗ[𝒟.R] (Fin 2 → 𝒟.R)),
      (ρ'.baseChange 𝒟.R).conj e = 𝒟.ρ :=
  sorry

open scoped TensorProduct in
/-- **Frame coordinates of a base-changed framed representation** (PROVEN;
the local copy, over a VARIABLE base number field and at a place `w`, of
`Deformation.lean`'s `exists_frameCoords_of_baseChange_conj`, which is
hard-coded to `ℚ` and to the single place `ℚ_2`): if a surjective
`S`-functional `πR` transforms by a scalar `ε` under the local action of
`ρS = (ρ' ⊗ S)ᵉ`, then reading it through the standard frame
`x ↦ πR (e (1 ⊗ x))` presents it as a ROW `(a, b) ∈ S²` which is
unimodular and satisfies the same scalar transformation law on `C²`.

Unimodularity is the only non-formal step: were both `a` and `b` in `𝔪_S`,
then `πR ∘ e` would land in `𝔪_S` on every pure tensor, hence everywhere by
`TensorProduct.induction_on`, contradicting surjectivity of `πR`.

Stated with `ε` valued in the AMBIENT `S`, not in the subring `C`: the
`ℚ`-level original takes `ε : Γ ℚ_2 → C`, which forces its caller to prove
first that the tame character is already defined over `C` (the sign lemma
`exists_tameSign_of_deformation` there). The consumer below does not need
that, because it pushes the character into `C` along the retraction
instead, so the weaker binder is the useful one here. -/
theorem exists_frameCoords_of_baseChange_conj_hilbert
    {F : Type u} [Field F] [NumberField F] (w : HeightOneSpectrum (𝓞 F))
    {S : Type*} [CommRing S] [TopologicalSpace S] [IsTopologicalRing S]
    [IsLocalRing S] {C : Subring S}
    {ρS : GaloisRep F S (Fin 2 → S)} {ρ' : FramedGaloisRep F C (Fin 2)}
    (e : (S ⊗[C] (Fin 2 → C)) ≃ₗ[S] (Fin 2 → S))
    (he : (ρ'.baseChange S).conj e = ρS)
    {πR : (Fin 2 → S) →ₗ[S] S} (hπRsurj : Function.Surjective πR)
    {ε : Γ (w.adicCompletion F) → S}
    (hπRequi : ∀ (g : Γ (w.adicCompletion F)) (x : Fin 2 → S),
      πR (ρS.toLocal w g x) = ε g * πR x) :
    ∃ a b : S, (IsUnit a ∨ IsUnit b) ∧
      ∀ (g : Γ (w.adicCompletion F)) (x : Fin 2 → C),
        (((ρ'.toLocal w g x) 0 : C) : S) * a +
          (((ρ'.toLocal w g x) 1 : C) : S) * b =
          ε g * (((x 0 : C) : S) * a + ((x 1 : C) : S) * b) := by
  classical
  have hcast : ∀ c : C, (c : S) = algebraMap C S c := fun _ => rfl
  set φ : (Fin 2 → C) → S := fun x => πR (e ((1 : S) ⊗ₜ[C] x)) with hφdef
  have hφadd : ∀ x y, φ (x + y) = φ x + φ y := by
    intro x y
    show πR (e ((1 : S) ⊗ₜ[C] (x + y))) = _
    rw [TensorProduct.tmul_add, map_add, map_add]
  have hφsmul : ∀ (c : C) (x : Fin 2 → C), φ (c • x) = (c : S) * φ x := by
    intro c x
    have h1 : (1 : S) ⊗ₜ[C] (c • x) = (c : S) • ((1 : S) ⊗ₜ[C] x) := by
      rw [TensorProduct.tmul_smul, hcast, algebraMap_smul]
    show πR (e ((1 : S) ⊗ₜ[C] (c • x))) = _
    rw [h1, map_smul, map_smul, smul_eq_mul]
  have hdecomp : ∀ x : Fin 2 → C,
      x = x 0 • Pi.single (0 : Fin 2) (1 : C) + x 1 • Pi.single 1 1 := by
    intro x
    funext i
    fin_cases i <;> simp
  have hφw : ∀ x : Fin 2 → C,
      φ x = (x 0 : S) * φ (Pi.single 0 1) + (x 1 : S) * φ (Pi.single 1 1) := by
    intro x
    conv_lhs => rw [hdecomp x]
    rw [hφadd, hφsmul, hφsmul]
  have hhe : ∀ (G : Γ F) (y : S ⊗[C] (Fin 2 → C)),
      e ((ρ'.baseChange S) G y) = ρS G (e y) := by
    intro G y
    have h1 : ((ρ'.baseChange S).conj e) G = ρS G := by rw [he]
    rw [GaloisRep.conj_apply] at h1
    have h2 := congrArg (fun f : Module.End S (Fin 2 → S) => f (e y)) h1
    simpa [LinearEquiv.conj_apply] using h2
  have hφequi : ∀ (g : Γ (w.adicCompletion F)) (x : Fin 2 → C),
      φ (ρ'.toLocal w g x) = ε g * φ x := by
    intro g x
    have h1 : (1 : S) ⊗ₜ[C] (ρ'.toLocal w g x) =
        (ρ'.baseChange S)
          (Field.absoluteGaloisGroup.map (algebraMap F (w.adicCompletion F)) g)
          ((1 : S) ⊗ₜ[C] x) := by
      rw [GaloisRep.baseChange_tmul, GaloisRep.toLocal_apply]
    show πR (e ((1 : S) ⊗ₜ[C] (ρ'.toLocal w g x))) = _
    rw [h1, hhe]
    have h2 := hπRequi g (e ((1 : S) ⊗ₜ[C] x))
    rw [GaloisRep.toLocal_apply] at h2
    rw [h2]
  have hab : IsUnit (φ (Pi.single 0 1)) ∨ IsUnit (φ (Pi.single 1 1)) := by
    by_contra hc
    rw [not_or] at hc
    have hA : φ (Pi.single 0 1) ∈ IsLocalRing.maximalIdeal S :=
      (IsLocalRing.mem_maximalIdeal _).mpr hc.1
    have hB : φ (Pi.single 1 1) ∈ IsLocalRing.maximalIdeal S :=
      (IsLocalRing.mem_maximalIdeal _).mpr hc.2
    have hmem : ∀ y : S ⊗[C] (Fin 2 → C),
        πR (e y) ∈ IsLocalRing.maximalIdeal S := by
      intro y
      induction y using TensorProduct.induction_on with
      | zero => rw [map_zero, map_zero]; exact Ideal.zero_mem _
      | add x y hx hy => rw [map_add, map_add]; exact Ideal.add_mem _ hx hy
      | tmul c x =>
        have h1 : (c ⊗ₜ[C] x) = c • ((1 : S) ⊗ₜ[C] x) := by
          rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
        rw [h1, map_smul, map_smul, smul_eq_mul]
        refine Ideal.mul_mem_left _ _ ?_
        show φ x ∈ _
        rw [hφw]
        exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hA)
          (Ideal.mul_mem_left _ _ hB)
    obtain ⟨z, hz⟩ := hπRsurj 1
    have h1 : (1 : S) ∈ IsLocalRing.maximalIdeal S := by
      rw [← hz, ← e.apply_symm_apply z]
      exact hmem _
    exact (IsLocalRing.mem_maximalIdeal _).mp h1 isUnit_one
  refine ⟨φ (Pi.single 0 1), φ (Pi.single 1 1), hab, ?_⟩
  intro g x
  have h1 := hφequi g x
  rw [hφw (ρ'.toLocal w g x), hφw x] at h1
  exact h1

open scoped TensorProduct in
/-- **The tame quadratic quotient at a place over `2` descends to the trace
subring** (LEAF — new 2026-07-26; the `F`-level twin of
`Deformation.lean`'s PROVEN `isTameAtTwo_of_baseChange_traceSubring`): if
the framed representation `ρ'` over `R' = hilbertTraceSubring ℓ 𝒟.ρ`
base-changes, up to framing, to `𝒟.ρ`, then `ρ'` carries the tame-at-`2`
datum of `IsHilbertHardlyRamified` at every place `w ∣ 2` — a surjective
`R'`-linear functional whose quotient character is unramified with trivial
square.

WHAT IS FORMAL AND WHAT IS NOT. The CHARACTER descends for free: `δ` takes
values in `𝒟.R` with `δ(g)² = 1`, and in a local ring in which `2` is
invertible — `𝒟.R` has residue characteristic `ℓ ≥ 5`, odd — the only
square roots of `1` are `±1`, since `(δ(g) − 1)(δ(g) + 1) = 0` and at most
one factor lies in the maximal ideal. So `δ(g) ∈ {±1} ⊆ R'` and the
character is already defined over `R'`, unramified and quadratic there.

The content is the `Γ F_w`-stable LINE `ker p ⊆ 𝒟.R²`: its intersection
with the frame `e(1 ⊗ R'²)` must be a rank-one direct summand. That is a
statement about the `R'`-LATTICE, not a formal consequence of the
base-change identity, and a general subring descent of it would be FALSE:
for `R' = ℤ_ℓ[[Y², Y³]]` inside `ℤ_ℓ[[Y]]` the matrices
`[[1, −Y³], [0, 1 + Y²]]` and `[[1, −Y⁴], [0, 1 + Y³]]` have entries in
`R'`, generate `R'` by their traces, and their common eigenrow `(1, Y)`
meets `R'²` only inside `𝔪'R'²`.

THE `ℚ`-LEVEL ROUTE, which is the one to port, and where the arithmetic
enters. Pick `g₀ ∈ Γ F_w` with `χ_ℓ(g₀) ≢ 1 (mod ℓ)` — over `ℚ_2` this is
`Deformation.lean`'s `exists_cyclotomicCharacter_padicTwo_sub_one_isUnit`,
concretely a Frobenius, where `χ_ℓ = 2` and `1 − 2 = −1` is a unit.
Cayley–Hamilton against the unimodular eigenrow then forces
`det ρ'(g₀) = δ(g₀)·tr ρ'(g₀) − 1`, so the two eigenvalues of `ρ'(g₀)` are
`δ(g₀)` and `κ(g₀)` with
`(δ(g₀) − κ(g₀))·δ(g₀) = 1 − det ρ'(g₀) = 1 − χ_ℓ(g₀)`, a UNIT. The
eigen-projector `ρ'(g₀) − κ(g₀)` is then defined over `R'` with unit trace,
so one of its two rows is unimodular over the local ring `R'`, and each of
its rows is proportional to the frame row by one of the two
eigen-equations — which transfers the equivariance for ALL of `Γ F_w`, not
just for `g₀`. In the counterexample above the two characters coincide,
which is exactly what `χ_ℓ(g₀) ≠ 1` excludes.

**THE ARITHMETIC INPUT DOES *NOT* TRANSPORT VERBATIM** (flagged 2026-07-26
at the cut, by the author of the consumer). The step "pick `g₀` with
`χ_ℓ(g₀) ≢ 1`" is available over `ℚ_2` and is **NOT** available over an
arbitrary `F_w ∣ 2`. `χ_ℓ mod ℓ` is trivial on `Γ F_w` exactly when
`μ_ℓ ⊆ F_w`, and `ℚ_2(μ_ℓ)` is the UNRAMIFIED extension of `ℚ_2` of degree
`ord_ℓ(2)`, which is finite — so any `F` whose completion at `w` contains
it kills the argument. Nothing in `HilbertDeformationDatum` excludes such an
`F`: the totally real field here is whatever potential modularity produced.

**FALSITY AUDIT — THE HYPOTHESIS-FREE STATEMENT IS FALSE, AND THIS IS WHY
THE RETRACTION `f` IS NOW A HYPOTHESIS** (2026-07-26; the leaf as originally
cut carried no `f`, and in that form it is refuted by the witness below).

A *concrete* `(F, ℓ, w)` realising the obstruction exists: take `ℓ = 7` and
`F = ℚ(ζ₇)⁺`, the real cyclotomic cubic field. `2` has order `3` in
`(ℤ/7)ˣ`, so `2` is INERT in `F` with residue degree `3`, and the unique
`w ∣ 2` has `F_w = ℚ_2(μ_7)`, the unramified cubic extension. `F` is
totally real and `ℓ = 7 ≥ 5`, so every side condition of this module holds,
and `χ_7(Γ F_w) = 1 + 7ℤ_7` — every `g` has `χ_ℓ(g) ≡ 1 (mod ℓ)`, so NO
`g₀` separates the two residual eigenvalues.

Against that arithmetic backdrop the LATTICE descent genuinely fails. Put
`R = ℤ_7[[Y]]` and let `R' = ℤ_7[[Z]] ↪ R` by `Z ↦ 7Y` (injective, local,
closed). For `c ∈ 1 + 7ℤ_7` set

    M_c = [[1, ((1 − c)/7)·Z], [0, c]] ∈ GL₂(R'),

which is a genuine homomorphism `1 + 7ℤ_7 → GL₂(R')`, since
`u(c') + u(c)c' = u(cc')` for `u(c) = (1 − c)/7`. Take
`ρ'|_{Γ F_w} : g ↦ M_{χ_7(g)}`; it is continuous, UNRAMIFIED (it factors
through `χ_7`, which is unramified at `w ∣ 2` because `ℓ ≠ 2`), and has
`det = χ_7`, exactly as `IsHilbertHardlyRamified.det` demands. Its traces
are `1 + c ∈ ℤ_7`, so nothing here obstructs `R'` being the trace subring.

* Over `R` the tame datum EXISTS: the row `(1, Y)` satisfies
  `(1, Y)·M_c = (1, Y)`, it is unimodular (`1` is a unit), and its character
  is `δ = 1` — unramified with `δ² = 1`. So `𝒟` is a legitimate datum.
* Over `R'` it does NOT. The `δ = 1` eigenrows in `R'²` are
  `{(x, Yx) : x, Yx ∈ R'} = 7·R'·(1, Y) = R'·(7, Z)`, and BOTH entries of
  `(7, Z)` lie in `𝔪' = (7, Z)`: no unimodular eigenrow exists. The only
  other eigenrow is `(0, 1)`, with character `χ_7`, and `χ_7² ≠ 1` — so it
  is barred by the `δ² = 1` clause. Hence there is no admissible `p`.

The counterexample dies exactly when `f` is present: a ring retraction
`f : R ↠ R'` of the inclusion would give `7·f(Y) = Z`, and `Z ∉ 7·ℤ_7[[Z]]`.
So the retraction hypothesis is not a convenience — it is *precisely* the
missing content, and with it the proof below is three steps and needs no
arithmetic at `w` at all (in particular it is insensitive to whether
`μ_ℓ ⊆ F_w`, which is what makes it a correct `F`-level statement rather
than a transplanted `ℚ`-level one).

WHY THE RETRACTION IS AVAILABLE UPSTREAM, and why it is a well-posed leaf
rather than a smuggled hypothesis: see
`exists_ringHom_retraction_hilbertTraceSubring` below, which supplies it
from `𝒟.IsWeaklyUniversal`. Briefly — a weakly universal `𝒟` and the
genuinely universal trace-generated datum `𝒟ᵘⁿⁱᵛ` map to each other, the
round trip `Rᵘⁿⁱᵛ → 𝒟.R → Rᵘⁿⁱᵛ` fixes every charpoly coefficient and hence
is the identity on the trace-generated `Rᵘⁿⁱᵛ` (Mazur §1.8), so `𝒟.R`
retracts onto the image of `Rᵘⁿⁱᵛ`, which is `R'`.

WHAT THIS COSTS THE CUT. Only `exists_framedGaloisRep_hilbertTraceSubring`
and `exists_hilbertTraceDescent` change, by carrying `f` as a parameter;
`exists_isWeaklyUniversal_isTraceGenerated_hilbertDeformationDatum`
discharges it from the `IsWeaklyUniversal` hypothesis it already has, so
NOTHING outside this section sees the repair.

FAITHFULNESS: the conclusion quantifies over `localInertiaGroup w` and MUST
NOT be widened to `Γ F` or even to `Γ F_w` — the quotient character is
unramified, i.e. trivial on inertia, but emphatically NOT trivial on
Frobenius. Widening the inertia quantifier is the single commonest way a
leaf in this development has been made false.

WELL-POSEDNESS — why quantifying over the output of the Rouquier–Nyssen
leaf is harmless. The tame clause is invariant under an `R'`-change of
frame (if `p` witnesses it for `Fρ'F⁻¹` with `F ∈ GL₂(R')` then `p ∘ F`
witnesses it for `ρ'`), and any two descents are `R'`-conjugate by Nyssen's
uniqueness, their framings differing by an element of the centraliser of
`𝒟.ρ(G_F)`, which is `𝒟.R^×` by Schur plus absolute irreducibility. So the
leaf holds for every output of the Rouquier–Nyssen leaf or for none: a
prover may fix whichever descent is convenient, and a prover who finds it
FALSE has found Carayol's descent incompatible with the tame filtration and
should REPORT that rather than weaken this statement. -/
theorem isHilbertTameAtTwo_of_baseChange_hilbertTraceSubring
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ5 : 5 ≤ ℓ) (F : Type u) [Field F] [NumberField F]
    {k : Type u} [Field k] [Finite k] [TopologicalSpace k]
    {V : Type v} [AddCommGroup V] [Module k V] [Module.Finite k V]
    [Module.Free k V]
    {ρbar : GaloisRep ℚ k V}
    (𝒟 : HilbertDeformationDatum ℓ F ρbar)
    (hloc : IsLocalRing (hilbertTraceSubring ℓ 𝒟.ρ))
    (f : 𝒟.R →+* hilbertTraceSubring ℓ 𝒟.ρ)
    (hf : ∀ x : hilbertTraceSubring ℓ 𝒟.ρ, f (x : 𝒟.R) = x)
    (ρ' : FramedGaloisRep F (hilbertTraceSubring ℓ 𝒟.ρ) (Fin 2))
    (e : (𝒟.R ⊗[hilbertTraceSubring ℓ 𝒟.ρ]
        (Fin 2 → hilbertTraceSubring ℓ 𝒟.ρ)) ≃ₗ[𝒟.R] (Fin 2 → 𝒟.R))
    (he : (ρ'.baseChange 𝒟.R).conj e = 𝒟.ρ)
    (w : HeightOneSpectrum (𝓞 F)) (hw : ((2 : ℕ) : 𝓞 F) ∈ w.asIdeal) :
    ∃ (p : (Fin 2 → hilbertTraceSubring ℓ 𝒟.ρ)
        →ₗ[hilbertTraceSubring ℓ 𝒟.ρ] (hilbertTraceSubring ℓ 𝒟.ρ))
      (_ : Function.Surjective p)
      (δ : GaloisRep (w.adicCompletion F) (hilbertTraceSubring ℓ 𝒟.ρ)
        (hilbertTraceSubring ℓ 𝒟.ρ)),
      (∀ g : Γ (w.adicCompletion F),
        ∀ x : Fin 2 → hilbertTraceSubring ℓ 𝒟.ρ,
        p (ρ'.toLocal w g x) = δ g (p x)) ∧
      localInertiaGroup w ≤ δ.ker ∧
      ∀ g : Γ (w.adicCompletion F), δ g * δ g = 1 := by
  classical
  letI := hloc
  -- the tame datum of `𝒟` itself, at the place `w`
  obtain ⟨pR, hpRsurj, δR, hRequi, hRinert, hRsq⟩ :=
    𝒟.isHilbertHardlyRamified.isTameAtTwo w hw
  -- `δR` is multiplication by the scalar `ε g`
  set ε : Γ (w.adicCompletion F) → 𝒟.R := fun g => δR g 1 with hεdef
  have hεapp : ∀ g : Γ (w.adicCompletion F), ε g = δR g 1 := fun _ => rfl
  have hδRapp : ∀ (g : Γ (w.adicCompletion F)) (y : 𝒟.R), δR g y = ε g * y := by
    intro g y
    calc δR g y = δR g (y • (1 : 𝒟.R)) := by rw [smul_eq_mul, mul_one]
      _ = y • δR g 1 := by rw [map_smul]
      _ = ε g * y := by rw [hεapp, smul_eq_mul]; exact mul_comm _ _
  have hεsq : ∀ g, ε g * ε g = 1 := by
    intro g
    have h := congrArg (fun t : Module.End 𝒟.R 𝒟.R => t (1 : 𝒟.R)) (hRsq g)
    simp only [Module.End.mul_apply, Module.End.one_apply] at h
    rwa [hδRapp, ← hεapp] at h
  have hεone : ε 1 = 1 := by
    rw [hεapp, show δR 1 = 1 from map_one δR]
    rfl
  have hεmul : ∀ g h', ε (g * h') = ε g * ε h' := by
    intro g h'
    rw [hεapp, hεapp, hεapp, show δR (g * h') = δR g * δR h' from map_mul δR g h',
      Module.End.mul_apply, hδRapp, ← hεapp]
  have hεinert : ∀ g ∈ localInertiaGroup w, ε g = 1 := by
    intro g hg
    rw [hεapp, show δR g = 1 from hRinert hg]
    rfl
  -- frame coordinates of the descent, over `𝒟.R`
  obtain ⟨a, b, hab, hcoord⟩ :=
    exists_frameCoords_of_baseChange_conj_hilbert (ρ' := ρ') w e he hpRsurj
      (ε := ε) (fun g x => by rw [hRequi g x, hδRapp])
  -- push the frame row into `R'` along the retraction
  set π : (Fin 2 → hilbertTraceSubring ℓ 𝒟.ρ)
      →ₗ[hilbertTraceSubring ℓ 𝒟.ρ] (hilbertTraceSubring ℓ 𝒟.ρ) :=
    (f a) • LinearMap.proj 0 + (f b) • LinearMap.proj 1 with hπdef
  have hπapp : ∀ x : Fin 2 → hilbertTraceSubring ℓ 𝒟.ρ,
      π x = f a * x 0 + f b * x 1 := by
    intro x; simp [hπdef]
  have hπsurj : Function.Surjective π := by
    have hab' : IsUnit (f a) ∨ IsUnit (f b) := by
      rcases hab with h | h
      · exact Or.inl (h.map f)
      · exact Or.inr (h.map f)
    rcases hab' with h | h
    · obtain ⟨u, hu⟩ := h.exists_right_inv
      intro c
      refine ⟨Pi.single 0 (u * c), ?_⟩
      rw [hπapp]
      have h0 : (Pi.single (0 : Fin 2) (u * c) :
        Fin 2 → hilbertTraceSubring ℓ 𝒟.ρ) 0 = u * c := by simp
      have h1 : (Pi.single (0 : Fin 2) (u * c) :
        Fin 2 → hilbertTraceSubring ℓ 𝒟.ρ) 1 = 0 := by simp
      rw [h0, h1, mul_zero, add_zero, ← mul_assoc, hu, one_mul]
    · obtain ⟨u, hu⟩ := h.exists_right_inv
      intro c
      refine ⟨Pi.single 1 (u * c), ?_⟩
      rw [hπapp]
      have h0 : (Pi.single (1 : Fin 2) (u * c) :
        Fin 2 → hilbertTraceSubring ℓ 𝒟.ρ) 0 = 0 := by simp
      have h1 : (Pi.single (1 : Fin 2) (u * c) :
        Fin 2 → hilbertTraceSubring ℓ 𝒟.ρ) 1 = u * c := by simp
      rw [h0, h1, mul_zero, zero_add, ← mul_assoc, hu, one_mul]
  -- the descended character: the retraction of the ambient one
  have hπequi : ∀ (g : Γ (w.adicCompletion F))
      (x : Fin 2 → hilbertTraceSubring ℓ 𝒟.ρ),
      π (ρ'.toLocal w g x) = f (ε g) * π x := by
    intro g x
    have h := congrArg f (hcoord g x)
    rw [map_add, map_mul, map_mul, hf, hf, map_mul, map_add, map_mul, map_mul,
      hf, hf] at h
    rw [hπapp, hπapp]
    calc f a * (ρ'.toLocal w g x) 0 + f b * (ρ'.toLocal w g x) 1
        = (ρ'.toLocal w g x) 0 * f a + (ρ'.toLocal w g x) 1 * f b := by
          rw [mul_comm (f a), mul_comm (f b)]
      _ = f (ε g) * (x 0 * f a + x 1 * f b) := h
      _ = f (ε g) * (f a * x 0 + f b * x 1) := by ring
  have hεCsq : ∀ g, f (ε g) * f (ε g) = 1 := by
    intro g; rw [← map_mul, hεsq, map_one]
  -- continuity of the descended character, read off `π` at a section point
  obtain ⟨x₀, hx₀⟩ := hπsurj 1
  letI := moduleTopology (hilbertTraceSubring ℓ 𝒟.ρ)
    (Module.End (hilbertTraceSubring ℓ 𝒟.ρ)
      (Fin 2 → hilbertTraceSubring ℓ 𝒟.ρ))
  letI := moduleTopology (hilbertTraceSubring ℓ 𝒟.ρ)
    (Module.End (hilbertTraceSubring ℓ 𝒟.ρ) (hilbertTraceSubring ℓ 𝒟.ρ))
  haveI : ContinuousAdd
      (Module.End (hilbertTraceSubring ℓ 𝒟.ρ) (hilbertTraceSubring ℓ 𝒟.ρ)) :=
    ModuleTopology.continuousAdd _ _
  haveI : ContinuousSMul (hilbertTraceSubring ℓ 𝒟.ρ)
      (Module.End (hilbertTraceSubring ℓ 𝒟.ρ) (hilbertTraceSubring ℓ 𝒟.ρ)) :=
    ModuleTopology.continuousSMul _ _
  have hεCcont : Continuous (fun g => f (ε g)) := by
    have h1 : (fun g => f (ε g)) = fun g =>
        (π ∘ₗ (LinearMap.applyₗ x₀ :
          Module.End (hilbertTraceSubring ℓ 𝒟.ρ)
              (Fin 2 → hilbertTraceSubring ℓ 𝒟.ρ)
            →ₗ[hilbertTraceSubring ℓ 𝒟.ρ]
              (Fin 2 → hilbertTraceSubring ℓ 𝒟.ρ)))
          ((ρ'.toLocal w) g) := by
      funext g
      have h2 := hπequi g x₀
      rw [hx₀, mul_one] at h2
      exact h2.symm
    rw [h1]
    exact (IsModuleTopology.continuous_of_linearMap _).comp
      (ρ'.toLocal w).continuous_toFun
  set δ : GaloisRep (w.adicCompletion F) (hilbertTraceSubring ℓ 𝒟.ρ)
      (hilbertTraceSubring ℓ 𝒟.ρ) :=
    { toFun := fun g => f (ε g) • (1 : Module.End (hilbertTraceSubring ℓ 𝒟.ρ)
        (hilbertTraceSubring ℓ 𝒟.ρ))
      map_one' := by rw [hεone, map_one, one_smul]
      map_mul' := fun g h' => by
        refine LinearMap.ext fun c => ?_
        simp only [hεmul, map_mul, LinearMap.smul_apply, Module.End.one_apply,
          Module.End.mul_apply, smul_eq_mul]
        ring
      continuous_toFun := hεCcont.smul continuous_const } with hδdef
  have hδapp : ∀ (g : Γ (w.adicCompletion F))
      (c : hilbertTraceSubring ℓ 𝒟.ρ), δ g c = f (ε g) * c := by
    intro g c
    show (f (ε g) • (1 : Module.End (hilbertTraceSubring ℓ 𝒟.ρ)
      (hilbertTraceSubring ℓ 𝒟.ρ))) c = f (ε g) * c
    rw [LinearMap.smul_apply, Module.End.one_apply, smul_eq_mul]
  refine ⟨π, hπsurj, δ, fun g x => ?_, fun σ hσ => ?_, fun g => ?_⟩
  · rw [hπequi, hδapp]
  · show f (ε σ) • (1 : Module.End (hilbertTraceSubring ℓ 𝒟.ρ)
      (hilbertTraceSubring ℓ 𝒟.ρ)) = 1
    rw [hεinert σ hσ, map_one, one_smul]
  · refine LinearMap.ext fun c => ?_
    show (δ g) ((δ g) c) = c
    rw [hδapp, hδapp, ← mul_assoc, hεCsq, one_mul]

set_option backward.isDefEq.respectTransparency false in
open scoped TensorProduct in
/-- **Carayol's Théorème 1 at the `F` level** (PROVEN 2026-07-26 as an
assembly over the three leaves just above — the Rouquier–Nyssen descent
`exists_framedGaloisRep_baseChange_hilbertTraceSubring`, the Raynaud
sub-object closure that
`isFlatAt_of_subring_baseChange_of_numberField` runs on, and the tame
descent `isHilbertTameAtTwo_of_baseChange_hilbertTraceSubring`; formerly a
single sorry leaf. The `F`-level twin of `Deformation.lean`'s
`exists_framedGaloisRep_traceSubring`, which is proven there over the
corresponding three-way cut): a framed deformation whose residual
representation is irreducible is CONJUGATE, inside `GL₂(𝒟.R)`, to one
taking values in `GL₂(R')` for the closed trace subring `R'`; and the
conjugated representation still satisfies the `F`-level local conditions.

The conclusion is stated through the characteristic polynomials rather than
through an explicit conjugating matrix, because that is all the descent
assembly needs and because the matrix is not canonical (it is unique only
up to `R'ˣ`). Irreducibility is what makes the `R'`-span of `𝒟.ρ(G_F)` a
full matrix algebra, which is Carayol's actual argument; without it the
theorem is false (a reducible `ρ` with an extension class outside `R'`
cannot be conjugated into `GL₂(R')`). It is consumed inside the
Rouquier–Nyssen leaf, which is why `hirrF` appears unused in the assembly
below.

WHAT THE ASSEMBLY PROVES, given the descended `ρ'` and the framing `e` with
`(ρ' ⊗ 𝒟.R)ᵉ = 𝒟.ρ`. Two of the four local clauses are FORMAL.

* *Determinant.* `det` commutes with base change
  (`LinearMap.det_baseChange`) and with conjugation (`LinearMap.det_conj`),
  so `det ρ'(g)` and the cyclotomic value have the same image in `𝒟.R`, and
  the inclusion `R' → 𝒟.R` is injective.
* *Unramifiedness away from `2ℓ`.* `ρ'(g)` is determined by `𝒟.ρ(g)` on the
  image of the standard frame — `𝒟.ρ(g)(e(1 ⊗ x)) = e(1 ⊗ ρ'(g)x)` — so
  `𝒟.ρ(g) = 1` forces `1 ⊗ ρ'(g)x = 1 ⊗ x`, and `1 ⊗ ·` is injective
  (`one_tmul_injective_hilbert`). Note this is applied ONLY at
  `g ∈ localInertiaGroup w`, through `IsUnramifiedAt.localInertiaGroup_le`:
  the inertia quantifier is never widened.
* *Charpolys.* Exactly `charpoly_baseChange_conj_hilbert`, at every
  `g : Γ F` — where the `ℚ`-level twin can only conclude at Frobenius
  elements of the good primes.

Only flatness at the places over `ℓ` and the tame condition at the places
over `2` genuinely need the `R'`-LATTICE, and those are the two descent
steps: flatness is `isFlatAt_of_conj_eq_of_numberField` followed by the
general `isFlatAt_of_subring_baseChange_of_numberField` (so on this side
only the Raynaud sub-object leaf is open), and tameness is the leaf.

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
    (hloc : IsLocalRing (hilbertTraceSubring ℓ 𝒟.ρ))
    (f : 𝒟.R →+* hilbertTraceSubring ℓ 𝒟.ρ)
    (hf : ∀ x : hilbertTraceSubring ℓ 𝒟.ρ, f (x : 𝒟.R) = x) :
    letI := hloc
    ∃ ρ' : FramedGaloisRep F (hilbertTraceSubring ℓ 𝒟.ρ) (Fin 2),
      IsHilbertHardlyRamified ℓ F
        (rank_finTwoPi (hilbertTraceSubring ℓ 𝒟.ρ)) ρ' ∧
      ∀ g : Γ F, ((ρ' g).charpoly).map (hilbertTraceSubring ℓ 𝒟.ρ).subtype =
        (𝒟.ρ g).charpoly := by
  letI := hloc
  obtain ⟨ρ', e, he⟩ :=
    exists_framedGaloisRep_baseChange_hilbertTraceSubring ℓ hℓ5 F hirrF 𝒟 hloc
  -- the structure map of `R'` is the inclusion, hence injective
  have hinj : Function.Injective
      (algebraMap (hilbertTraceSubring ℓ 𝒟.ρ) 𝒟.R) := Subtype.val_injective
  -- `𝒟.ρ` acts on the image of the standard `R'`-frame through `ρ'`
  have hbc : ∀ g : Γ F, ∀ x : Fin 2 → (hilbertTraceSubring ℓ 𝒟.ρ),
      𝒟.ρ g (e ((1 : 𝒟.R) ⊗ₜ[hilbertTraceSubring ℓ 𝒟.ρ] x)) =
        e ((1 : 𝒟.R) ⊗ₜ[hilbertTraceSubring ℓ 𝒟.ρ] (ρ' g x)) := by
    intro g x
    have hg : ((ρ'.baseChange 𝒟.R).conj e) g = 𝒟.ρ g := by rw [he]
    calc 𝒟.ρ g (e ((1 : 𝒟.R) ⊗ₜ[hilbertTraceSubring ℓ 𝒟.ρ] x))
        = ((ρ'.baseChange 𝒟.R).conj e) g
            (e ((1 : 𝒟.R) ⊗ₜ[hilbertTraceSubring ℓ 𝒟.ρ] x)) := by rw [hg]
      _ = e ((1 : 𝒟.R) ⊗ₜ[hilbertTraceSubring ℓ 𝒟.ρ] (ρ' g x)) := by
            rw [GaloisRep.conj_apply, LinearEquiv.conj_apply_apply,
              LinearEquiv.symm_apply_apply]
            congr 1
  -- an element killed by `𝒟.ρ` is killed by `ρ'`: the frame is injective
  have hkey : ∀ g : Γ F, 𝒟.ρ g = 1 → ρ' g = 1 := by
    intro g hg1
    refine LinearMap.ext fun x => ?_
    have h2 := hbc g x
    rw [hg1, Module.End.one_apply] at h2
    rw [Module.End.one_apply]
    exact (one_tmul_injective_hilbert hinj (Fin 2) (e.injective h2)).symm
  refine ⟨ρ', ⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · -- the determinant is the cyclotomic character, by injectivity
    intro g
    have hg : ((ρ'.baseChange 𝒟.R).conj e) g = 𝒟.ρ g := by rw [he]
    have hdet : (algebraMap (hilbertTraceSubring ℓ 𝒟.ρ) 𝒟.R) (ρ'.det g) =
        𝒟.ρ.det g := by
      rw [GaloisRep.det_apply 𝒟.ρ g, ← hg, GaloisRep.conj_apply,
        LinearEquiv.conj_apply, LinearMap.comp_assoc, LinearMap.det_conj]
      show _ = LinearMap.det (LinearMap.baseChange 𝒟.R (ρ' g))
      rw [LinearMap.det_baseChange, GaloisRep.det_apply ρ' g]
    rw [𝒟.isHilbertHardlyRamified.det g] at hdet
    exact hinj hdet
  · -- unramifiedness away from `2ℓ`, through the injective frame; the
    -- quantifier stays on `localInertiaGroup w`
    intro w hw2 hwl
    have hun := 𝒟.isHilbertHardlyRamified.isUnramified w hw2 hwl
    exact ⟨fun σ hσ => hkey _ (hun.localInertiaGroup_le hσ)⟩
  · -- flatness at every `w ∣ ℓ`: conjugation, then the subring descent
    intro w hw
    exact isFlatAt_of_subring_baseChange_of_numberField w 𝒟.isAdic
      (isFlatAt_of_conj_eq_of_numberField w e he
        (𝒟.isHilbertHardlyRamified.isFlat w hw))
  · -- the tame quadratic quotient at every `w ∣ 2` (descent leaf)
    intro w hw
    exact isHilbertTameAtTwo_of_baseChange_hilbertTraceSubring ℓ hℓ5 F 𝒟 hloc
      f hf ρ' e he w hw
  · -- the characteristic polynomials, through the base change
    intro g
    conv_rhs => rw [← he]
    exact (charpoly_baseChange_conj_hilbert ρ' e g).symm

/-- **The trace-subring inclusion of a WEAKLY UNIVERSAL datum admits a ring
retraction** (LEAF — new 2026-07-26, and it is the repaired form of an
obstruction that was previously hidden inside
`isHilbertTameAtTwo_of_baseChange_hilbertTraceSubring`): for a weakly
universal `𝒟` there is a ring homomorphism `f : 𝒟.R → R'` onto the trace
subring which is the identity on `R'`.

WHY THIS LEAF EXISTS AT ALL, and why it is not a smuggled hypothesis. The
FALSITY AUDIT in the docstring of
`isHilbertTameAtTwo_of_baseChange_hilbertTraceSubring` exhibits an explicit
`R' = ℤ_7[[Z]] ↪ ℤ_7[[Y]] = R` (by `Z ↦ 7Y`), together with a legitimate
unramified local representation at a place `w ∣ 2` of the totally real field
`F = ℚ(ζ₇)⁺`, for which the tame datum exists over `R` and does NOT exist
over `R'`. That refutes the tame descent as a statement about an arbitrary
datum. What kills the witness is exactly the retraction: `7·f(Y) = Z` is
unsolvable in `ℤ_7[[Z]]`. So the content that the descent needs is precisely
this, and it belongs in a named leaf rather than inside a proof.

THE ARGUMENT, which is Mazur §1.8 plus one round trip and is why the
statement is TRUE (only its formalization is open). Let `𝒟ᵘⁿⁱᵛ` be the
genuinely universal datum; for absolutely irreducible `ρbar` its ring
`Rᵘⁿⁱᵛ` is topologically generated by the traces of the universal
deformation. Weak universality of `𝒟` gives `𝒟.R → Rᵘⁿⁱᵛ`, and `𝒟` being a
datum gives `h : Rᵘⁿⁱᵛ → 𝒟.R`; both are compatible with the `ℤ_ℓ`-structure
maps, the reduction maps and — the load-bearing clause — the characteristic
polynomials at every `g : Γ F`. So the round trip `Rᵘⁿⁱᵛ → 𝒟.R → Rᵘⁿⁱᵛ`
fixes every charpoly coefficient, hence fixes a topologically generating set
of `Rᵘⁿⁱᵛ`, hence (being continuous) is the identity. Therefore `h` is split
injective, its image is closed and is exactly the closed subring generated
by the charpoly coefficients of `𝒟.ρ` together with `ℤ_ℓ` and the
Teichmüller roots — that is, `R' = hilbertTraceSubring ℓ 𝒟.ρ` — and
`f := h ∘ (the retraction)` corestricted to `R'` is the required map.

WHY `IsWeaklyUniversal` MAY NOT BE DROPPED. Without it the statement is
false, by the same `ℤ_7[[Z]] ↪ ℤ_7[[Y]]` witness: nothing constrains a bare
datum's ring to retract onto its trace subring.

FAITHFULNESS: `f` is asked to be a bare `RingHom`, not a continuous
`ℤ_ℓ`-algebra map. That is deliberate and is all the consumer uses — a unit
of `𝒟.R` lying in `R'` maps to a unit of `R'`, and `f` is automatically
`R'`-linear because it fixes `R'`. Asking for less makes the leaf easier
without making the consumer weaker.

References: Mazur, *Deforming Galois representations*, §1.8; Carayol, op.
cit., Théorème 1. -/
theorem exists_ringHom_retraction_hilbertTraceSubring
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ5 : 5 ≤ ℓ) (F : Type u) [Field F] [NumberField F]
    {k : Type u} [Field k] [Finite k] [TopologicalSpace k]
    {V : Type v} [AddCommGroup V] [Module k V] [Module.Finite k V]
    [Module.Free k V]
    {ρbar : GaloisRep ℚ k V}
    (hirrF : (ρbar.map (algebraMap ℚ F)).IsIrreducible)
    (𝒟 : HilbertDeformationDatum ℓ F ρbar) (h𝒟 : 𝒟.IsWeaklyUniversal) :
    ∃ f : 𝒟.R →+* hilbertTraceSubring ℓ 𝒟.ρ,
      ∀ x : hilbertTraceSubring ℓ 𝒟.ρ, f (x : 𝒟.R) = x :=
  sorry

/-- **Carayol subring-descent stratum at the `F` level** (PROVEN 2026-07-26
as glue over the two Carayol strata above —
`exists_isLocalRing_hilbertTraceSubring`, still a leaf, and
`exists_framedGaloisRep_hilbertTraceSubring`, PROVEN the same day over its
own three-way cut; the `F`-level twin of
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
    (𝒟 : HilbertDeformationDatum ℓ F ρbar)
    (f : 𝒟.R →+* hilbertTraceSubring ℓ 𝒟.ρ)
    (hf : ∀ x : hilbertTraceSubring ℓ 𝒟.ρ, f (x : 𝒟.R) = x) :
    ∃ 𝒟' : HilbertDeformationDatum ℓ F ρbar, 𝒟.IsTraceDescent 𝒟' := by
  classical
  obtain ⟨hloc, hnoeth, hadic, hcompl⟩ :=
    exists_isLocalRing_hilbertTraceSubring ℓ hℓ5 F hirrF 𝒟
  letI := hloc
  obtain ⟨ρ', hhr', hcp'⟩ :=
    exists_framedGaloisRep_hilbertTraceSubring ℓ hℓ5 F hirrF 𝒟 hloc f hf
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
composition glue over the two Carayol strata
`exists_isLocalRing_hilbertTraceSubring` (still a leaf) and
`exists_framedGaloisRep_hilbertTraceSubring` (PROVEN), through
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
  obtain ⟨f, hf⟩ :=
    exists_ringHom_retraction_hilbertTraceSubring ℓ hℓ5 F hirrF 𝒟 h𝒟
  obtain ⟨𝒟', ht', ι, hι1, hι2, hι3⟩ :=
    exists_hilbertTraceDescent ℓ hℓ5 F hlk hirrF 𝒟 f hf
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
Hecke input is a `HilbertHeckeAlgebra` and the target of the classifying map
must be an object of the `F`-level deformation CATEGORY. Presenting the one as
the other is `exists_hilbertHeckeDatum_of_hilbertHeckeAlgebra`.

That piece is now PROVEN, and the FORMAL-CONTENT AUDIT in its docstring is the
thing to read before reasoning about where the automorphic burden of this
module sits: it is NOT there. `HilbertHeckeAlgebra` carries
`isHilbertHardlyRamified` for its own `ρT`, i.e. a Hilbert Hecke algebra is of
the minimal level BY FIAT, so level lowering over totally real fields is part
of PRODUCING one — `nonempty_potentialHeckeDatum_of_five_le`, whose docstring
records it — and not of presenting one. What was genuinely missing there was
the topology, and that was an interface defect, repaired in
`HilbertHeckeAlgebra` rather than proven.

Why the classifying map is not left implicit: `IsWeaklyUniversal` produces it
with its three compatibilities, and those three are exactly the hypotheses the
two halves consume, so passing `ψ` explicitly keeps each half a statement
about a MAP rather than about an existential, which is what makes them
independently attackable and independently auditable. -/

/-- **A Hilbert Hecke algebra IS an object of the `F`-level deformation
category** (PROVEN 2026-07-26, after the INTERFACE REPAIR of
`HilbertHeckeAlgebra` recorded in that structure's docstring and audited
below; formerly a leaf advertised as "level lowering over totally real
fields", which it is not).

Given the residual-modularity input `T₀`, produce a Hilbert Hecke algebra `T`
together with a `HilbertDeformationDatum` whose coefficient ring IS `T.T`.
The witness is `T := T₀` and `𝒟T := T₀` read as a datum, field for field,
with `AlgEquiv.refl` for the isomorphism.

## FORMAL-CONTENT AUDIT (2026-07-26) — this statement carries NO arithmetic

Read this before using the statement, and before reasoning about where the
automorphic burden of the `R_F = T_F` cluster sits. Every clause a
`HilbertDeformationDatum` demands is ALREADY a field of `HilbertHeckeAlgebra`,
or follows from one in a line:

| datum field | supplied by |
| --- | --- |
| `commRing`, `topologicalSpace`, `isTopologicalRing`, `isLocalRing`, `algebra` | the same instance fields of `HilbertHeckeAlgebra` |
| `isNoetherianRing` | `IsNoetherianRing.of_finite ℤ_[ℓ] T₀.T` from `moduleFinite` |
| `isAdic`, `isAdicComplete` | the fields of the same names, added by the interface repair |
| `ρ`, `isHilbertHardlyRamified` | `ρT`, `isHilbertHardlyRamified` |
| `π`, `π_surjective`, `resid` | `πT`, `πT_surjective`, `residT` |

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
modular forms*, J. reine angew. Math. 537 (2001).

FORMAL-CONTENT AUDIT retained from the concurrent owner whose vacuous
proof this strengthening replaced -- it is the reason the strengthening
was needed, and it must not be lost with the proof:

**The previous docstring's headline claim — that the passage from `T₀` to `T`
is level lowering (Fujiwara, Jarvis, Rajaei) — is FALSE about the formal
statement, and was already contradicted inside that same docstring** ("so
formally this clause is inherited"). `HilbertHeckeAlgebra.isHilbertHardlyRamified`
says that `ρT` is unramified outside the places over `2ℓ`, flat over `ℓ`, and
tame with square-trivial unramified quotient character over `2` — i.e. **a
Hilbert Hecke algebra is of the minimal level BY FIAT**. There is no
non-minimal `T₀` to lower. Level lowering is therefore part of the cost of
PRODUCING a `HilbertHeckeAlgebra` at all, which is
`nonempty_potentialHeckeDatum_of_five_le`; that leaf's docstring has recorded
it correctly all along ("this last part silently contains level lowering over
totally real fields (Fujiwara, Jarvis, Rajaei)"). Nothing is lost by this
audit: the burden was never in two places, and it is not moved, only stated
once instead of twice.

**What WAS genuinely missing was the topology, and it was an interface defect
rather than a theorem.** `GaloisRep` is a CONTINUOUS homomorphism, so the type
of `ρT` and the meaning of `IsHilbertHardlyRamified` both depend on the
topology `T` carries; the datum demands the maximal-adic topology and
completeness, and the structure used to fix only `IsTopologicalRing`. No
arithmetic input can bridge that — retopologizing a ring does not transport a
continuity hypothesis, and the two conditions are incomparable. The previous
docstring diagnosed this exactly and prescribed the fix ("the honest fix, if
this leaf is ever attacked, is to pin the topology in `HilbertHeckeAlgebra`");
this owner carried the prescription out. See the INTERFACE REPAIR section of
`HilbertHeckeAlgebra`.

**Unused hypotheses are underscore-prefixed** so that the emptiness is
mechanically visible and not merely asserted: `_hℓ5`, `_htr`, `_hgal`,
`_hirrF` and `_𝒟₀` play no part. `_𝒟₀` in particular was added by an earlier
faithfulness repair to make the deformation category nonempty; `T₀` now makes
it nonempty on its own, which is precisely the content of this lemma. The
signature is nevertheless kept as it was, so that the consumer
`exists_heckeDatum_isWeaklyUniversal_isTraceGenerated` is untouched and so
that a future owner who reinstates a genuinely level-lowering form of the
statement — one taking a Hecke algebra whose `ρT` is NOT assumed hardly
ramified — inherits the binders it will need.

References, for the arithmetic that is NOT here but is in
`nonempty_potentialHeckeDatum_of_five_le`: Carayol, *Sur les représentations
`ℓ`-adiques associées aux formes modulaires de Hilbert*, Ann. Sci. ÉNS 19
(1986); Taylor, *On Galois representations associated to Hilbert modular
forms*, Invent. Math. 98 (1989); Fujiwara, *Deformation rings and Hecke
algebras in the totally real case*; Jarvis, *Level lowering for modular mod
`ℓ` representations over totally real fields*, Math. Ann. 313 (1999); Rajaei,
*On the levels of mod `ℓ` Hilbert modular forms*, J. reine angew. Math. 537
(2001). -/
theorem exists_hilbertHeckeDatum_of_hilbertHeckeAlgebra
    (ℓ : ℕ) [Fact ℓ.Prime] (_hℓ5 : 5 ≤ ℓ)
    (F : Type u) [Field F] [NumberField F]
    {k : Type u} [Field k] [TopologicalSpace k]
    {V : Type v} [AddCommGroup V] [Module k V] [Module.Finite k V]
    [Module.Free k V]
    {ρbar : GaloisRep ℚ k V}
    (_htr : NumberField.IsTotallyReal F) (_hgal : IsGalois ℚ F)
    (_hirrF : (ρbar.map (algebraMap ℚ F)).IsIrreducible)
    (_𝒟₀ : HilbertDeformationDatum ℓ F ρbar)
    (T₀ : HilbertHeckeAlgebra ℓ F ρbar) :
    ∃ (T : HilbertHeckeAlgebra ℓ F ρbar) (𝒟T : HilbertDeformationDatum ℓ F ρbar)
      (e : 𝒟T.R ≃ₐ[ℤ_[ℓ]] T.T), ∀ g : Γ F,
        ((𝒟T.ρ g).charpoly).map e.toAlgHom.toRingHom = (T.ρT g).charpoly := by
  -- The only field a `HilbertDeformationDatum` demands that a
  -- `HilbertHeckeAlgebra` does not carry verbatim; everything else is
  -- transported field for field.
  haveI hnoeth : IsNoetherianRing T₀.T := IsNoetherianRing.of_finite ℤ_[ℓ] T₀.T
  refine ⟨T₀,
    { R := T₀.T
      isNoetherianRing := hnoeth
      isAdic := T₀.isAdic
      isAdicComplete := T₀.isAdicComplete
      ρ := T₀.ρT
      isHilbertHardlyRamified := T₀.isHilbertHardlyRamified
      π := T₀.πT
      π_surjective := T₀.πT_surjective
      resid := T₀.residT },
    AlgEquiv.refl, fun g => ?_⟩
  -- `e = AlgEquiv.refl`, so the transport is `Polynomial.map (RingHom.id _)`.
  -- Stated as an explicit rewrite rather than by `simp`: the project simp set
  -- contains sorried lemmas, and using it here would taint this proof term
  -- with `sorryAx` for no mathematical reason.
  show ((T₀.ρT g).charpoly).map
      (AlgEquiv.refl (R := ℤ_[ℓ]) (A₁ := T₀.T)).toAlgHom.toRingHom
    = (T₀.ρT g).charpoly
  rw [show (AlgEquiv.refl (R := ℤ_[ℓ]) (A₁ := T₀.T)).toAlgHom.toRingHom
      = RingHom.id T₀.T from rfl]
  exact Polynomial.map_id

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

/-- **Taylor–Wiles primes of a totally real field `F`** — the `F`-level twin of
`Modularity/Patching.lean`'s `IsTaylorWilesPrimeSet`, with rational primes
replaced by finite places of `F`.

A place `w` of `F` is a Taylor–Wiles prime of level `n` for `ρbar|_{G_F}` when

* it is GOOD: `w ∤ 2ℓ`, so `ρbar|_{G_F}` is unramified at `w` and the
  `F`-level hardly ramified conditions impose nothing there;
* its residue field satisfies `N w ≡ 1 mod ℓ ^ n`, so that the `ℓ`-part of
  `(𝓞_F/w)ˣ` has order divisible by `ℓ ^ n` — this is what supplies the
  diamond torus `Δ_{Q_n}` and makes the auxiliary levels converge;
* `ρbar(Frob_w)` has DISTINCT eigenvalues in `k`, which is what splits the
  local deformation problem at `w` into a torus and lets the diamond operators
  act.

The eigenvalue condition is written on the characteristic polynomial so that it
makes sense over `k` without choosing a basis: `charFrob w` is monic of degree
`2`, and asking it to be `(X - α)(X - β)` with `α ≠ β` is exactly "split with
distinct eigenvalues".

This is the `F`-level form of Wiles, Ann. of Math. 141 (1995), ch. 3;
Diamond–Darmon–Taylor (1995), §5.3, as used by Fujiwara and Skinner–Wiles over
totally real fields. -/
def IsHilbertTaylorWilesPrimeSet (ℓ : ℕ) (F : Type u) [Field F] [NumberField F]
    {k : Type u} [Field k] [TopologicalSpace k]
    {V : Type v} [AddCommGroup V] [Module k V] [Module.Finite k V]
    [Module.Free k V]
    (ρbar : GaloisRep ℚ k V) (n : ℕ)
    (Q : Finset (HeightOneSpectrum (𝓞 F))) : Prop :=
  ∀ w ∈ Q, ((ℓ : ℕ) : 𝓞 F) ∉ w.asIdeal ∧ ((2 : ℕ) : 𝓞 F) ∉ w.asIdeal ∧
    Nat.card (𝓞 F ⧸ w.asIdeal) ≡ 1 [MOD ℓ ^ n] ∧
    ∃ α β : k, α ≠ β ∧
      (ρbar.map (algebraMap ℚ F)).charFrob w =
        (Polynomial.X - Polynomial.C α) * (Polynomial.X - Polynomial.C β)

/-- **The Taylor–Wiles prime supply over `F`** (LEAF — new 2026-07-26; the
`F`-level twin of `Modularity/Patching.lean`'s PROVEN
`exists_taylorWilesPrimeSet`).

For every level `n` and every required size `r` there is a set of at least `r`
Taylor–Wiles primes of `F` of level `n`.

THE CLASSICAL ROUTE, and it is Chebotarev over `F` rather than over `ℚ`: the
group-theoretic input is that `ρbar|_{G_F}` is irreducible with determinant the
mod-`ℓ` cyclotomic character — which is what `𝒟₀` supplies, since
`HilbertDeformationDatum.resid` transports the determinant clause of
`isHilbertHardlyRamified` down to the residual representation. For `ℓ ≥ 5` the
restriction of `ρbar|_{G_F}` to `Gal(F̄/F(ζ_{ℓ^n}))` then still has an element
`σ` whose image has two distinct eigenvalues (the odd-prime dichotomy of
Diamond–Darmon–Taylor §4.3; base change to `F` costs nothing because
irreducibility is hypothesised over `F`). Chebotarev density in the finite
extension cut out by `ρbar|_{G_F}` and `ζ_{ℓ^n}` produces infinitely many
places `w` of `F` with `Frob_w` in the class of `σ`, and each is automatically
good, satisfies `N w ≡ 1 mod ℓ ^ n` (because `σ` fixes `ζ_{ℓ^n}`), and has
split distinct-eigenvalue Frobenius.

`htr` and `hgal` are deliberately ABSENT: the prime supply is a Chebotarev
statement about `F` and the representation, with no archimedean or base-change
input. They enter only in `exists_hilbertPatchedModule` below, where the
Selmer/dual-Selmer count and Brauer induction genuinely need them.

References: Wiles, Ann. of Math. 141 (1995), ch. 3; Diamond–Darmon–Taylor
(1995), Lemma 5.31; Fujiwara, *Deformation rings and Hecke algebras in the
totally real case*, §3; Skinner–Wiles, Duke 107 (2001), §2. -/
theorem exists_hilbertTaylorWilesPrimeSet
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ5 : 5 ≤ ℓ)
    (F : Type u) [Field F] [NumberField F]
    {k : Type u} [Field k] [TopologicalSpace k]
    {V : Type v} [AddCommGroup V] [Module k V] [Module.Finite k V]
    [Module.Free k V]
    {ρbar : GaloisRep ℚ k V}
    (hirrF : (ρbar.map (algebraMap ℚ F)).IsIrreducible)
    (𝒟₀ : HilbertDeformationDatum ℓ F ρbar) :
    ∀ n r : ℕ, ∃ Q : Finset (HeightOneSpectrum (𝓞 F)),
      r ≤ Q.card ∧ IsHilbertTaylorWilesPrimeSet ℓ F ρbar n Q :=
  sorry

/-- **The Taylor–Wiles patching construction over `F`** (LEAF — new
2026-07-26; the `F`-level twin of `Modularity/Patching.lean`'s
`exists_patchedModule`, and the ONLY genuinely `F`-specific input to
`injective_classifyingMap_hilbertHeckeDatum` below).

Out of the `F`-level deformation and Hecke data, and the Taylor–Wiles prime
supply `hTW`, produce a `Modularity.PatchedModule` for the classifying map
`ψ : R_F → T_F` — the limit object of the patching process, carrying `M_∞`
finite over `R_∞ = ℤ_ℓ[[x₁, …, x_q]]` with an `M_∞`-regular sequence of length
`q + 1` in the maximal ideal, the patching surjection `R_∞ ↠ R_F`, and the
bottom identification `M_∞/𝔞M_∞ ≅ M₀` intertwining the actions through `ψ`.

WHY THE CUT IS HERE, and not lower. `Modularity.PatchedModule` mentions no base
field whatsoever — it is a statement about a ring map `ψ : Runiv →+* T` and a
module over a power-series ring — which is precisely why it, the
Auslander–Buchsbaum development behind it, and `PatchedModule.injective` could
be HOISTED out of the `ℚ`-level `Modularity/Patching.lean` into
`Modularity/PatchingCore.lean` and shared between the two base fields (see that
module's header for why hoisting rather than duplicating). Everything BELOW
this cut is pure commutative algebra and is already PROVEN; everything ABOVE it
is the arithmetic of Hilbert modular forms, and that is what this leaf asks
for:

* **Auxiliary deformation rings over `F`.** For each `n`, the deformation
  problem of `ρbar|_{G_F}` with the level raised at `Q_n` — `IsHilbertHardlyRamified`
  away from `Q_n`, and the split-torus local condition at each `w ∈ Q_n`
  supplied by the distinct-eigenvalue clause of `IsHilbertTaylorWilesPrimeSet`.
  The tangent-space bound making these quotients of a power-series ring in
  `q = dim_k H¹_{Q_n}(F, ad⁰ ρbar)` variables is the Greenberg–Wiles formula
  over `F`, and TOTAL REALNESS is exactly what makes its archimedean local
  terms come out — this is where `htr` is used.
* **Auxiliary Hecke modules of Hilbert modular forms.** The cohomology of the
  Shimura variety attached to a quaternion algebra over `F`, at level raised by
  `Q_n`, finite free over `ℤ_ℓ[Δ_{Q_n}]` by the Taylor–Wiles freeness lemma in
  Fujiwara's form; `Δ_{Q_n}` has order divisible by `ℓ ^ n` by the congruence
  clause of `IsHilbertTaylorWilesPrimeSet`.
* **Descent of the base change.** Identifying the bottom of the tower with the
  given Hecke data requires descending the base change from `F` to `ℚ`, which
  is Brauer induction over the Galois `F` — this is where `hgal` is used.
* **The pigeonhole / inverse-limit extraction** then produces the limit object.

WHAT THIS DELIBERATELY DOES NOT USE. The `ℚ`-level development also carries a
LEVEL-WISE interface, `TaylorWilesSystem`/`TaylorWilesLevelRaw`, between "the
arithmetic at each finite level" and "the extraction of the limit". That
interface has a known defect — its level-wise cut is missing the augmented
bound `bIdeal_le_aug`, so the bottom-level `bIdeal_le` is vacuous and no raw
level exists above the bottom datum — and its structures hardcode
`MvPowerSeries (Fin q) ℤ_[p]` in BOTH the diamond-coordinate and the
presentation role, which is correct only when `k = 𝔽_ℓ`. Cutting at
`PatchedModule` instead means this leaf inherits neither problem: it is stated
against the limit object only, and the limit object's regular sequence is
stated directly rather than assembled level by level.

`h𝒟w` and `h𝒟t` are what identify `ψ` with THE classifying map (see
`isUniversal_of_isWeaklyUniversal_isTraceGenerated` above), without which the
patched situation would be built for the wrong map; `e` is what supplies
`Module.Finite ℤ_[ℓ] 𝒟T.R` on the Hecke side.

References: Taylor–Wiles, Ann. of Math. 141 (1995); Diamond, Invent. Math. 128
(1997); Fujiwara, *Deformation rings and Hecke algebras in the totally real
case*; Skinner–Wiles, Duke 107 (2001); Kisin, Ann. of Math. 170 (2009);
Barnet-Lamb–Gee–Geraghty–Taylor, *Potential automorphy and change of weight*,
§§1–2. -/
theorem exists_hilbertPatchedModule
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
    (hψρ : ∀ g : Γ F, ((𝒟.ρ g).charpoly).map ψ = (𝒟T.ρ g).charpoly)
    (hTW : ∀ n r : ℕ, ∃ Q : Finset (HeightOneSpectrum (𝓞 F)),
      r ≤ Q.card ∧ IsHilbertTaylorWilesPrimeSet ℓ F ρbar n Q) :
    Nonempty (Modularity.PatchedModule.{u, u, u, u} ℓ ψ) :=
  sorry

/-- **`R_F ↪ T_F`: the classifying map is INJECTIVE** (PROVEN 2026-07-26 as
glue over `exists_hilbertTaylorWilesPrimeSet` and
`exists_hilbertPatchedModule`, on top of the HOISTED and already-proven
`Modularity.PatchedModule.injective`; the `F`-level twin of
`Modularity/Patching.lean`'s
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

PROOF (glue, 2026-07-26). The earlier version of this docstring recorded that
`Modularity/Patching.lean` carries the entire `ℚ`-level development in about
8900 lines, of which the commutative algebra — everything from
`exists_add_notMem_of_forall_not_le` to `free_of_isRegular_mvPowerSeries`,
together with the `PatchedModule` interface and `PatchedModule.injective` — is
base-field-independent and **should be hoisted rather than duplicated**. That
hoist has now been carried out: those 990 lines — `TaylorWilesCoefficients`,
`PatchedModule`, the Auslander–Buchsbaum section and `PatchedModule.injective`
— moved VERBATIM into
`Fermat/FLT/Modularity/PatchingCore.lean`, which is imported both by
`Modularity/Patching.lean` and by this module. It had to be a hoist and not a
local copy because `Modularity/Patching.lean` is DOWNSTREAM of this file (it
imports `HardlyRamified/Deformation.lean`, which `public import`s this module),
so the `ℚ`-level file cannot be imported here at all.

With that in hand this node is glue, and the frontier below it is exactly the
`F`-specific arithmetic:

1. `exists_hilbertTaylorWilesPrimeSet` — Taylor–Wiles primes at places of `F`
   rather than rational primes (Chebotarev over `F`).
2. `exists_hilbertPatchedModule` — the auxiliary deformation rings over `F` and
   the Hecke modules of Hilbert modular forms at the augmented levels, patched
   to the limit object. This is where `htr` (Greenberg–Wiles at the
   archimedean places) and `hgal` (Brauer induction for the base change) are
   consumed.
3. `Modularity.PatchedModule.injective` — PROVEN, and shared with the
   `ℚ`-level theorem.

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
  (exists_hilbertPatchedModule ℓ hℓ5 F htr hgal hirrF 𝒟 𝒟T T e h𝒟w h𝒟t ψ
      hψalg hψπ hψρ
      (exists_hilbertTaylorWilesPrimeSet ℓ hℓ5 F hirrF 𝒟)).elim
    Modularity.PatchedModule.injective

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
   Hecke input `T₀` did not: `HilbertHeckeAlgebra` pinned no topology on `T`
   beyond `IsTopologicalRing`, whereas `HilbertDeformationDatum` demands the
   MAXIMAL-ADIC one together with `IsAdicComplete`, and continuity of `ρT` for
   a coarser topology says nothing about continuity for the adic one. This is
   verbatim the defect that `exists_isWeaklyUniversal_hilbertDeformationDatum`
   was repaired for on the same day, and the repair is the same: a hypothesis
   `𝒟₀ : HilbertDeformationDatum ℓ F ρbar`. It costs the consumer below
   NOTHING — that consumer already has such a datum in hand as its own `𝒟`.

   SUPERSEDED IN ITS REASON, NOT IN ITS EFFECT (2026-07-26, third pass):
   `HilbertHeckeAlgebra` now carries `isAdic` and `isAdicComplete`, so `T₀`
   DOES make the deformation category nonempty — that is exactly what
   `exists_hilbertHeckeDatum_of_hilbertHeckeAlgebra` proves — and `𝒟₀` is
   consequently redundant here. It is kept because removing it would change
   the signature for no gain; both consumers discharge it for free.

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
    (hw2 : ∀ w : HeightOneSpectrum (𝓞 F), ((2 : ℕ) : 𝓞 F) ∈ w.asIdeal →
      ¬ ((ℓ : ℤ) ∣ ((Nat.card (𝓞 F ⧸ w.asIdeal) : ℤ) ^ 2 - 1)))
    (hirrF : (ρbar.map (algebraMap ℚ F)).IsIrreducible)
    (𝒟₀ : HilbertDeformationDatum ℓ F ρbar)
    (T₀ : HilbertHeckeAlgebra ℓ F ρbar) :
    ∃ (T : HilbertHeckeAlgebra ℓ F ρbar) (𝒟T : HilbertDeformationDatum ℓ F ρbar),
      𝒟T.IsWeaklyUniversal ∧ 𝒟T.IsTraceGenerated ∧
        Nonempty (𝒟T.R ≃ₐ[ℤ_[ℓ]] T.T) := by
  -- (1) the `F`-level universal ring, made trace-generated. Both steps are
  -- already cut leaves of this module; `𝒟₀` is what makes the first one apply.
  obtain ⟨𝒟₁, h𝒟₁⟩ :=
    exists_isWeaklyUniversal_hilbertDeformationDatum ℓ hℓ5 F hw2 hirrF 𝒟₀
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
    (hw2 : ∀ w : HeightOneSpectrum (𝓞 F), ((2 : ℕ) : 𝓞 F) ∈ w.asIdeal →
      ¬ ((ℓ : ℤ) ∣ ((Nat.card (𝓞 F ⧸ w.asIdeal) : ℤ) ^ 2 - 1)))
    (hirrF : (ρbar.map (algebraMap ℚ F)).IsIrreducible)
    (𝒟 : HilbertDeformationDatum ℓ F ρbar) (h𝒟 : 𝒟.IsWeaklyUniversal)
    (ht𝒟 : 𝒟.IsTraceGenerated)
    (T₀ : HilbertHeckeAlgebra ℓ F ρbar) :
    ∃ T : HilbertHeckeAlgebra ℓ F ρbar, Nonempty (𝒟.R ≃ₐ[ℤ_[ℓ]] T.T) := by
  obtain ⟨T, 𝒟T, hwT, htT, ⟨e⟩⟩ :=
    exists_heckeDatum_isWeaklyUniversal_isTraceGenerated ℓ hℓ5 F htr hgal hw2
      hirrF 𝒟 T₀
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
    (hw2 : ∀ w : HeightOneSpectrum (𝓞 F), ((2 : ℕ) : 𝓞 F) ∈ w.asIdeal →
      ¬ ((ℓ : ℤ) ∣ ((Nat.card (𝓞 F ⧸ w.asIdeal) : ℤ) ^ 2 - 1)))
    (hirrF : (ρbar.map (algebraMap ℚ F)).IsIrreducible)
    (𝒟 : HilbertDeformationDatum ℓ F ρbar) (h𝒟 : 𝒟.IsWeaklyUniversal)
    (ht𝒟 : 𝒟.IsTraceGenerated)
    (T₀ : HilbertHeckeAlgebra ℓ F ρbar) :
    Module.Finite ℤ_[ℓ] 𝒟.R := by
  obtain ⟨T, ⟨e⟩⟩ :=
    exists_heckeAlgebra_algEquiv_of_isWeaklyUniversal ℓ hℓ5 F hlk htr hgal hw2
      hirrF 𝒟 h𝒟 ht𝒟 T₀
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
  -- The tame-at-`2` gluing clause needs `ℓ ∤ N(w)² − 1` at every `w ∣ 2` — the
  -- sharp hypothesis of the repaired `isHilbertTameAtTwo_of_fibreProduct`. It is
  -- exactly what `PotentialHeckeDatum.residueCardTwo` is for: `N(w) = 2` makes
  -- the test element `3`, and `5 ≤ ℓ` finishes.
  have hw2 : ∀ w : HeightOneSpectrum (𝓞 P.F), ((2 : ℕ) : 𝓞 P.F) ∈ w.asIdeal →
      ¬ ((ℓ : ℤ) ∣ ((Nat.card (𝓞 P.F ⧸ w.asIdeal) : ℤ) ^ 2 - 1)) := by
    intro w hw hdvd
    rw [P.residueCardTwo w hw] at hdvd
    have h3 : (ℓ : ℤ) ∣ 3 := by norm_num at hdvd; exact hdvd
    have hle : (ℓ : ℤ) ≤ 3 := Int.le_of_dvd (by norm_num) h3
    omega
  obtain ⟨𝒟₀, h𝒟₀⟩ :=
    exists_isWeaklyUniversal_hilbertDeformationDatum ℓ hℓ5 P.F hw2 P.irreducibleF 𝒟'
  obtain ⟨𝒟, h𝒟, ht𝒟⟩ :=
    exists_isWeaklyUniversal_isTraceGenerated_hilbertDeformationDatum ℓ hℓ5 P.F
      (natCast_eq_zero_of_finite_algebra ℓ k) P.irreducibleF 𝒟₀ h𝒟₀
  obtain ⟨f, hfalg, -, hfρ⟩ := h𝒟 𝒟'
  -- (4) `R_F` is module-finite over `ℤ_ℓ`, by `R_F = T_F`
  haveI : Module.Finite ℤ_[ℓ] 𝒟.R :=
    moduleFinite_hilbertDeformation_of_isWeaklyUniversal ℓ hℓ5 P.F
      (natCast_eq_zero_of_finite_algebra ℓ k) P.totallyReal P.galoisF hw2
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
