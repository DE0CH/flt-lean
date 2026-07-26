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
over the six leaves below and is what `Deformation.lean` consumes.

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
   over two sharper local leaves, `exists_padicTwoEmbedding_of_mem` and
   `isFlatAt_map_of_isFlatAt_under`; its determinant and unramifiedness
   clauses are now PROVEN glue.
3. `HilbertDeformationDatum` / `IsWeaklyUniversal` — Mazur's category and
   its universal object over `F`, i.e. `R_F`;
   `exists_isWeaklyUniversal_hilbertDeformationDatum` is item 2. It was
   REFUTED and REPAIRED on 2026-07-26 (it needs the category to be
   NONEMPTY; see the faithfulness section on it and the proven refutation
   `rank_eq_two_of_hilbertDeformationDatum`), and is now PROVEN as an
   assembly over SIX leaves — the arithmetic-free Schlessinger machine
   `exists_isWeaklyUniversal_hilbertDeformationDatum_of_clauses` together
   with the four deformation-condition clauses
   `isHilbertBaseChangeClause`, `isHilbertFibreProductClause`,
   `isHilbertFiniteFramesClause`, `isHilbertProLimitClause` and the
   Brauer–Nesbitt clause `isHilbertResidualRigidityClause` (PROVEN
   2026-07-26 over `BrauerNesbittConjugacy.lean`'s abstract dimension-`2`
   core `exists_linearEquiv_of_charpoly_eq`, under the added `[Finite k]`
   that core is proven with; the other four are still leaves).
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
   VACUITY AUDIT in its docstring and in the leaf's.
5. `exists_heckeAlgebra_algEquiv_of_isWeaklyUniversal` — **`R_F = T_F`**,
   item 4. DECOMPOSED 2026-07-26 and now PROVEN over
   `exists_heckeDatum_isWeaklyUniversal_isTraceGenerated` (LEAF —
   Taylor–Wiles–Kisin patching in the Hilbert modular setting, i.e. "the
   `F`-level universal ring IS a Hilbert Hecke algebra") plus the formal
   Carayol rigidity
   `HilbertDeformationDatum.isUniversal_of_isWeaklyUniversal_isTraceGenerated`
   and `HilbertDeformationDatum.exists_ringEquiv_of_isUniversal`, both
   PROVEN here.
6. `exists_isWeaklyUniversal_isTraceGenerated_hilbertDeformationDatum` —
   Carayol trace descent at the `F` level (LEAF, new 2026-07-26). It
   exists because a FAITHFULNESS AUDIT (in the `R_F = T_F` section
   below) found `R_F = T_F` and its finiteness corollary FALSE as
   originally stated: `IsWeaklyUniversal` is an existence-only mapping
   property, which `𝒟₀.R⟦X⟧` satisfies without being module-finite over
   `ℤ_ℓ`. Trace generation is the missing hypothesis, and this leaf is
   what supplies it to the assembly. `Deformation.lean` had already made
   exactly this repair at the `ℚ` level, on the same day; this module
   was written without it.

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
public import Fermat.FLT.Deformations.RepresentationTheory.GaloisRepTransport
public import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.GroupTheory.Index
public import Mathlib.LinearAlgebra.Charpoly.Basic
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.RingTheory.Adjoin.Basic
public import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.Finiteness.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Pi
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.Topology.Algebra.Algebra
-- proof-only: the abstract dimension-`2` Brauer–Nesbitt core
-- `exists_linearEquiv_of_charpoly_eq`, which discharges
-- `isHilbertResidualRigidityClause` below. `BrauerNesbittConjugacy.lean` sits
-- in `GaloisRepresentation/` and imports only `GaloisRep.lean`, `BrauerNesbitt.lean`,
-- `Chebotarev.lean` and mathlib, so it is OUTSIDE the circularity guard
-- (nothing from `Family.lean`, `Lift.lean`, `Modularity/*` or `Deformation.lean`);
-- `Deformation.lean`, the consumer of this module, already imports it too.
import Fermat.FLT.GaloisRepresentation.BrauerNesbittConjugacy

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

/-- **The local embedding `ℚ_2 ↪ F_w` at a place over `2`, and inertia**
(LEAF — the local half of item 1 of the audit's list, at the place `2`).

`F_w` is complete and contains `ℚ`, and `w | 2`, so the `w`-adic topology
restricts to the `2`-adic topology on `ℚ` and the inclusion `ℚ → F_w`
extends by continuity to the completion `ℚ_[2]`. The resulting `φ` is a
LOCAL homomorphism of complete discretely valued fields, so the induced
map `Γ F_w → Γ ℚ_[2]` carries inertia into inertia.

WHY BOTH HALVES ARE ONE LEAF: the inertia conclusion is about the SPECIFIC
`φ` produced by the first half. An arbitrary abstract `φ` over `ℚ` would
also do — every field embedding of `ℚ_[2]` into a complete field over `ℚ`
is automatically continuous — but that automatic continuity is itself a
theorem nobody here has, so bundling is the honest form.

THE ROUTE TO A PROOF, in the vocabulary that exists here (recorded because
it was mapped out and only NOT executed for size — it is a module, not a
lemma):

* mathlib's `Padic.adicCompletionEquiv R p : ℚ_[p] ≃A[ℚ] ((primesEquiv
  (R := R)).symm p).adicCompletion ℚ` is stated for a general Dedekind `R`
  with `[Algebra R ℚ] [IsFractionRing R ℚ] [IsIntegralClosure R ℤ ℚ]`, so it
  applies at `R := 𝓞 ℚ` DIRECTLY — no `ℤ ↔ 𝓞 ℚ` bridge is needed. That
  identifies `ℚ_[2]` with `v₂.adicCompletion ℚ` for `v₂ = w.under (𝓞 ℚ)`
  (`under_eq_of_natCast_mem` above supplies `v₂`);
* `HeightOneSpectrum.adicCompletionMap v₂ w (algebraMap ℚ F) _` then gives
  `v₂.adicCompletion ℚ →+* w.adicCompletion F`, and its composite with the
  equivalence is `φ`; `adicCompletionMap_coe` is the `comp` clause;
* for the inertia clause,
  `Field.absoluteGaloisGroup.map_mem_localInertiaGroup` gives
  `localInertiaGroup w → localInertiaGroup v₂`, and
  `Field.absoluteGaloisGroup.exists_conj_map_comp'` plus normality of
  inertia (`Field.absoluteGaloisGroup.conj_mem_localInertiaGroup`) absorb
  the conjugation ambiguity of `Field.absoluteGaloisGroup.map`.

WHAT IS GENUINELY MISSING is the last identification: `localInertiaGroup v₂`
is spelled through `IsLocalRing.maximalIdeal (IntegralClosure 𝒪_{v₂} …)`,
whereas `IsHardlyRamified.isTameAtTwo` is spelled through the maximal ideal
of `Z2bar = Valued.v.valuationSubring (ℚ_[2]ᵃˡᵍ)`. The two subrings are the
same object — the integral closure of `ℤ_2` in `ℚ_[2]ᵃˡᵍ` IS its valuation
ring, which is what `AbsoluteGaloisGroup.lean`'s `localValuationSubring`
proves in the other spelling — but nothing identifies them across the base
change `ℚ_[2] ≅ v₂.adicCompletion ℚ`.

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
            (Γ ℚ_[2]) :=
  sorry

/-- **Flatness descends to every place over a flat place** (LEAF — the
flatness half of item 1/2 of the audit's list).

`GaloisRep.IsFlatAt v` asks that for every open ideal `I` of the coefficient
ring the representation on `M/IM` be the geometric points of a finite flat
group scheme over `𝒪_v` (`GaloisRep.HasFlatProlongationAt`). Finite flat
group schemes base-change: if `G` is a finite flat `𝒪_v`-Hopf algebra with
`G ⊗ K_v` étale and geometric points `M/IM`, then `𝒪_w ⊗_{𝒪_v} G` is a
finite flat `𝒪_w`-Hopf algebra with the same geometric points read over
`L_w`, because `𝒪_v → 𝒪_w` is a local map of complete DVRs and the geometric
points are computed in a common algebraic closure.

WHAT IS MISSING: base change of `HopfAlgebra`/`Module.Flat`/`Module.Finite`
along `𝒪_v → 𝒪_w`, together with the identification of
`(K_w ⊗_{𝒪_w} (𝒪_w ⊗_{𝒪_v} G)) →ₐ[K_w] K_wᵃˡᵍ` with
`(K_v ⊗_{𝒪_v} G) →ₐ[K_v] K_vᵃˡᵍ` as `Γ K_w`-sets, along the
`Field.absoluteGaloisGroup.map` of the completion map — the same map
`isUnramifiedAt_map_of_isUnramifiedAt_under` uses, with the same
conjugation ambiguity, which `HasFlatProlongationAt.of_equiv` is already
shaped to absorb.

FAITHFULNESS: a statement about the EXISTENCE of a prolongation upstairs
given one downstairs, produced by base change — not a descent of existence
from `𝒪^nr`, so the `𝒪ᵥ` rule does not bite. -/
theorem isFlatAt_map_of_isFlatAt_under
    {K : Type*} [Field K] [NumberField K] {L : Type*} [Field L] [NumberField L]
    [Algebra K L]
    {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsLocalRing A]
    {M : Type*} [AddCommGroup M] [Module A M] [Module.Finite A M] [Module.Free A M]
    (ρ : GaloisRep K A M) (w : HeightOneSpectrum (𝓞 L))
    (h : ρ.IsFlatAt (w.under (𝓞 K))) :
    (ρ.map (algebraMap K L)).IsFlatAt w :=
  sorry

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
* *flatness* (over `isFlatAt_map_of_isFlatAt_under`): a place `w | ℓ` lies
  over `ℓ` (`under_eq_of_natCast_mem`), and flat prolongations base-change
  along `𝒪_ℓ → 𝒪_w`;
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

/-- **Functoriality of the `F`-level condition** (LEAF).

Over `ℚ` this is `Deformation.lean`'s PROVEN
`isHardlyRamified_pushforwardFrame`, whose only genuine residue is the
flatness transfer `isFlatAt_baseChange`; the other three clauses of
`IsHardlyRamified` are formal. The same split applies here, place by place:
the determinant clause is an identity in `R` pushed along `ψ`, the
unramifiedness and tameness clauses are inclusions of kernels, and the
flatness clause at each `w ∣ ℓ` is the base change of a finite flat group
scheme along `𝒪_{F_w} → 𝒪_{F_w} ⊗ A`.

None of that development exists over a general number field: `Threeadic.lean`
and `Deformation.lean` state their flat-prolongation transfer over `ℚ`'s
places. Hoisting it to a variable base field is the bulk of this leaf. -/
theorem isHilbertBaseChangeClause (ℓ : ℕ) [Fact ℓ.Prime]
    (F : Type u) [Field F] [NumberField F] :
    IsHilbertBaseChangeClause ℓ F :=
  sorry

/-- **Gluing along fibre products** (LEAF; Schlessinger's H1 and H2).

Over `ℚ` this is `Deformation.lean`'s leaf `isHardlyRamified_of_fibreProduct`.
The mathematical content is that each clause of the local condition is
detected componentwise: a homomorphism into `GL₂` of a fibre product is
exactly a compatible pair of homomorphisms, the determinant clause and the
order-`2` clause are equations that hold iff they hold in both components,
and the inertia-kernel clauses are intersections. Only the flatness clause
at `w ∣ ℓ` needs an argument — the fibre product of two finite flat group
schemes over `𝒪_{F_w}` along a common quotient is again one, which is where
the surjectivity of `f₂` and the embedding hypothesis are used. -/
theorem isHilbertFibreProductClause (ℓ : ℕ) [Fact ℓ.Prime]
    (F : Type u) [Field F] [NumberField F] :
    IsHilbertFibreProductClause ℓ F :=
  sorry

/-- **Finiteness of the hardly ramified frames over a finite level** (LEAF;
Schlessinger's H3).

Over `ℚ` this is `Deformation.lean`'s leaf
`finite_setOf_isHardlyRamified_frames`. The argument is Hermite–Minkowski:
a hardly ramified frame over the finite ring `A` is a homomorphism
`G_F → GL₂(A)` unramified outside the finitely many places of `F` above
`2ℓ` and with bounded ramification at those, hence factors through the
Galois group of an extension of `F` of bounded degree and bounded
discriminant, of which there are finitely many; and `GL₂(A)` is finite. -/
theorem isHilbertFiniteFramesClause (ℓ : ℕ) [Fact ℓ.Prime]
    (F : Type u) [Field F] [NumberField F] :
    IsHilbertFiniteFramesClause ℓ F :=
  sorry

/-- **Detection of the `F`-level condition on the finite levels** (LEAF).

Over `ℚ` this is `Deformation.lean`'s leaf
`isHardlyRamified_of_forall_isOpen_quotient`. The determinant,
unramifiedness and tameness clauses are separation statements — a complete
separated local ring injects into the inverse limit of its finite
quotients, so an identity or a kernel inclusion holding at every level holds
over `R`; the flatness clause is DEFINITIONALLY a statement about the open
quotients (`GaloisRep.IsFlatAt.cond` quantifies over open ideals), which is
why this clause is available at all rather than being a genuine limit
theorem about group schemes. -/
theorem isHilbertProLimitClause (ℓ : ℕ) [Fact ℓ.Prime]
    (F : Type u) [Field F] [NumberField F] :
    IsHilbertProLimitClause ℓ F :=
  sorry

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

/-- **Existence of the `F`-level universal deformation ring `R_F`, over the
deformation-condition package** (LEAF — item 2 of the audit's
missing-machinery list, after the 2026-07-26 cut; this is the
ARITHMETIC-FREE half).

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

WHAT IS AND IS NOT IN THIS LEAF. In: Schlessinger's inductive
small-extension argument over H1–H3, the passage to the inverse limit, the
Noetherian/`IsAdic`/`IsAdicComplete` upgrade of the limit (Mazur's `Φ_ℓ`
criterion — the pure commutative algebra of `ProfiniteLocalNoetherian.lean`,
which is upstream of this module and may be imported when this leaf is
attacked), the lifting of the classifying map from the Artinian levels to a
complete Noetherian test object along `R' = lim R' ⧸ 𝔪'ⁿ`, and the
conjugation of an arbitrary object's residual frame onto `ρbar|_{G_F}`
supplied by `hrig`. Out: every arithmetic statement about
`IsHilbertHardlyRamified`, which enters only through the four clauses.

WHY `𝒟₀`. It is the nonemptiness of the category, i.e. Schlessinger's
"`F(k)` is a point": it supplies the residual frame that the machine
deforms and it pins `finrank k V = 2`. Without it the statement is FALSE —
see the faithfulness repair recorded above.

`Deformation.lean` carries the whole of this argument over `ℚ`, as the
PROVEN assembly `exists_isWeaklyUniversalOnIdentifiedFrames` over the same
construction/finiteness split, but that development is downstream of this
module and specific to the `ℚ`-level conditions, so it cannot be reused
here. Its architecture is nevertheless the map to follow: the two nodes
`exists_universalFrame_profinite_of_deformationCondition` (construct a
profinite pro-object) and
`isNoetherianRing_isAdic_of_profinite_of_finite_ringHom` (upgrade it) are
the natural sub-cut of this leaf, and only the second of them is already
importable here.

CIRCULARITY GUARD (inherited). Nothing from `Family.lean`, `Lift.lean`,
`Modularity/*` or `Deformation.lean` may be imported to discharge this; in
particular the odd-prime dichotomy
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
    {k : Type u} [Field k] [TopologicalSpace k]
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
    ∃ 𝒟 : HilbertDeformationDatum ℓ F ρbar, 𝒟.IsWeaklyUniversal :=
  sorry

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

`[Finite k]` (added 2026-07-26 with the proof of
`isHilbertResidualRigidityClause`, which is the only place it is used) is the
hypothesis under which the residual-rigidity clause is discharged; see that
theorem's docstring for why the available dimension-`2` Brauer–Nesbitt core
needs it and why no consumer loses anything — the residue field of the
deformation problem is finite in every consumer of this module. -/
theorem exists_isWeaklyUniversal_hilbertDeformationDatum
    (ℓ : ℕ) [Fact ℓ.Prime] (F : Type u) [Field F] [NumberField F]
    {k : Type u} [Field k] [Finite k] [TopologicalSpace k]
    {V : Type v} [AddCommGroup V] [Module k V] [Module.Finite k V]
    [Module.Free k V]
    {ρbar : GaloisRep ℚ k V}
    (hirrF : (ρbar.map (algebraMap ℚ F)).IsIrreducible)
    (𝒟₀ : HilbertDeformationDatum ℓ F ρbar) :
    ∃ 𝒟 : HilbertDeformationDatum ℓ F ρbar, 𝒟.IsWeaklyUniversal :=
  exists_isWeaklyUniversal_hilbertDeformationDatum_of_clauses ℓ F hirrF 𝒟₀
    (isHilbertBaseChangeClause ℓ F) (isHilbertFibreProductClause ℓ F)
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

**Why NOT `Function.Surjective πT`**, though a deformation datum has it:
`k` is only assumed to be the coefficient field of `ρbar`, and it may
properly contain the field generated by the Frobenius traces (`ρbar`
defined over `𝔽_ℓ` and viewed over `𝔽_{ℓ²}`, say), while `adjoin_heckeT`
confines the image of `πT` to the `ℤ_[ℓ]`-algebra generated by those
traces. Demanding surjectivity would make the production leaf FALSE in that
case. A consumer that wants to see `T` as an object of the deformation
category must therefore supply the residual-field bookkeeping itself; that
is recorded here, not hidden. -/
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
  /-- `T` is generated over `ℤ_ℓ` by the good-place Hecke operators. -/
  adjoin_heckeT : Algebra.adjoin ℤ_[ℓ] (heckeT '' {w | w ∉ bad}) = ⊤
  /-- The reduction map onto the residual coefficient field. -/
  πT : T →+* k
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
from the new leaf
`exists_isWeaklyUniversal_isTraceGenerated_hilbertDeformationDatum`, the
`F`-level twin of `Deformation.lean`'s Carayol trace descent.

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

/-- **Carayol trace descent at the `F` level** (LEAF — new 2026-07-26, the
`F`-level twin of `Deformation.lean`'s PROVEN
`exists_isWeaklyUniversal_isTraceGenerated_of_isWeaklyUniversal`): a
weakly universal `F`-level datum may be replaced by one that is ALSO
trace-generated.

Carayol's theorem (*Formes modulaires et représentations galoisiennes à
valeurs dans un anneau local complet*, Théorème 1 and Lemme 1): for a
residually absolutely irreducible `ρbar|_{G_F}`, the representation
`𝒟.ρ` descends to the closed `ℤ_ℓ`-subalgebra of `𝒟.R` topologically
generated by the Teichmüller roots and the coefficients of its own
characteristic polynomials, and the descended datum is again an object of
the category; the descended datum is trace-generated by construction, and
weakly universal because the classifying map out of `𝒟` composed with
the inclusion is compatible in each of the three clauses.

At the `ℚ` level this is PROVEN in `Deformation.lean` over the leaf
`exists_isTraceGenerated_ringHom`, whose proof constructs the sub-datum
explicitly (`exists_isTraceGenerated_ringHom_of_forall_trace_mem`). That
development is downstream of this module and specific to the `ℚ`-level
conditions, so it is re-opened here rather than reused; porting it is the
obvious way to close this leaf.

WHY THIS LEAF EXISTS AT ALL: `exists_isWeaklyUniversal_hilbertDeformationDatum`
produces only weak universality, and the faithfulness audit at the head of
this section shows that weak universality alone cannot support
`R_F = T_F`. This is the step that supplies the missing hypothesis. -/
theorem exists_isWeaklyUniversal_isTraceGenerated_hilbertDeformationDatum
    (ℓ : ℕ) [Fact ℓ.Prime] (F : Type u) [Field F] [NumberField F]
    {k : Type u} [Field k] [TopologicalSpace k]
    {V : Type v} [AddCommGroup V] [Module k V] [Module.Finite k V]
    [Module.Free k V]
    {ρbar : GaloisRep ℚ k V}
    (hirrF : (ρbar.map (algebraMap ℚ F)).IsIrreducible)
    (𝒟 : HilbertDeformationDatum ℓ F ρbar) (h𝒟 : 𝒟.IsWeaklyUniversal) :
    ∃ 𝒟' : HilbertDeformationDatum ℓ F ρbar,
      𝒟'.IsWeaklyUniversal ∧ 𝒟'.IsTraceGenerated :=
  sorry

/-- **`R_F` IS a Hilbert Hecke algebra** (LEAF — new 2026-07-26; the
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
galoisiennes à valeurs dans un anneau local complet*. -/
theorem exists_heckeDatum_isWeaklyUniversal_isTraceGenerated
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ5 : 5 ≤ ℓ)
    (F : Type u) [Field F] [NumberField F]
    {k : Type u} [Field k] [TopologicalSpace k]
    {V : Type v} [AddCommGroup V] [Module k V] [Module.Finite k V]
    [Module.Free k V]
    {ρbar : GaloisRep ℚ k V}
    (htr : NumberField.IsTotallyReal F) (hgal : IsGalois ℚ F)
    (hirrF : (ρbar.map (algebraMap ℚ F)).IsIrreducible)
    (T₀ : HilbertHeckeAlgebra ℓ F ρbar) :
    ∃ (T : HilbertHeckeAlgebra ℓ F ρbar) (𝒟T : HilbertDeformationDatum ℓ F ρbar),
      𝒟T.IsWeaklyUniversal ∧ 𝒟T.IsTraceGenerated ∧
        Nonempty (𝒟T.R ≃ₐ[ℤ_[ℓ]] T.T) :=
  sorry

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
    {k : Type u} [Field k] [TopologicalSpace k]
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
    exists_heckeDatum_isWeaklyUniversal_isTraceGenerated ℓ hℓ5 F htr hgal hirrF T₀
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
    {k : Type u} [Field k] [TopologicalSpace k]
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
    exists_isWeaklyUniversal_hilbertDeformationDatum ℓ P.F P.irreducibleF 𝒟'
  obtain ⟨𝒟, h𝒟, ht𝒟⟩ :=
    exists_isWeaklyUniversal_isTraceGenerated_hilbertDeformationDatum ℓ P.F
      P.irreducibleF 𝒟₀ h𝒟₀
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
