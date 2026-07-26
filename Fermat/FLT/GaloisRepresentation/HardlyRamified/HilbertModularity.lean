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
over the five leaves below and is what `Deformation.lean` consumes.

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
   `exists_isWeaklyUniversal_hilbertDeformationDatum` is item 2 (LEAF).
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
   item 4, Taylor–Wiles–Kisin patching in the Hilbert modular setting
   (LEAF).

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

/-- **Existence of the `F`-level universal deformation ring `R_F`** (LEAF
— item 2 of the audit's missing-machinery list).

Mazur's representability theorem for the hardly ramified deformation
problem over the totally real field `F`, for a residually IRREDUCIBLE
`ρbar|_{G_F}`: Schlessinger's criteria hold for the functor of `F`-level
deformations (the local conditions of `IsHilbertHardlyRamified` form a
deformation condition in the sense of Mazur §§18–23 / Conrad–Diamond–
Taylor §2 — closed under subobjects, quotients and fibre products), and
the tangent space is finite dimensional because `F` has finitely many
places above `2ℓ` and the relevant Selmer group is finite.

`Deformation.lean` carries the whole of this argument over `ℚ` — as the
PROVEN assembly `exists_isWeaklyUniversalOnIdentifiedFrames` over the
Schlessinger split — but that development is downstream of this module
and specific to the `ℚ`-level conditions, so it cannot be reused here
without the module split recorded in the leaf's docstring. Redoing it
over `F` is the module-sized build the audit predicted.

BLGGT §1 is the reference for the `F`-level ring in the shape used
here. -/
theorem exists_isWeaklyUniversal_hilbertDeformationDatum
    (ℓ : ℕ) [Fact ℓ.Prime] (F : Type u) [Field F] [NumberField F]
    {k : Type u} [Field k] [TopologicalSpace k]
    {V : Type v} [AddCommGroup V] [Module k V] [Module.Finite k V]
    [Module.Free k V]
    {ρbar : GaloisRep ℚ k V}
    (hirrF : (ρbar.map (algebraMap ℚ F)).IsIrreducible) :
    ∃ 𝒟 : HilbertDeformationDatum ℓ F ρbar, 𝒟.IsWeaklyUniversal :=
  sorry

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

/-! ### Item 4 — `R_F = T_F` -/

/-- **`R_F = T_F`** (LEAF — item 4 of the audit's missing-machinery list;
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
    {ρbar : GaloisRep ℚ k V}
    (htr : NumberField.IsTotallyReal F) (hgal : IsGalois ℚ F)
    (hirrF : (ρbar.map (algebraMap ℚ F)).IsIrreducible)
    (𝒟 : HilbertDeformationDatum ℓ F ρbar) (h𝒟 : 𝒟.IsWeaklyUniversal)
    (T₀ : HilbertHeckeAlgebra ℓ F ρbar) :
    ∃ T : HilbertHeckeAlgebra ℓ F ρbar, Nonempty (𝒟.R ≃ₐ[ℤ_[ℓ]] T.T) :=
  sorry

/-- **`Module.Finite ℤ_[ℓ] R_F`** (PROVEN over `R_F = T_F`): the `F`-level
universal deformation ring is a finite `ℤ_ℓ`-module, because it is
isomorphic to the Hecke algebra, which is one.

This is the single consequence of the whole Hilbert-modular development
that the assembly below consumes, and it is why the route is not
circular: the finiteness is imported from the automorphic side over `F`,
where modularity is a theorem, and never from `ℚ`, where it is what
pillar α is proving. -/
theorem moduleFinite_hilbertDeformation_of_isWeaklyUniversal
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ5 : 5 ≤ ℓ)
    (F : Type u) [Field F] [NumberField F]
    {k : Type u} [Field k] [TopologicalSpace k]
    {V : Type v} [AddCommGroup V] [Module k V] [Module.Finite k V]
    [Module.Free k V]
    {ρbar : GaloisRep ℚ k V}
    (htr : NumberField.IsTotallyReal F) (hgal : IsGalois ℚ F)
    (hirrF : (ρbar.map (algebraMap ℚ F)).IsIrreducible)
    (𝒟 : HilbertDeformationDatum ℓ F ρbar) (h𝒟 : 𝒟.IsWeaklyUniversal)
    (T₀ : HilbertHeckeAlgebra ℓ F ρbar) :
    Module.Finite ℤ_[ℓ] 𝒟.R := by
  obtain ⟨T, ⟨e⟩⟩ :=
    exists_heckeAlgebra_algEquiv_of_isWeaklyUniversal ℓ hℓ5 F htr hgal hirrF 𝒟 h𝒟 T₀
  exact Module.Finite.equiv e.symm.toLinearEquiv

/-! ### The assembly: integrality of the traces on a finite-index subgroup -/

/-- **The Hilbert-modular input of pillar α, assembled** (PROVEN over the
five leaves above): for a hardly ramified deformation `ρ` of an
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
   (`exists_isWeaklyUniversal_hilbertDeformationDatum`) and is
   module-finite over `ℤ_ℓ` by `R_F = T_F`
   (`moduleFinite_hilbertDeformation_of_isWeaklyUniversal`).
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
  -- (2) the `F`-level universal deformation ring `R_F`
  obtain ⟨𝒟, h𝒟⟩ :=
    exists_isWeaklyUniversal_hilbertDeformationDatum ℓ P.F P.irreducibleF
  -- (3) `ρ|_{G_F}` as an object of the `F`-level category
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
  obtain ⟨f, hfalg, -, hfρ⟩ := h𝒟 𝒟'
  -- (4) `R_F` is module-finite over `ℤ_ℓ`, by `R_F = T_F`
  haveI : Module.Finite ℤ_[ℓ] 𝒟.R :=
    moduleFinite_hilbertDeformation_of_isWeaklyUniversal ℓ hℓ5 P.F P.totallyReal P.galoisF
      P.irreducibleF 𝒟 h𝒟 P.hecke
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
