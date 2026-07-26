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
`HardlyRamified/Defs.lean` and mathlib, so `Deformation.lean` may
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
   missing-machinery list (LEAF).
2. `IsHilbertHardlyRamified` — the `F`-level local deformation condition,
   and `isHilbertHardlyRamified_map_of_isHardlyRamified`: the restriction
   of a hardly ramified representation satisfies it (LEAF).
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
   Brauer–Nesbitt clause `isHilbertResidualRigidityClause`.
4. `HilbertHeckeAlgebra` — `T_F`, carrying `Module.Finite ℤ_[ℓ] T_F`,
   generation by Hecke operators, and the residual eigensystem of
   `ρbar|_{G_F}`; `PotentialHeckeDatum` bundles it with the totally real
   `F` that Moret–Bailly produces, and
   `nonempty_potentialHeckeDatum_of_five_le` is items 3 + 5 (LEAF).
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

/-- **`[G_ℚ : G_F] = [F : ℚ] < ∞`** (LEAF — item 1 of the audit's
missing-machinery list).

The classical content: `Field.absoluteGaloisGroup.map (algebraMap ℚ F)`
is injective (source and target algebraic closures are identified by the
chosen embedding, and an automorphism of `Fᵃˡᵍ` fixing `F` is determined
by its restriction to `ℚᵃˡᵍ = Fᵃˡᵍ`), with image the fixing subgroup of
the image of `F` in `ℚᵃˡᵍ`; the orbit–stabiliser bijection
`G_ℚ / G_F ≃ Hom_ℚ(F, ℚᵃˡᵍ)` then has `[F : ℚ]` elements, finite because
`F` is a number field.

Nothing in mathlib packages this: `InfiniteGalois` gives the
Krull-topological correspondence between intermediate fields and closed
subgroups, but the finite-index statement for a FINITE intermediate
extension has to be assembled from the count of `ℚ`-algebra maps
`F → ℚᵃˡᵍ` (`IntermediateField.card_algHom_eq_finrank` and friends) and
the coset bijection.

Formalization note: `Subgroup.FiniteIndex` only asks that the index be
nonzero, so the sharp value `[F : ℚ]` is deliberately NOT part of the
statement — no consumer here needs it. -/
theorem finiteIndex_galoisSubgroup (F : Type u) [Field F] [NumberField F] :
    (galoisSubgroup F).FiniteIndex :=
  sorry

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

/-- **Restriction of a hardly ramified representation is hardly ramified
over `F`** (LEAF — the local half of item 1/2 of the audit's list).

The four clauses are four standard compatibilities of restriction along
`G_F ≤ G_ℚ`, none of which exists in this repository or in mathlib:

* *determinant*: `GaloisRep.map` is precomposition with
  `Field.absoluteGaloisGroup.map` and `GaloisRep.det` is postcomposition
  with `LinearMap.det`, so the two commute — with the definition chosen
  above this clause alone is elementary;
* *unramifiedness*: a place `w` of `F` not above `2` or `ℓ` lies over a
  rational prime `p ∉ {2, ℓ}`, and the inertia group at `w` maps into the
  inertia group at `p`, hence into the kernel;
* *flatness*: the places of `F` above `ℓ` lie over `ℓ`, and finite flat
  group schemes base-change along `F_w / ℚ_ℓ`, so a flat prolongation of
  `ρ|_{G_ℓ}` prolongs `ρ|_{G_{F_w}}`;
* *tameness at `2`*: the `ℚ`-level quotient `π : V ↠ R` and its character
  `δ` are restricted along `G_{F_w} → G_{ℚ_2}`; `δ`'s unramifiedness
  survives because inertia at `w` maps into inertia at `2`, and its
  order-dividing-`2` property is an identity, hence stable under
  restriction. This clause is the only one whose `ℚ`-level statement is
  phrased over the bespoke `Z2bar` inertia subgroup rather than over
  `localInertiaGroup`, so it additionally needs those two subgroups to be
  identified.

They are grouped into one leaf because they share the single missing
ingredient — the comparison of the local decomposition and inertia groups
of `F` at `w` with those of `ℚ` at the prime below `w`, which is the
local half of item 1. -/
theorem isHilbertHardlyRamified_map_of_isHardlyRamified
    (ℓ : ℕ) [Fact ℓ.Prime] {hℓOdd : Odd ℓ}
    (F : Type u) [Field F] [NumberField F]
    {R : Type u} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    [IsLocalRing R] [Algebra ℤ_[ℓ] R]
    (ρ : FramedGaloisRep ℚ R (Fin 2))
    (hρ : IsHardlyRamified hℓOdd (rank_finTwoPi R) ρ) :
    IsHilbertHardlyRamified ℓ F (rank_finTwoPi R) (ρ.map (algebraMap ℚ F)) :=
  sorry

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

/-- **Brauer–Nesbitt over `F`** (LEAF): equal characteristic polynomials at
every element identify a framed representation with the irreducible
`ρbar|_{G_F}` up to conjugation. See `IsHilbertResidualRigidityClause` for
the argument and for why the `ℚ`-level twin is the harder statement. -/
theorem isHilbertResidualRigidityClause (F : Type u) [Field F] [NumberField F]
    {k : Type u} [Field k] [TopologicalSpace k]
    {V : Type v} [AddCommGroup V] [Module k V] [Module.Finite k V]
    [Module.Free k V] (ρbar : GaloisRep ℚ k V) :
    IsHilbertResidualRigidityClause F ρbar :=
  sorry

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
rigidity. -/
theorem exists_isWeaklyUniversal_hilbertDeformationDatum
    (ℓ : ℕ) [Fact ℓ.Prime] (F : Type u) [Field F] [NumberField F]
    {k : Type u} [Field k] [TopologicalSpace k]
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

The three components that carry the arithmetic:

* the instance field `moduleFinite`, i.e. **`Module.Finite ℤ_[ℓ] T`**.
  This is the whole point of the structure: it is the item
  `Modularity/Patching.lean` takes as a HYPOTHESIS and that nothing in
  the repository supplies. Classically it holds because the space of
  Hilbert modular forms of fixed weight and level is a finitely generated
  `ℤ_ℓ`-module on which `T` acts faithfully.
* `adjoin_heckeT` — `T` is generated over `ℤ_ℓ` by the good-place Hecke
  operators. Without it the structure would be inhabited by `ℤ_ℓ` itself
  with `heckeT` arbitrary, and would record nothing.
* `residualT` — **residual modularity of `ρbar|_{G_F}`**: the reduction of
  the Hecke eigensystem is the system of Frobenius traces of
  `ρbar|_{G_F}`. This is the clause potential modularity produces and
  `R_F = T_F` consumes; `−(charFrob w).coeff 1` is the trace of Frobenius
  at `w`, the `charFrob` being monic of degree `2`.

No non-degeneracy clause is imposed on `bad`: every statement here
quantifies over places OUTSIDE `bad`, so a larger bad set is a weaker
datum, which is the direction that keeps the production leaf honest. -/
structure HilbertHeckeAlgebra (ℓ : ℕ) [Fact ℓ.Prime]
    (F : Type u) [Field F] [NumberField F]
    {k : Type u} [Field k] [TopologicalSpace k]
    {V : Type v} [AddCommGroup V] [Module k V] [Module.Finite k V]
    [Module.Free k V]
    (ρbar : GaloisRep ℚ k V) where
  /-- The Hecke algebra. -/
  T : Type u
  [commRing : CommRing T]
  [algebra : Algebra ℤ_[ℓ] T]
  [moduleFinite : Module.Finite ℤ_[ℓ] T]
  /-- The finite bad set: the level of the newform and the places over
  `2` and `ℓ`. -/
  bad : Finset (HeightOneSpectrum (𝓞 F))
  /-- The Hecke operator at a place. -/
  heckeT : HeightOneSpectrum (𝓞 F) → T
  /-- `T` is generated over `ℤ_ℓ` by the good-place Hecke operators. -/
  adjoin_heckeT : Algebra.adjoin ℤ_[ℓ] (heckeT '' {w | w ∉ bad}) = ⊤
  /-- The reduction map onto the residual coefficient field. -/
  πT : T →+* k
  /-- Residual modularity of `ρbar|_{G_F}`: the reduced Hecke eigensystem
  is its system of Frobenius traces. -/
  residualT : ∀ w ∉ bad, πT (heckeT w) =
    -((ρbar.map (algebraMap ℚ F)).charFrob w).coeff 1

attribute [instance] HilbertHeckeAlgebra.commRing
  HilbertHeckeAlgebra.algebra HilbertHeckeAlgebra.moduleFinite

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
proven over this leaf. -/
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
  -- (3) the `F`-level universal deformation ring `R_F`
  obtain ⟨𝒟, h𝒟⟩ :=
    exists_isWeaklyUniversal_hilbertDeformationDatum ℓ P.F P.irreducibleF 𝒟'
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
