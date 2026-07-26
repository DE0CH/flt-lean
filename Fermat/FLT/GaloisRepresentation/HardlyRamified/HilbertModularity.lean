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
   `exists_isWeaklyUniversal_hilbertDeformationDatum` is item 2 (LEAF).
4. `HilbertHeckeAlgebra` — `T_F`, carrying `Module.Finite ℤ_[ℓ] T_F`,
   generation by Hecke operators, and the residual eigensystem of
   `ρbar|_{G_F}`; `PotentialHeckeDatum` bundles it with the totally real
   `F` that Moret–Bailly produces, and
   `nonempty_potentialHeckeDatum_of_five_le` is items 3 + 5 (LEAF).
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
  -- (2) the `F`-level universal deformation ring `R_F`, made trace-generated
  obtain ⟨𝒟₀, h𝒟₀⟩ :=
    exists_isWeaklyUniversal_hilbertDeformationDatum ℓ P.F P.irreducibleF
  obtain ⟨𝒟, h𝒟, ht𝒟⟩ :=
    exists_isWeaklyUniversal_isTraceGenerated_hilbertDeformationDatum ℓ P.F
      P.irreducibleF 𝒟₀ h𝒟₀
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
