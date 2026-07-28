/-
Copyright (c) 2026 Deyao Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.RingTheory.Ideal.MinimalPrime.Basic
public import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import Mathlib.Topology.Connected.Clopen
public import Mathlib.Topology.Irreducible

/-!
# Irreducible open neighbourhoods, and connectedness ⟹ irreducibility

Three statements the pin does not have, in increasing order of structure:

* `irreducibleSpace_of_isOpen_isIrreducible_nhds` — pure point-set topology: a CONNECTED
  space in which every point has an irreducible OPEN neighbourhood is irreducible.
* `exists_isOpen_isIrreducible_of_isDomain_localization` — pure commutative algebra: a prime
  `p` of a NOETHERIAN ring whose localization `R_p` is a domain has an irreducible open
  neighbourhood in `Spec R`.
* `AlgebraicGeometry.exists_isOpen_isIrreducible_nhds_of_isDomain_stalk` — the scheme-level
  form of the second: a point with domain stalk on a locally noetherian scheme has an
  irreducible open neighbourhood.

Composed, they say: **a connected, locally noetherian scheme whose stalks are all domains is
irreducible** — which with `isReduced_of_isReduced_stalk` and
`isIntegral_of_irreducibleSpace_of_isReduced` is the route from "smooth over a field" to
"integral".

## Why this module exists

This block was **independently written three times** in this development:

* `GaloisRepresentation.Modularity.irreducibleSpace_of_connectedSpace_of_locallyIrreducible`,
  `…exists_isOpen_isIrreducible_primeSpectrum` and
  `…exists_isOpen_isIrreducible_of_isDomain_stalk` in `Fermat/FLT/Modularity/MoretBailly.lean`
  (2026-07-26);
* a verbatim restatement under the present names in
  `Fermat/FLT/Mathlib/AlgebraicGeometry/CurveExtension.lean` (2026-07-27), made because
  `MoretBailly.lean` is a 34 000-line module whose import cone reaches the Deformations and
  automorphic-form subtrees, and importing it to reach 130 lines of point-set topology would
  have been a cone-growth trade nobody would take.

That restatement's own docstring asked for exactly this hoist: *"if those three are ever
hoisted into `Fermat/FLT/Mathlib/`, delete this block and import them instead."*  Both copies
are now deleted and both files import this module.

**The module has ZERO `Fermat` imports**, deliberately — the same property that lets
`Fermat/FLT/Modularity/RegularStalks.lean` be consumed from both sides of the Modularity
subtree.  So it is importable from anywhere, including from mathlib-shim modules that must
not reach into the project proper, and a fourth copy should never be necessary.
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

/-- **A CONNECTED, LOCALLY IRREDUCIBLE SPACE IS IRREDUCIBLE** (PROVEN — pure point-set
topology, no schemes and no noetherian hypothesis).

If every point has an irreducible OPEN neighbourhood then the irreducible component of any
point is open (each of its points has a neighbourhood inside it, since the closure of an
irreducible open meeting the component IS the component), hence clopen, hence everything.

The openness is load-bearing and the statement is FALSE with "irreducible open
neighbourhood" weakened to "irreducible subset containing the point": two lines crossing at
the origin form a connected space in which every point lies on an irreducible subset, and
which is reducible — the origin has no irreducible *open* neighbourhood. -/
theorem irreducibleSpace_of_isOpen_isIrreducible_nhds
    {X : Type*} [TopologicalSpace X] [ConnectedSpace X]
    (hloc : ∀ x : X, ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ IsIrreducible U) :
    IrreducibleSpace X := by
  obtain ⟨x₀⟩ := (inferInstance : Nonempty X)
  have key : ∀ y ∈ irreducibleComponent x₀,
      ∃ U : Set X, IsOpen U ∧ y ∈ U ∧ U ⊆ irreducibleComponent x₀ := by
    intro y hy
    obtain ⟨U, hUo, hyU, hUirr⟩ := hloc y
    refine ⟨U, hUo, hyU, ?_⟩
    have hZsub : irreducibleComponent x₀ ⊆ _root_.closure U := by
      intro z hz
      by_contra hzn
      obtain ⟨w, -, hwU, hwc⟩ :=
        (isIrreducible_irreducibleComponent (x := x₀)).2 U (_root_.closure U)ᶜ hUo
          isClosed_closure.isOpen_compl ⟨y, hy, hyU⟩ ⟨z, hz, hzn⟩
      exact hwc (subset_closure hwU)
    have heq : _root_.closure U = irreducibleComponent x₀ :=
      eq_irreducibleComponent (hUirr.isPreirreducible.closure) hZsub
    exact heq ▸ subset_closure
  have hZopen : IsOpen (irreducibleComponent x₀) := by
    rw [isOpen_iff_forall_mem_open]
    intro y hy
    obtain ⟨U, hUo, hyU, hUZ⟩ := key y hy
    exact ⟨U, hUZ, hUo, hyU⟩
  have hZuniv : irreducibleComponent x₀ = Set.univ :=
    IsClopen.eq_univ ⟨isClosed_irreducibleComponent, hZopen⟩ ⟨x₀, mem_irreducibleComponent⟩
  rw [irreducibleSpace_def, Set.top_eq_univ, ← hZuniv]
  exact isIrreducible_irreducibleComponent

/-- **A PRIME WHOSE LOCALIZATION IS A DOMAIN HAS AN IRREDUCIBLE OPEN NEIGHBOURHOOD IN
`Spec R`** (PROVEN — pure commutative algebra, no scheme theory and no smoothness).

`R_p` is a domain, so `⊥` is its least prime and `IsLocalization.AtPrime.orderIsoOfPrime`
carries that to a LEAST prime `q ≤ p` of `R`, which is therefore the unique minimal prime
below `p`.  Noetherianity makes `minimalPrimes R` finite, so
`U := Spec R ∖ ⋃ {V(q') : q' ∈ minimalPrimes R, q' ≠ q}` is open; `p ∈ U` by that
uniqueness, and every prime contains some minimal prime, so `U ⊆ V(q)`, which is irreducible
because `q` is prime.

Both hypotheses are needed: without noetherianity there can be infinitely many minimal
primes and `U` is not open; without the domain hypothesis `p` may lie on several components
and then no neighbourhood of it is irreducible. -/
theorem exists_isOpen_isIrreducible_of_isDomain_localization {R : Type u} [CommRing R]
    [IsNoetherianRing R] (p : PrimeSpectrum R)
    (hp : IsDomain (Localization.AtPrime p.asIdeal)) :
    ∃ U : Set (PrimeSpectrum R), IsOpen U ∧ p ∈ U ∧ IsIrreducible U := by
  classical
  haveI : p.asIdeal.IsPrime := p.isPrime
  have hbot : (⊥ : Ideal (Localization.AtPrime p.asIdeal)).IsPrime := Ideal.isPrime_bot
  set e := IsLocalization.AtPrime.orderIsoOfPrime (Localization.AtPrime p.asIdeal) p.asIdeal
    with he
  set q : Ideal R := (e ⟨⊥, hbot⟩).1 with hqdef
  have hq : q.IsPrime := (e ⟨⊥, hbot⟩).2.1
  have hleast : ∀ r : Ideal R, r.IsPrime → r ≤ p.asIdeal → q ≤ r := by
    intro r hr hrle
    have h1 : (⟨⊥, hbot⟩ : {P : Ideal (Localization.AtPrime p.asIdeal) // P.IsPrime}) ≤
        e.symm ⟨r, hr, hrle⟩ := Subtype.mk_le_mk.mpr bot_le
    have h2 := e.monotone h1
    rw [e.apply_symm_apply] at h2
    exact h2
  have huniq : ∀ r ∈ minimalPrimes R, r ≤ p.asIdeal → r = q := by
    intro r hr hrle
    have hr' := (IsMinimalPrime.iff_minimal r).mp hr
    have h1 : q ≤ r := hleast r hr'.1 hrle
    exact le_antisymm (hr'.2 hq h1) h1
  set S : Set (Ideal R) := minimalPrimes R \ {q} with hSdef
  have hSfin : S.Finite := (minimalPrimes.finite_of_isNoetherianRing R).subset Set.sdiff_subset
  set U : Set (PrimeSpectrum R) := (⋃ r ∈ S, PrimeSpectrum.zeroLocus (r : Set R))ᶜ with hUdef
  have hUopen : IsOpen U :=
    (hSfin.isClosed_biUnion fun r _ => PrimeSpectrum.isClosed_zeroLocus _).isOpen_compl
  have hpU : p ∈ U := by
    simp only [hUdef, Set.mem_compl_iff, Set.mem_iUnion, not_exists, exists_prop, not_and]
    intro r hrS hpz
    exact hrS.2 (huniq r hrS.1 (PrimeSpectrum.mem_zeroLocus _ _ |>.mp hpz))
  have hUsub : U ⊆ PrimeSpectrum.zeroLocus (q : Set R) := by
    intro x hx
    obtain ⟨r, hrmin, hrle⟩ :=
      Ideal.exists_minimalPrimes_le (I := (⊥ : Ideal R)) (J := x.asIdeal) bot_le
    have hrq : r = q := by
      by_contra hne
      refine hx ?_
      simp only [Set.mem_iUnion, exists_prop]
      exact ⟨r, ⟨hrmin, hne⟩, (PrimeSpectrum.mem_zeroLocus _ _).mpr hrle⟩
    exact (PrimeSpectrum.mem_zeroLocus _ _).mpr (hrq ▸ hrle)
  have hqrad : q.radical.IsPrime := by rw [hq.radical]; exact hq
  have hirr : IsIrreducible (PrimeSpectrum.zeroLocus (q : Set R)) :=
    (PrimeSpectrum.isIrreducible_zeroLocus_iff q).mpr hqrad
  exact ⟨U, hUopen, hpU,
    hirr.isPreirreducible.subset_irreducible ⟨p, hpU⟩ hUopen (subset_refl U) hUsub⟩

namespace AlgebraicGeometry

/-- **A POINT WITH DOMAIN STALK ON A LOCALLY NOETHERIAN SCHEME HAS AN IRREDUCIBLE OPEN
NEIGHBOURHOOD** (PROVEN over the affine statement above).

The transport is done on an affine CHART rather than an affine open:
`Scheme.exists_Spec_apply_eq` produces an open immersion `f : Spec R ⟶ Z` hitting `z`, which
is cheaper to work with than `IsAffineOpen.isoSpec` because it moves both the noetherian
hypothesis and the stalk across in one step and leaves no subtype coercions behind.
`Spec.stalkIso` identifies the stalk of `Spec R` at `y` with `Localization.AtPrime y.asIdeal`,
and the image of an irreducible open under an open embedding is an irreducible open. -/
theorem exists_isOpen_isIrreducible_nhds_of_isDomain_stalk {Z : Scheme.{u}}
    [IsLocallyNoetherian Z] (z : Z) (hz : IsDomain (Z.presheaf.stalk z)) :
    ∃ U : Set Z, IsOpen U ∧ z ∈ U ∧ IsIrreducible U := by
  obtain ⟨R, f, hf, y, hy⟩ := Scheme.exists_Spec_apply_eq (X := Z) z
  haveI := hf
  haveI : IsLocallyNoetherian (Spec R) := isLocallyNoetherian_of_isOpenImmersion f
  haveI : IsNoetherianRing R := isLocallyNoetherian_Spec.mp inferInstance
  subst hy
  haveI : IsDomain ((Spec R).presheaf.stalk y) :=
    (asIso (f.stalkMap y)).symm.commRingCatIsoToRingEquiv.toMulEquiv.isDomain _
  haveI : IsDomain (Localization.AtPrime y.asIdeal) :=
    (Spec.stalkIso R y).symm.commRingCatIsoToRingEquiv.toMulEquiv.isDomain _
  obtain ⟨U, hUopen, hyU, hUirr⟩ := exists_isOpen_isIrreducible_of_isDomain_localization y
    inferInstance
  refine ⟨f.base '' U, ?_, ⟨y, hyU, rfl⟩, ?_⟩
  · exact f.isOpenEmbedding.isOpenMap _ hUopen
  · exact hUirr.image _ f.continuous.continuousOn

end AlgebraicGeometry
