/-
Copyright (c) 2026 Deyao Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.RingTheory.Ideal.MinimalPrime.Localization
public import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Spectrum.Prime.Topology

/-!
# Connected + locally irreducible ⟹ irreducible

Three lemmas — one of point-set topology, one of commutative algebra, one of
scheme theory — which together say:

> a CONNECTED, locally noetherian scheme all of whose stalks are DOMAINS is
> IRREDUCIBLE.

Nothing here is new.  This module exists purely to hold ONE copy of an argument
that this development had independently written **three** times:

* `Fermat/FLT/Modularity/MoretBailly.lean`, as
  `irreducibleSpace_of_connectedSpace_of_locallyIrreducible`,
  `exists_isOpen_isIrreducible_primeSpectrum` and
  `exists_isOpen_isIrreducible_of_isDomain_stalk` (2026-07-26);
* `Fermat/FLT/Modularity/AbelianSchemeIsogeny.lean`, as the four-lemma
  minimum-generalization chain ending in
  `irreducibleSpace_of_connected_of_isDomain_stalk` (2026-07-27) — an
  independent proof of the same theorem, written because `MoretBailly.lean` is
  strictly DOWNSTREAM of that file and so could not be consumed from it;
* `Fermat/FLT/Mathlib/AlgebraicGeometry/CurveExtension.lean`, as
  `irreducibleSpace_of_isOpen_isIrreducible_nhds` and two siblings, written
  because `MoretBailly.lean` is a 34 000-line module whose import cone reaches
  the Deformations and automorphic-form subtrees while `CurveExtension.lean`'s
  entire `Fermat` cone is two modules.

That last note is the one this module answers: it ends "**if those three are
ever hoisted into `Fermat/FLT/Mathlib/`, delete this block and import them
instead**".  The imports above are `Mathlib` only, so this module is reachable
from every one of the three sites at a cone cost of six mathlib files.

## The declarations, and the namespace

The three declarations are moved here VERBATIM from `MoretBailly.lean`, in the
same namespace `GaloisRepresentation.Modularity`, so every existing reference
resolves unchanged through the `public import` — the same treatment, and for the
same reason, as the earlier hoist into `Fermat/FLT/Modularity/RegularStalks.lean`.
The namespace is a project namespace rather than `AlgebraicGeometry` only
because keeping it is what makes the move a no-op for consumers; the statements
themselves are general mathematics and would be at home in mathlib.

* `irreducibleSpace_of_connectedSpace_of_locallyIrreducible` — pure point-set
  topology, no schemes and no noetherian hypothesis.
* `exists_isOpen_isIrreducible_primeSpectrum` — the affine heart: over a
  noetherian ring, a prime with domain localization has an irreducible open
  neighbourhood in `Spec R`.
* `exists_isOpen_isIrreducible_of_isDomain_stalk` — the transport of the
  previous one to a locally noetherian scheme, along an affine chart.

The composite ("connected + locally noetherian + domain stalks ⟹ irreducible")
is stated downstream, as
`GaloisRepresentation.Modularity.irreducibleSpace_of_connected_of_isDomain_stalk`
in `Fermat/FLT/Modularity/AbelianSchemeIsogeny.lean`, which is now a two-line
composition of the first and third lemmas here.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

namespace GaloisRepresentation.Modularity

universe u

/-- **CONNECTED + LOCALLY IRREDUCIBLE ⟹ IRREDUCIBLE** (**PROVEN 2026-07-26** —
pure point-set topology, no scheme theory and no noetherian hypothesis).

If every point of a connected space has an irreducible OPEN neighbourhood then
the whole space is irreducible.

THE PROOF, and why the hypothesis has to be an OPEN neighbourhood.  Fix `x₀`
and let `Z = irreducibleComponent x₀`.  For `y ∈ Z` pick an irreducible open
`U ∋ y`.  Then `U ∩ Z ≠ ∅`, and `Z` is irreducible, so no open set can separate
`U` from `Z`: `Z ⊆ closure U`.  Since `closure U` is irreducible and `Z` is a
MAXIMAL irreducible set, `closure U = Z`, whence `U ⊆ Z`.  So `Z` is a union of
open sets, i.e. open; it is also closed (components are), and nonempty; a
connected space has no proper nonempty clopen subset, so `Z = univ` and the
space is irreducible.

The openness is load-bearing and the statement is FALSE with "irreducible
neighbourhood" weakened to "irreducible subset containing the point": two
lines crossing at the origin form a connected space in which every point lies
on an irreducible subset (one of the lines) but which is reducible.  What fails
there is exactly the step above — the origin has no irreducible *open*
neighbourhood, since every open neighbourhood meets both lines. -/
theorem irreducibleSpace_of_connectedSpace_of_locallyIrreducible
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

/-- **A PRIME WITH DOMAIN LOCALIZATION HAS AN IRREDUCIBLE OPEN NEIGHBOURHOOD
IN `Spec R`** (**PROVEN 2026-07-26** — the affine heart of the
connected ⟹ irreducible upgrade; pure commutative algebra, no scheme theory
and no smoothness).

If `R` is noetherian and `R_p` is a domain then `p` has an irreducible open
neighbourhood in `Spec R`.  Both hypotheses are needed: without noetherianity
there can be infinitely many minimal primes and the neighbourhood below is
not open; without the domain hypothesis `p` may lie on several components,
and then no neighbourhood of it is irreducible.

THE PROOF.  `R_p` is a domain, so `⊥` is its least prime; the order
isomorphism `IsLocalization.AtPrime.orderIsoOfPrime` carries the primes of
`R_p` onto the primes of `R` below `p`, so there is a LEAST prime `q ≤ p`,
and it is the unique minimal prime of `R` below `p`.  Noetherianity makes
`minimalPrimes R` finite, so
`U := Spec R ∖ ⋃ {V(q') : q' ∈ minimalPrimes R, q' ≠ q}` is open; `p ∈ U` by
that uniqueness, and every prime contains some minimal prime, so a prime in
`U` contains `q`, i.e. `U ⊆ V(q)`.  Finally `V(q)` is irreducible because `q`
is prime, and a nonempty open subset of an irreducible set is irreducible. -/
theorem exists_isOpen_isIrreducible_primeSpectrum {R : Type u} [CommRing R]
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
  have hqle : q ≤ p.asIdeal := (e ⟨⊥, hbot⟩).2.2
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

open CategoryTheory AlgebraicGeometry in
/-- **A POINT WITH DOMAIN STALK ON A LOCALLY NOETHERIAN SCHEME HAS AN
IRREDUCIBLE OPEN NEIGHBOURHOOD** (**PROVEN 2026-07-26** over
`exists_isOpen_isIrreducible_primeSpectrum` — elementary, and entirely
independent of smoothness).

The transport is done on an affine CHART rather than an affine open:
`Scheme.exists_Spec_apply_eq` produces an open immersion
`f : Spec R ⟶ Z` hitting `z`, which is cheaper to work with than
`IsAffineOpen.isoSpec` because it moves both the noetherian hypothesis and
the stalk across in one step and leaves no subtype coercions behind.

* `R` is noetherian: `isLocallyNoetherian_of_isOpenImmersion` transports
  `IsLocallyNoetherian` along `f`, and `isLocallyNoetherian_Spec` reads it
  off as `IsNoetherianRing R`.
* `R_y` is a domain: `f.stalkMap y` is an isomorphism because `f` is an open
  immersion, and `Spec.stalkIso` identifies the stalk of `Spec R` at `y` with
  `Localization.AtPrime y.asIdeal`; `MulEquiv.isDomain` moves the hypothesis
  across both.
* The open irreducible neighbourhood is then produced in `Spec R` by the
  affine lemma and pushed forward along `f.base`, which is an open embedding,
  so the image is open (`IsOpenMap`) and still irreducible
  (`IsIrreducible.image`). -/
theorem exists_isOpen_isIrreducible_of_isDomain_stalk {Z : AlgebraicGeometry.Scheme.{u}}
    [AlgebraicGeometry.IsLocallyNoetherian Z] (z : Z)
    (hz : IsDomain (Z.presheaf.stalk z)) :
    ∃ U : Set Z, IsOpen U ∧ z ∈ U ∧ IsIrreducible U := by
  obtain ⟨R, f, hf, y, hy⟩ := AlgebraicGeometry.Scheme.exists_Spec_apply_eq (X := Z) z
  haveI := hf
  haveI : AlgebraicGeometry.IsLocallyNoetherian (AlgebraicGeometry.Spec R) :=
    AlgebraicGeometry.isLocallyNoetherian_of_isOpenImmersion f
  haveI : IsNoetherianRing R := AlgebraicGeometry.isLocallyNoetherian_Spec.mp inferInstance
  subst hy
  haveI : IsDomain ((AlgebraicGeometry.Spec R).presheaf.stalk y) :=
    (asIso (f.stalkMap y)).symm.commRingCatIsoToRingEquiv.toMulEquiv.isDomain _
  haveI : IsDomain (Localization.AtPrime y.asIdeal) :=
    (AlgebraicGeometry.Spec.stalkIso R y).symm.commRingCatIsoToRingEquiv.toMulEquiv.isDomain _
  obtain ⟨U, hUopen, hyU, hUirr⟩ := exists_isOpen_isIrreducible_primeSpectrum y inferInstance
  refine ⟨f.base '' U, ?_, ⟨y, hyU, rfl⟩, ?_⟩
  · exact f.isOpenEmbedding.isOpenMap _ hUopen
  · exact hUirr.image _ f.continuous.continuousOn

end GaloisRepresentation.Modularity
