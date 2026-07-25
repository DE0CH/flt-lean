/-
GaloisRepresentation/HardlyRamified/ProfiniteLocalNoetherian.lean — own
work for the Fermat project (not vendored from the FLT project).

# A profinite local ring with finitely many points in each finite test ring
# is Noetherian, and its topology is the maximal-adic one

This module isolates, as pure commutative algebra, the FINITENESS half of
the deformation-theoretic core
`exists_isStrictlyUniversalOnFrames_of_deformationCondition`
(`Deformation.lean`): the step that upgrades the pro-object of the hardly
ramified deformation problem — which the Schlessinger construction
delivers as a mere PROFINITE local ring, an inverse limit of finite
levels — into an object of Mazur's category, i.e. a NOETHERIAN local ring
carrying the `𝔪`-adic topology and adically complete.

> Let `R` be a compact Hausdorff topological local `ℤ_ℓ`-algebra whose
> open ideals form a neighbourhood basis of `0`, with residue field the
> finite field `k` (a continuous surjection `π : R ↠ k`). Suppose that
> for EVERY finite local `ℤ_ℓ`-algebra `A` and every `πA : A →+* k` the
> set of continuous `ℤ_ℓ`-algebra maps `R → A` lifting `π` is FINITE.
> Then `R` is Noetherian, its topology is the `𝔪`-adic one, and it is
> `𝔪`-adically complete.

This is Mazur's `Φ_ℓ`-finiteness criterion (*Deforming Galois
representations*, MSRI Publ. 16 (1989), §1.2) in abstract form, or
equivalently the Noetherian clause of Schlessinger's Theorem 2.11
(*Functors of Artin rings*, Trans. AMS 130 (1968)): a pro-object of the
category of Artinian local rings is a genuine Noetherian complete local
ring exactly when its tangent space is finite dimensional. It is stated
here with the tangent space replaced by the (equivalent, and
arithmetically usable) hypothesis that `R` has only finitely many
continuous points in every finite test ring, because that is the form the
deformation-theoretic consumer can supply directly: there the points of
`R` in `A` inject into the hardly ramified framed representations over
`A`, of which there are finitely many by the restricted-ramification
finiteness leaf.

**Why the statement is not vacuous, and why the hypothesis is needed.**
A profinite local ring need NOT be Noetherian: take
`R = 𝔽_ℓ ⊕ ∏_{i ∈ ℕ} 𝔽_ℓ · x_i` with `x_i x_j = 0`, a compact local ring
with square-zero maximal ideal. Its continuous points in the dual numbers
`k[ε]` are the continuous `k`-functionals on `∏_{i} 𝔽_ℓ`, i.e. the
finitely supported ones — infinitely many, so the hypothesis fails, as it
must.

## The intended route (no power series, no Witt vectors)

1. **`𝔪` is open and `R ⧸ I` is finite for every open ideal `I`.**
   `𝔪 = ker π` because `π` is a surjection onto a field and `R` is local;
   `π` is continuous and `k` is discrete, so `𝔪` is open. An open ideal
   has discrete quotient (`QuotientRing.isOpenQuotientMap_mk`), and the
   quotient of a compact space is compact, so `R ⧸ I` is finite
   (`finite_of_compact_of_discrete`).
2. **Every open ideal contains a power of `𝔪`.** `R ⧸ I` is a finite
   local ring, so its maximal ideal is nilpotent (Artinian
   Jacobson-radical nilpotence — `Deformation.lean`'s
   `exists_maximalIdeal_pow_eq_bot`, restated here rather than imported,
   this module being upstream of that file), and `𝔪` maps into it.
3. **The cotangent space is finite dimensional.** Write `N` for the
   closure of `𝔪 ^ 2 + ℓ • R` (note `ℓ ∈ 𝔪`, `k` having characteristic
   `ℓ`) and `t = 𝔪 ⧸ N`, a profinite `k`-vector space. Because `k` is
   FINITE, hence perfect and monogenic, the complete local ring `R ⧸ N`
   contains a coefficient field: lift a generator of `kˣ` to a
   `(|k| − 1)`-st root of unity by Hensel's lemma (the same elementary
   route `Deformation.lean`'s `exists_coefficientRing_ringHom` takes, and
   the reason no Witt vectors are needed). Hence continuous
   `ℤ_ℓ`-algebra maps `R → k[ε]` lifting `π` correspond bijectively to
   continuous `k`-linear functionals on `t`. A profinite `k`-vector space
   with only finitely many continuous functionals is finite dimensional —
   an infinite dimensional one, being the inverse limit of its finite
   dimensional discrete quotients, has infinitely many. So `hhom` applied
   at `A = k[ε]` bounds `dim_k t`.
4. **`𝔪` is finitely generated.** Lift a `k`-basis of `t` to
   `x₁, …, x_g ∈ 𝔪`; topological Nakayama in the compact ring `R`
   (successive approximation, converging by compactness plus
   Hausdorffness) gives `𝔪 = (x₁, …, x_g)`.
5. **`IsAdic` and `IsAdicComplete`.** With `𝔪` finitely generated and
   open, every `𝔪 ^ n` is open, and by step 2 every open ideal contains
   some `𝔪 ^ n`: the two families are cofinal, so the given topology IS
   the `𝔪`-adic one. A compact Hausdorff topological group is complete,
   and separatedness is Hausdorffness, so `R` is `𝔪`-adically complete.
6. **Noetherian.**
   `CompleteLocalNoetherian.isNoetherianRing_of_isAdicComplete_of_fg`
   (Stacks 05GH / Matsumura Thm 8.4, proven in this project) turns steps
   4 and 5 into Noetherianity.

Only step 3 has genuine content beyond bookkeeping; it is where the
hypothesis is consumed, and it is the reason the module needs a finite
residue field rather than an arbitrary one.

## The two leaves

The route above is cut in two, along the seam between the FINITENESS
argument (steps 3–4, which is where the hypothesis `hhom` is spent, and
the only place the residue field has to be finite) and the TOPOLOGY
(steps 1, 2, 5, which hold for any profinite local ring with finitely
generated maximal ideal):

* `fg_maximalIdeal_of_finite_ringHom` — the maximal ideal is finitely
  generated (SORRY, the only open node of this module);
* `isAdic_isAdicComplete_of_isOpen_of_fg` — a profinite local ring whose
  maximal ideal is open and finitely generated carries the `𝔪`-adic
  topology and is `𝔪`-adically complete (PROVEN 2026-07-26, steps 1, 2
  and 5 above).

The main theorem is proven over them: it identifies `𝔪` with `ker π`,
which is open because `π` is continuous and `k` is discrete, and then
applies `CompleteLocalNoetherian.isNoetherianRing_of_isAdicComplete_of_fg`.
-/
module

public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology
public import Mathlib.NumberTheory.Padics.PadicIntegers
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
public import Mathlib.RingTheory.Noetherian.Basic
-- proof-only: `ker π` is a maximal ideal when `π` is onto a field.
import Mathlib.RingTheory.Ideal.Quotient.Operations
-- proof-only: the quotient topology on `R ⧸ I` and the openness of the
-- quotient map, from which an open ideal is shown to have finite quotient.
import Mathlib.Topology.Algebra.Ring.Ideal
-- proof-only: `Ideal.finite_quotient_pow` — finiteness of `R ⧸ 𝔪 ^ n` from
-- finiteness of `R ⧸ 𝔪` for a finitely generated `𝔪`.
import Mathlib.RingTheory.Ideal.Quotient.Index
-- proof-only: `Ideal.FG.pow` — a power of a finitely generated ideal is
-- finitely generated.
import Mathlib.RingTheory.Finiteness.Ideal
-- proof-only: `Ideal.isCompact_of_fg` — a finitely generated ideal of a
-- compact topological ring is compact, hence closed.
import Mathlib.Topology.Algebra.Module.Compact
-- proof-only: `AddSubgroup.isOpen_of_isClosed_of_finiteIndex`.
import Mathlib.Topology.Algebra.Group.ClosedSubgroup
-- proof-only: nilpotence of the Jacobson radical of an Artinian ring, which
-- is what makes the maximal ideal of a FINITE local quotient nilpotent.
import Mathlib.RingTheory.Artinian.Ring
-- proof-only: `isLocalHom_of_le_jacobson_bot`.
import Mathlib.RingTheory.LocalRing.RingHom.Basic
-- proof-only: `isLocalHom_of_le_jacobson_bot`, used to see the maximal ideal
-- of `R` inside that of a finite local quotient.
import Mathlib.RingTheory.Henselian
-- proof-only: the Noetherianity criterion this module's last step applies.
import Fermat.FLT.GaloisRepresentation.HardlyRamified.CompleteLocalNoetherian

@[expose] public section

namespace ProfiniteLocalNoetherian

universe u

/-- **The maximal ideal of a profinite local ring with finitely many points
in every finite test ring is finitely generated** (sorry node — the
FINITENESS half of this module's cut, steps 3–4 of the header route, and
the only place where the residue field must be finite).

The tangent space of `R` is the space of continuous `k`-linear functionals
on `𝔪 ⧸ closure (𝔪 ^ 2 + ℓ • R)`; because `k` is finite, hence perfect and
monogenic, `R` modulo that ideal contains a coefficient field (lift a
generator of `kˣ` to a `(|k| − 1)`-st root of unity by Hensel — this is the
elementary route `Deformation.lean`'s `exists_coefficientRing_ringHom`
takes, and the reason no Witt vectors are needed), so those functionals are
exactly the continuous `ℤ_ℓ`-algebra maps `R → k[ε]` lifting `π`. `hhom` at
`A = k[ε]` makes them finitely many, so the cotangent space is finite
dimensional — a profinite `k`-vector space with only finitely many
continuous functionals is, being the inverse limit of its finite
dimensional discrete quotients, finite dimensional. Lifting a basis and
running topological Nakayama in the compact ring `R` (successive
approximation, converging by compactness and Hausdorffness) finishes.

This is the exact point at which Mazur's `Φ_ℓ` condition is consumed; the
counterexample in the module header (a compact local ring with square-zero
maximal ideal `∏_{i ∈ ℕ} 𝔽_ℓ`) shows the hypothesis cannot be dropped.

`hhom` QUANTIFIES ONLY OVER DISCRETE TEST RINGS (`[DiscreteTopology A]`,
added 2026-07-26 in alignment with `Deformation.lean`'s
`exists_isStrictlyUniversalOnFrames_of_deformationCondition`, whose `hfin`
carries the same binder). This costs the prover nothing: `hhom` is spent at
`A = k[ε]` with `k` FINITE, and a finite topological ring in the Mazur
category is discrete, so the instance is available at the only point of use.
The narrowing is mathematically necessary rather than cosmetic — over a
finite ring carrying the INDISCRETE topology, continuity of `φ` is no
constraint at all and the finiteness hypothesis would be asserting something
false about the abstract (non-topological) point set. -/
theorem fg_maximalIdeal_of_finite_ringHom
    {ℓ : ℕ} [Fact ℓ.Prime] {k : Type u} [Field k] [Finite k]
    [Algebra ℤ_[ℓ] k] [TopologicalSpace k] [DiscreteTopology k]
    {R : Type u} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    [IsLocalRing R] [Algebra ℤ_[ℓ] R] [CompactSpace R] [T2Space R]
    (hbasis : ∀ U ∈ nhds (0 : R), ∃ I : Ideal R, IsOpen (I : Set R) ∧
      (I : Set R) ⊆ U)
    (π : R →+* k) (hπsurj : Function.Surjective π) (hπcont : Continuous π)
    (hhom : ∀ (A : Type u) [CommRing A] [TopologicalSpace A]
      [IsTopologicalRing A] [IsLocalRing A] [Algebra ℤ_[ℓ] A] [Finite A]
      [DiscreteTopology A]
      (πA : A →+* k),
      {φ : R →+* A | Continuous φ ∧ πA.comp φ = π ∧
        φ.comp (algebraMap ℤ_[ℓ] R) = algebraMap ℤ_[ℓ] A}.Finite) :
    (IsLocalRing.maximalIdeal R).FG :=
  sorry

/-- **A profinite local ring whose maximal ideal is open and finitely
generated carries the `𝔪`-adic topology and is `𝔪`-adically complete**
(PROVEN 2026-07-26 — the TOPOLOGY half of this module's cut, steps 1, 2
and 5 of the header route; no arithmetic, and no finiteness of the residue
field).

`IsAdic`: the powers `𝔪 ^ n` and the open ideals are cofinal in each
other. Downwards, every open ideal `I ≠ ⊤` contains some `𝔪 ^ n`, because
`R ⧸ I` is compact and discrete, hence a FINITE local ring, hence has
nilpotent maximal ideal (Artinian Jacobson-radical nilpotence), and `𝔪`
maps into it. Upwards, `𝔪 ^ n` is CLOSED, being finitely generated hence
the image of a compact `R ^ g` under a continuous map
(`Ideal.isCompact_of_fg`), and of FINITE INDEX, `R ⧸ 𝔪 ^ n` being finite
by `Ideal.finite_quotient_pow` over the finite `R ⧸ 𝔪`; a closed subgroup
of finite index is open (`AddSubgroup.isOpen_of_isClosed_of_finiteIndex`).
This is the same route mathlib takes for compact Hausdorff NOETHERIAN
rings in `Ideal.isOpen_pow_of_isMaximal`, with finite generation of `𝔪`
in place of the Noetherian hypothesis that is not yet available here.

`IsAdicComplete`: with the topology identified as the `𝔪`-adic one,
Hausdorffness gives `IsHausdorff` (adic separatedness) and compactness
gives `IsPrecomplete` — a compact Hausdorff topological group is a
complete uniform space, and a compatible sequence of cosets of the
`𝔪 ^ n` has the finite intersection property, so it has a limit. -/
theorem isAdic_isAdicComplete_of_isOpen_of_fg
    {R : Type u} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    [IsLocalRing R] [CompactSpace R] [T2Space R]
    (hbasis : ∀ U ∈ nhds (0 : R), ∃ I : Ideal R, IsOpen (I : Set R) ∧
      (I : Set R) ⊆ U)
    (hopen : IsOpen ((IsLocalRing.maximalIdeal R : Ideal R) : Set R))
    (hfg : (IsLocalRing.maximalIdeal R).FG) :
    IsAdic (IsLocalRing.maximalIdeal R) ∧
      IsAdicComplete (IsLocalRing.maximalIdeal R) R := by
  classical
  set 𝔪 : Ideal R := IsLocalRing.maximalIdeal R with h𝔪
  -- An ideal of `R`, seen as a submodule, is its own multiple by the top module.
  have hst : ∀ J : Ideal R, J • (⊤ : Submodule R R) = J := fun J => by
    rw [Ideal.smul_eq_mul, Ideal.mul_top]
  -- **An open ideal has finite quotient**: the quotient is discrete (the
  -- quotient map is open) and compact.
  have hfinq : ∀ I : Ideal R, IsOpen (I : Set R) → Finite (R ⧸ I) := by
    intro I hI
    haveI : DiscreteTopology (R ⧸ I) := by
      rw [discreteTopology_iff_isOpen_singleton_zero]
      have hz : ({0} : Set (R ⧸ I)) = Ideal.Quotient.mk I '' (I : Set R) := by
        ext x
        constructor
        · rintro rfl
          exact ⟨0, I.zero_mem, map_zero _⟩
        · rintro ⟨y, hy, rfl⟩
          exact (Ideal.Quotient.eq_zero_iff_mem).mpr hy
      rw [hz]
      exact (QuotientRing.isOpenQuotientMap_mk I).isOpenMap _ hI
    exact finite_of_compact_of_discrete
  haveI : Finite (R ⧸ 𝔪) := hfinq 𝔪 hopen
  -- **Every power of `𝔪` is open**: it is finitely generated, hence compact,
  -- hence closed, and `R ⧸ 𝔪 ^ n` is finite, so it has finite index.
  have hpowopen : ∀ n : ℕ, IsOpen ((𝔪 ^ n : Ideal R) : Set R) := by
    intro n
    haveI : Finite (R ⧸ 𝔪 ^ n) := Ideal.finite_quotient_pow hfg n
    have hcl : IsClosed ((𝔪 ^ n : Ideal R) : Set R) :=
      (Ideal.isCompact_of_fg (Ideal.FG.pow (n := n) hfg)).isClosed
    haveI : (𝔪 ^ n : Ideal R).toAddSubgroup.FiniteIndex :=
      @AddSubgroup.finiteIndex_of_finite_quotient _ _ _
        (inferInstanceAs (Finite (R ⧸ (𝔪 ^ n : Ideal R))))
    exact (𝔪 ^ n : Ideal R).toAddSubgroup.isOpen_of_isClosed_of_finiteIndex hcl
  -- **Every open ideal contains a power of `𝔪`**: its quotient is a FINITE
  -- local ring, whose maximal ideal is therefore nilpotent.
  have hple : ∀ I : Ideal R, IsOpen (I : Set R) →
      ∃ n : ℕ, (𝔪 ^ n : Ideal R) ≤ I := by
    intro I hI
    rcases eq_or_ne I ⊤ with rfl | hItop
    · exact ⟨0, le_top⟩
    haveI := hfinq I hI
    haveI : Nontrivial (R ⧸ I) := by
      rw [← not_subsingleton_iff_nontrivial, Ideal.Quotient.subsingleton_iff]
      exact hItop
    haveI : IsLocalHom (Ideal.Quotient.mk I) :=
      isLocalHom_of_le_jacobson_bot I (by
        rw [IsLocalRing.jacobson_eq_maximalIdeal (⊥ : Ideal R) bot_ne_top]
        exact IsLocalRing.le_maximalIdeal hItop)
    haveI : IsLocalRing (R ⧸ I) :=
      IsLocalRing.of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
    haveI : IsArtinianRing (R ⧸ I) := isArtinian_of_finite
    obtain ⟨N, hN⟩ : ∃ N : ℕ, IsLocalRing.maximalIdeal (R ⧸ I) ^ N = ⊥ := by
      obtain ⟨N, hN⟩ := IsArtinianRing.isNilpotent_jacobson_bot (R := R ⧸ I)
      exact ⟨N, by
        rwa [IsLocalRing.jacobson_eq_maximalIdeal (⊥ : Ideal (R ⧸ I)) bot_ne_top,
          Ideal.zero_eq_bot] at hN⟩
    refine ⟨N, ?_⟩
    have hmapmono : (𝔪).map (Ideal.Quotient.mk I) ≤
        IsLocalRing.maximalIdeal (R ⧸ I) := by
      rw [Ideal.map_le_iff_le_comap]
      intro y hy
      show Ideal.Quotient.mk I y ∈ IsLocalRing.maximalIdeal (R ⧸ I)
      rw [IsLocalRing.mem_maximalIdeal] at hy ⊢
      exact fun hu => hy (isUnit_of_map_unit (Ideal.Quotient.mk I) y hu)
    have hmono : ∀ n : ℕ, ((𝔪).map (Ideal.Quotient.mk I)) ^ n ≤
        IsLocalRing.maximalIdeal (R ⧸ I) ^ n := by
      intro n
      induction n with
      | zero => simp
      | succ m ih => rw [pow_succ, pow_succ]; exact Ideal.mul_mono ih hmapmono
    have hpow : ((𝔪) ^ N).map (Ideal.Quotient.mk I) = ⊥ := by
      rw [Ideal.map_pow, ← le_bot_iff, ← hN]
      exact hmono N
    rwa [Ideal.map_eq_bot_iff_le_ker, Ideal.mk_ker] at hpow
  -- **The topology IS the `𝔪`-adic one**: the two families are cofinal.
  have hadic : IsAdic 𝔪 := by
    rw [isAdic_iff]
    refine ⟨hpowopen, fun s hs => ?_⟩
    obtain ⟨I, hIopen, hIs⟩ := hbasis s hs
    obtain ⟨n, hn⟩ := hple I hIopen
    exact ⟨n, fun x hx => hIs (hn hx)⟩
  refine ⟨hadic, ?_⟩
  -- **Adic separatedness** is Hausdorffness: an element inside every `𝔪 ^ n`
  -- lies in every neighbourhood of `0`.
  haveI : IsHausdorff 𝔪 R := by
    constructor
    intro x hx
    by_contra hx0
    obtain ⟨n, hn⟩ := (isAdic_iff.mp hadic).2 ({x}ᶜ)
      (compl_singleton_mem_nhds (Ne.symm hx0))
    have hxmem : x ∈ (𝔪 ^ n : Ideal R) := by
      have h := hx n
      rw [SModEq.sub_mem, hst, sub_zero] at h
      exact h
    exact (hn hxmem) rfl
  -- **Adic precompleteness** is compactness: the cosets `f n + 𝔪 ^ n` are
  -- closed, nonempty and nested, so they have a common point.
  haveI : IsPrecomplete 𝔪 R := by
    constructor
    intro f hf
    set C : ℕ → Set R := fun n => (fun y : R => y - f n) ⁻¹' ((𝔪 ^ n : Ideal R))
      with hC
    have hCclosed : ∀ n, IsClosed (C n) :=
      fun n => IsClosed.preimage (by fun_prop)
        (Ideal.isCompact_of_fg (Ideal.FG.pow (n := n) hfg)).isClosed
    have hanti : ∀ {m n : ℕ}, m ≤ n → C n ⊆ C m := by
      intro m n hmn y hy
      have h1 : y - f n ∈ (𝔪 ^ n : Ideal R) := hy
      have h2 : f m - f n ∈ (𝔪 ^ m : Ideal R) := by
        have h := hf hmn
        rw [SModEq.sub_mem, hst] at h
        exact h
      show y - f m ∈ (𝔪 ^ m : Ideal R)
      have h3 : y - f m = (y - f n) - (f m - f n) := by ring
      rw [h3]
      exact Ideal.sub_mem _ (Ideal.pow_le_pow_right hmn h1) h2
    obtain ⟨L, hL⟩ : (⋂ n, C n).Nonempty := by
      refine IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed C
        (fun m n => ⟨max m n, hanti (le_max_left m n), hanti (le_max_right m n)⟩)
        (fun n => ⟨f n, by simp [hC]⟩)
        (fun n => (hCclosed n).isCompact) hCclosed
    refine ⟨L, fun n => ?_⟩
    rw [SModEq.sub_mem, hst]
    have hLn : L - f n ∈ (𝔪 ^ n : Ideal R) := Set.mem_iInter.mp hL n
    have h4 : f n - L = -(L - f n) := by ring
    rw [h4]
    exact neg_mem hLn
  constructor

/-- **A profinite local ring with finitely many points in every finite test
ring is Noetherian, `𝔪`-adic and `𝔪`-adically complete** (PROVEN
2026-07-26 over the two leaves above and
`CompleteLocalNoetherian.isNoetherianRing_of_isAdicComplete_of_fg`; the
FINITENESS half of the Schlessinger core, isolated the same day as pure
commutative algebra — see this module's header for the full route and for
the counterexample showing the hypothesis cannot be dropped).

`R` is a compact Hausdorff topological local `ℤ_ℓ`-algebra whose open
ideals form a neighbourhood basis of `0` — i.e. a profinite local ring —
with residue field the finite field `k`, and `hhom` says `R` has only
FINITELY many continuous `ℤ_ℓ`-algebra points lifting `π` in each finite
local `ℤ_ℓ`-algebra `A`. The conclusion is the three Mazur-category ring
clauses.

This is Mazur's `Φ_ℓ` criterion / the Noetherian clause of Schlessinger's
Theorem 2.11: what makes a pro-Artinian ring a genuine complete Noetherian
local ring is finiteness of its tangent space, and `hhom` at `A = k[ε]` is
exactly that finiteness.

CONSUMER. `exists_isStrictlyUniversalOnFrames_of_deformationCondition` in
`Deformation.lean`, which supplies `hhom` from the
restricted-ramification finiteness leaf: the continuous points of the
universal ring in `A` inject into the hardly ramified framed
representations over `A` (the injection being the minimality clause of
the hull, the target being finite by H3).

`hhom` QUANTIFIES ONLY OVER DISCRETE TEST RINGS (`[DiscreteTopology A]`,
added 2026-07-26): see `fg_maximalIdeal_of_finite_ringHom` above, which is
where the hypothesis is spent and which carries the identical binder. The
consumer's own `hfin` in `Deformation.lean` carries it too, so the three
statements are now aligned.

References: Mazur, *Deforming Galois representations*, MSRI Publ. 16
(1989), §1.2; Schlessinger, *Functors of Artin rings*, Trans. AMS 130
(1968), Thm 2.11; Stacks 05GH (the Noetherianity criterion, proven in
`CompleteLocalNoetherian.lean`). -/
theorem isNoetherianRing_isAdic_of_profinite_of_finite_ringHom
    {ℓ : ℕ} [Fact ℓ.Prime] {k : Type u} [Field k] [Finite k]
    [Algebra ℤ_[ℓ] k] [TopologicalSpace k] [DiscreteTopology k]
    {R : Type u} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    [IsLocalRing R] [Algebra ℤ_[ℓ] R] [CompactSpace R] [T2Space R]
    (hbasis : ∀ U ∈ nhds (0 : R), ∃ I : Ideal R, IsOpen (I : Set R) ∧
      (I : Set R) ⊆ U)
    (π : R →+* k) (hπsurj : Function.Surjective π) (hπcont : Continuous π)
    (hhom : ∀ (A : Type u) [CommRing A] [TopologicalSpace A]
      [IsTopologicalRing A] [IsLocalRing A] [Algebra ℤ_[ℓ] A] [Finite A]
      [DiscreteTopology A]
      (πA : A →+* k),
      {φ : R →+* A | Continuous φ ∧ πA.comp φ = π ∧
        φ.comp (algebraMap ℤ_[ℓ] R) = algebraMap ℤ_[ℓ] A}.Finite) :
    IsNoetherianRing R ∧ IsAdic (IsLocalRing.maximalIdeal R) ∧
      IsAdicComplete (IsLocalRing.maximalIdeal R) R := by
  -- `𝔪 = ker π`, `π` being a surjection onto a field out of a local ring, and
  -- it is OPEN because `π` is continuous and `k` is discrete.
  have hker : RingHom.ker π = IsLocalRing.maximalIdeal R :=
    IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective π hπsurj)
  have hopen : IsOpen ((IsLocalRing.maximalIdeal R : Ideal R) : Set R) := by
    rw [← hker, show ((RingHom.ker π : Ideal R) : Set R) = π ⁻¹' {0} from
      Set.ext fun x => by simp [RingHom.mem_ker]]
    exact (isOpen_discrete _).preimage hπcont
  have hfg : (IsLocalRing.maximalIdeal R).FG :=
    fg_maximalIdeal_of_finite_ringHom hbasis π hπsurj hπcont hhom
  obtain ⟨hadic, hcomplete⟩ :=
    isAdic_isAdicComplete_of_isOpen_of_fg hbasis hopen hfg
  exact ⟨CompleteLocalNoetherian.isNoetherianRing_of_isAdicComplete_of_fg
    hcomplete hfg, hadic, hcomplete⟩

end ProfiniteLocalNoetherian
