/-
WittVector/Coefficients.lean — own work for the Fermat project.

`W(k)` as a COEFFICIENT RING: the structure needed to use Witt vectors of a
perfect field of characteristic `p` as the base `R` of
`exists_isIdempotentElem_isLocalRing_quotient_of_moduleFinite`
(`Fermat.FLT.Mathlib.RingTheory.AdicCompletion.Finite`), i.e. as a COMPLETE
NOETHERIAN LOCAL ring which is moreover a `ℤ_[p]`-algebra with residue
field `k`.

## Why this file exists

The `W(k)` base-change narrowing recorded under "NARROWINGS IDENTIFIED" in
the docstring of `nonempty_potentialHeckeDatum_of_five_le`
(`HardlyRamified/HilbertModularity.lean`) — "the `W(k)` base change should be
PROVEN, not cited" — needs two halves:

1. the splitting of a module-finite algebra over a complete Noetherian local
   ring into local factors, which is
   `exists_isIdempotentElem_isLocalRing_quotient_of_moduleFinite`; and
2. `W(k)` presented as such a ring, over `ℤ_[p]`.

Half 1 was built on 2026-07-26. This file is half 2.

## STALE-BLOCKER CORRECTION (2026-07-27)

The task that produced this file was dispatched with the claim that mathlib
has "no adic-completeness instance for `W(k)`". **That is false**, and the
check that refutes it is a one-line grep:

    grep -rn 'IsAdicComplete' Mathlib/RingTheory/WittVector/

`WittVector.isAdicCompleteIdealSpanP`
(`Mathlib/RingTheory/WittVector/Complete.lean:116`) gives
`IsAdicComplete (Ideal.span {(p : 𝕎 k)}) (𝕎 k)` for `k` a perfect ring of
characteristic `p`. What is genuinely missing is only the identification of
that ideal with `IsLocalRing.maximalIdeal (𝕎 k)` — which is what
`maximalIdeal_eq_span_p` below supplies, in three lines — and the
`ℤ_[p]`-algebra structure. Noetherianness is likewise free, via
`PrincipalIdealRing.isNoetherianRing` from `WittVector.isDiscreteValuationRing`.

So the genuinely absent item was ONE of the two named in the dispatch, not
both, and it is small. The refuting check for the remaining claim
("no `Algebra ℤ_[p] (WittVector p k)` instance") is

    grep -rn 'PadicInt' Mathlib/RingTheory/WittVector/

which finds only the `𝕎 (ZMod p) ≃+* ℤ_[p]` comparison of
`Mathlib/RingTheory/WittVector/Compare.lean`, and no `Algebra` instance —
so that half of the claim stands, and `instAlgebraPadicInt` below is built
by composing that comparison with functoriality along `ZMod p → k`.
-/
module

public import Mathlib.RingTheory.WittVector.Compare
public import Mathlib.RingTheory.WittVector.Complete
public import Mathlib.RingTheory.WittVector.Teichmuller
public import Mathlib.RingTheory.WittVector.DiscreteValuationRing
public import Mathlib.RingTheory.TensorProduct.Finite
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.RingTheory.Nakayama
public import Fermat.FLT.Mathlib.RingTheory.AdicCompletion.Finite

@[expose] public section

namespace WittVector

/-! ### `W(k)` is a `ℤ_[p]`-algebra

`ℤ_[p] ≃+* 𝕎 (ZMod p)` is `WittVector.equiv`; pushing it forward along
functoriality for the unique ring map `ZMod p → k` of a ring of
characteristic `p` gives `ℤ_[p] → 𝕎 k`. -/

section AlgebraStructure

variable (p : ℕ) [Fact p.Prime] (k : Type*) [CommRing k] [CharP k p]

/-- **The structure map `ℤ_[p] → W(k)`**: the inverse of the comparison
isomorphism `WittVector.equiv : 𝕎 (ZMod p) ≃+* ℤ_[p]`, followed by
functoriality of Witt vectors along `ZMod.castHom : ZMod p →+* k`. -/
noncomputable def ofPadicInt : ℤ_[p] →+* WittVector p k :=
  (WittVector.map (ZMod.castHom (dvd_refl p) k)).comp
    (WittVector.equiv p).symm.toRingHom

/-- **`W(k)` is a `ℤ_[p]`-algebra.** -/
noncomputable instance instAlgebraPadicInt : Algebra ℤ_[p] (WittVector p k) :=
  (ofPadicInt p k).toAlgebra

lemma algebraMap_padicInt_eq : algebraMap ℤ_[p] (WittVector p k) = ofPadicInt p k := rfl

end AlgebraStructure

/-! ### `W(k)` is a complete Noetherian local ring with residue field `k` -/

section PerfectField

variable (p : ℕ) [Fact p.Prime] (k : Type*) [Field k] [CharP k p] [PerfectRing k p]

/-- **The maximal ideal of `W(k)` is `(p)`.** `W(k)` is local because it is a
DVR (`WittVector.isDiscreteValuationRing`), and `Ideal.span {p}` is maximal
because the quotient by it is the field `k` (`WittVector.quotientPEquiv`);
in a local ring a maximal ideal IS the maximal ideal. -/
theorem maximalIdeal_eq_span_p :
    IsLocalRing.maximalIdeal (WittVector p k) = Ideal.span {(p : WittVector p k)} :=
  (IsLocalRing.eq_maximalIdeal
    (Ideal.Quotient.maximal_of_isField _
      (MulEquiv.isField (Field.toIsField k)
        (quotientPEquiv (p := p) (k := k)).toMulEquiv))).symm

/-- **`W(k)` is maximal-adically complete.** This is
`WittVector.isAdicCompleteIdealSpanP` transported along
`maximalIdeal_eq_span_p`; the transport is the whole content, since mathlib
states completeness for `Ideal.span {p}` and every consumer that wants a
coefficient ring asks for the MAXIMAL ideal. -/
instance instIsAdicCompleteMaximalIdeal :
    IsAdicComplete (IsLocalRing.maximalIdeal (WittVector p k)) (WittVector p k) := by
  rw [maximalIdeal_eq_span_p]
  infer_instance

/-- **The residue field of `W(k)` is `k`.** -/
noncomputable def residueFieldEquiv :
    IsLocalRing.ResidueField (WittVector p k) ≃+* k :=
  (Ideal.quotEquivOfEq (maximalIdeal_eq_span_p p k)).trans quotientPEquiv

/-! ### The local factor of a module-finite `W(k)`-algebra

This is the payload: `exists_isIdempotentElem_isLocalRing_quotient_of_moduleFinite`
instantiated at `R = W(k)`, which is legitimate exactly because of the three
instances above (`IsLocalRing` from the DVR structure, `IsNoetherianRing`
from `PrincipalIdealRing.isNoetherianRing`, and `IsAdicComplete` from
`instIsAdicCompleteMaximalIdeal`). -/

/-- **The local factor of a module-finite `W(k)`-algebra at a maximal ideal.**

Given `A` module-finite over `W(k)` and `𝔪` maximal in `A`, there is an
idempotent `e` with `1 - e ∈ 𝔪`, `A ⧸ (1-e)` LOCAL, and
`A ≃ₐ[W(k)] A ⧸ (1-e) × A ⧸ (e)`. -/
theorem exists_isIdempotentElem_isLocalRing_quotient_wittVector
    {A : Type*} [CommRing A] [Algebra (WittVector p k) A]
    [Module.Finite (WittVector p k) A]
    (𝔪 : Ideal A) (h𝔪 : 𝔪.IsMaximal) :
    ∃ e : A, IsIdempotentElem e ∧ 1 - e ∈ 𝔪 ∧
      IsLocalRing (A ⧸ Ideal.span {1 - e}) ∧
      Nonempty (A ≃ₐ[WittVector p k]
        (A ⧸ Ideal.span {1 - e}) × (A ⧸ Ideal.span {e})) :=
  exists_isIdempotentElem_isLocalRing_quotient_of_moduleFinite (WittVector p k) 𝔪 h𝔪

/-- **The local factor of `W(k) ⊗_{ℤ_[p]} 𝕋` at a maximal ideal** — the shape
the Hecke-algebra narrowing actually needs.

`𝕋` is the classical `ℤ_[p]`-Hecke algebra: module-finite over `ℤ_[p]` and
nothing more. Its unramified base change to `W(k)` is module-finite over
`W(k)` by `Module.Finite.base_change`, so the previous theorem applies and
cuts out the local factor at any maximal ideal.

The tensor is written `W(k) ⊗_{ℤ_[p]} 𝕋` rather than `𝕋 ⊗_{ℤ_[p]} W(k)`
purely so that `Module.Finite.base_change` — which is stated for
`TensorProduct R A M` with the base-changed ring `A` on the LEFT — applies as
an instance without a commutation step. The two are isomorphic as
`W(k)`-algebras; nothing mathematical rides on the order. -/
theorem exists_isIdempotentElem_isLocalRing_quotient_baseChange
    (T : Type*) [CommRing T] [Algebra ℤ_[p] T] [Module.Finite ℤ_[p] T]
    (𝔪 : Ideal (TensorProduct ℤ_[p] (WittVector p k) T)) (h𝔪 : 𝔪.IsMaximal) :
    ∃ e : TensorProduct ℤ_[p] (WittVector p k) T,
      IsIdempotentElem e ∧ 1 - e ∈ 𝔪 ∧
      IsLocalRing (TensorProduct ℤ_[p] (WittVector p k) T ⧸ Ideal.span {1 - e}) ∧
      Nonempty (TensorProduct ℤ_[p] (WittVector p k) T ≃ₐ[WittVector p k]
        (TensorProduct ℤ_[p] (WittVector p k) T ⧸ Ideal.span {1 - e}) ×
        (TensorProduct ℤ_[p] (WittVector p k) T ⧸ Ideal.span {e})) :=
  exists_isIdempotentElem_isLocalRing_quotient_wittVector p k 𝔪 h𝔪

end PerfectField

/-! ### `W(k)` over `ℤ_[p]`: injectivity, torsion-freeness, finiteness, Teichmüller generation

Everything above is about `W(k)` as a ring in its own right. The narrowing
also needs `W(k)` as a `ℤ_[p]`-MODULE: module-finite, free, and generated by
Teichmüller roots.

All of it is PROVEN below (2026-07-27), and mathlib still has no statement
about `𝕎 k` as a module over anything — the check that would refute *that*
remains

    grep -rn 'Module.Finite\|Module.Free' Mathlib/RingTheory/WittVector/

which returns nothing. What made the leaves fall was not new Witt-vector
theory but the observation that **complete Nakayama is already packaged in
mathlib** as `surjective_of_mkQ_comp_surjective`
(`Mathlib/RingTheory/AdicCompletion/Functoriality.lean`): if `M` is
`I`-precomplete, `N` is `I`-Hausdorff, and `M → N → N ⧸ I·N` is surjective,
then `M → N` is surjective. Taking `M = k →₀ ℤ_[p]` (finite free, hence
precomplete), `N = 𝕎 k` (Hausdorff, from `isAdicCompleteIdealSpanP`
transported along `map_maximalIdeal_padicInt`) and the map that sends the
basis to the Teichmüller lifts, the mod-`p` surjectivity is just
`x ≡ τ(x.coeff 0) mod p` — i.e. `ker_constantCoeff` — and everything else is
formal. `span_range_teichmuller_eq_top` below is that argument; the two
leaves named in the dispatch are corollaries of it.

The refuting check for "this route is unavailable" is
`grep -rn 'surjective_of_mkQ_comp_surjective' Mathlib/`. The earlier plan
recorded here — Teichmüller SERIES plus a hand-built Cauchy sequence, via
`Mathlib.RingTheory.WittVector.TeichmullerSeries` — would also work, but it
is strictly more machinery: it needs the series to converge in a finitely
generated submodule, which is precomplete for exactly the reason the
packaged lemma already exploits. -/

section PadicIntModule

variable (p : ℕ) [Fact p.Prime] (k : Type*) [Field k] [CharP k p]

/-- **`ℤ_[p] → W(k)` is injective.** Both factors are: the comparison
isomorphism `WittVector.equiv` is bijective, and `WittVector.map` is injective
on an injective coefficient map — here `ZMod p → k`, injective because
`ZMod p` is a field. -/
theorem ofPadicInt_injective : Function.Injective (ofPadicInt p k) := by
  rw [ofPadicInt, RingHom.coe_comp]
  exact (WittVector.map_injective _ (ZMod.castHom (dvd_refl p) k).injective).comp
    (WittVector.equiv p).symm.injective

/-- **`W(k)` is torsion-free over `ℤ_[p]`.** `W(k)` is a domain (`k` is), so a
nonzero scalar acts regularly as soon as its image is nonzero, which is
`ofPadicInt_injective`. With `moduleFinite_padicInt` below this is what makes
`W(k)` FREE over `ℤ_[p]` — via mathlib's
`Module.free_of_finite_type_torsion_free'` over the PID `ℤ_[p]` — so freeness
is NOT a separate leaf. -/
instance instIsTorsionFreePadicInt : Module.IsTorsionFree ℤ_[p] (WittVector p k) :=
  Module.IsTorsionFree.comap (ofPadicInt p k)
    (fun c hc => by
      rw [isRegular_iff_ne_zero] at hc ⊢
      exact fun h => hc (ofPadicInt_injective p k (h.trans (map_zero _).symm)))
    (fun _ _ => rfl)

/-- **The maximal ideal of `ℤ_[p]` extends to `(p)` in `W(k)`.** The structure
map is a ring hom and `p` is a natural-number cast, so it is preserved on the
nose; this is what lets `isAdicCompleteIdealSpanP` — stated for
`Ideal.span {p}` over `𝕎 k` — be read as a statement about the `ℤ_[p]`-adic
filtration. -/
theorem map_maximalIdeal_padicInt :
    (IsLocalRing.maximalIdeal ℤ_[p]).map (algebraMap ℤ_[p] (WittVector p k))
      = Ideal.span {(p : WittVector p k)} := by
  rw [PadicInt.maximalIdeal_eq_span_p, Ideal.map_span, Set.image_singleton, map_natCast]

/-- **The Teichmüller lifts SPAN `W(k)` over `ℤ_[p]`** — the module-theoretic
core from which both of this section's remaining statements follow.

This is complete Nakayama, and the whole proof is an application of mathlib's
`surjective_of_mkQ_comp_surjective` to the `ℤ_[p]`-linear map

    (k →₀ ℤ_[p]) → 𝕎 k,   `Finsupp.single a 1 ↦ τ(a)`.

Its three hypotheses are discharged as follows.

* *`k →₀ ℤ_[p]` is `𝔪`-precomplete*: it is a finite free `ℤ_[p]`-module
  (`k` is finite), so `IsPrecomplete.of_finite_module` applies over the
  complete `ℤ_[p]`.
* *`𝕎 k` is `𝔪`-Hausdorff*: `isAdicCompleteIdealSpanP` gives Hausdorffness
  for `Ideal.span {p}` over `𝕎 k`, and `IsHausdorff.map_algebraMap_iff`
  transports it to the `ℤ_[p]`-adic filtration along
  `map_maximalIdeal_padicInt`.
* *Surjectivity mod `𝔪 · 𝕎 k = (p)*: every `x` is congruent to the
  Teichmüller lift of its own constant coefficient, because
  `constantCoeff (x - τ(constantCoeff x)) = 0` and
  `ker_constantCoeff : RingHom.ker constantCoeff = Ideal.span {p}`.

Perfectness of `k` — required by `isAdicCompleteIdealSpanP` and
`ker_constantCoeff` — is automatic here: a finite field is reduced, so
`PerfectRing.ofFiniteOfIsReduced` supplies it once `ExpChar k p` is in
scope. -/
theorem span_range_teichmuller_eq_top [Finite k] :
    Submodule.span ℤ_[p] (Set.range fun a : k => teichmuller p a) = ⊤ := by
  haveI : ExpChar k p := .prime Fact.out
  haveI : IsHausdorff (IsLocalRing.maximalIdeal ℤ_[p]) (WittVector p k) := by
    refine (IsHausdorff.map_algebraMap_iff (I := IsLocalRing.maximalIdeal ℤ_[p])
      (S := WittVector p k) (M := WittVector p k)).mp ?_
    rw [map_maximalIdeal_padicInt p k]
    infer_instance
  haveI : IsPrecomplete (IsLocalRing.maximalIdeal ℤ_[p]) (k →₀ ℤ_[p]) :=
    IsPrecomplete.of_finite_module _
  have hsurj : Function.Surjective
      (Finsupp.linearCombination ℤ_[p] (fun a : k => teichmuller p a)) := by
    refine surjective_of_mkQ_comp_surjective (I := IsLocalRing.maximalIdeal ℤ_[p]) ?_
    intro y
    obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective _ y
    refine ⟨Finsupp.single (constantCoeff x) 1, ?_⟩
    have hmem : teichmuller p (constantCoeff x) - x ∈
        (IsLocalRing.maximalIdeal ℤ_[p]) • (⊤ : Submodule ℤ_[p] (WittVector p k)) := by
      rw [Ideal.smul_top_eq_map, map_maximalIdeal_padicInt p k]
      simp only [Submodule.restrictScalars_mem]
      rw [← ker_constantCoeff, RingHom.mem_ker, map_sub, sub_eq_zero]
      simp
    simp only [LinearMap.comp_apply, Finsupp.linearCombination_single, one_smul,
      Submodule.mkQ_apply]
    exact (Submodule.Quotient.eq _).mpr hmem
  rw [← Finsupp.range_linearCombination]
  exact LinearMap.range_eq_top.mpr hsurj

/-- **`W(k)` is module-finite over `ℤ_[p]` for `k` a FINITE field.**
Classically `W(k)` is the unramified extension of `ℤ_[p]` of degree
`d = [k : 𝔽_p]`, free of rank `d`.

PROVEN from `span_range_teichmuller_eq_top`: `⊤` is the span of the range of
`teichmuller`, a set that is finite because `k` is, so `⊤` is finitely
generated — which is the definition of `Module.Finite`. Note this gives the
generating set explicitly (the `|k|` Teichmüller lifts) rather than merely
its existence. -/
theorem moduleFinite_padicInt [Finite k] : Module.Finite ℤ_[p] (WittVector p k) := by
  refine ⟨?_⟩
  rw [← span_range_teichmuller_eq_top p k]
  exact Submodule.fg_span (Set.finite_range _)

/-- **`W(k)` is free over `ℤ_[p]`** (for finite `k`) — PROVEN over
`moduleFinite_padicInt`, since `ℤ_[p]` is a PID and `W(k)` is torsion-free.
This is a derivation, not a second leaf. -/
theorem moduleFree_padicInt [Finite k] : Module.Free ℤ_[p] (WittVector p k) :=
  haveI := moduleFinite_padicInt p k
  Module.free_of_finite_type_torsion_free'

/-- **The Teichmüller roots generate `W(k)` over `ℤ_[p]`** —
`W(k) = ℤ_[p][μ_{|k|-1}]`.

The set is written out rather than named because
`HilbertModularity.teichmullerRootSet` lives downstream of this file; it is
that set verbatim, at `ℓ = p` and `R = W(k)`.

This is the clause that makes the Teichmüller half of
`HilbertHeckeAlgebra.adjoin_heckeT` a THEOREM about the local factor rather
than an assumption on it: the `W(k)` factor of `W(k) ⊗ 𝕋` is generated by
Teichmüller roots, and the `𝕋` factor by the Hecke operators, so together
they generate the base change and hence its local factor.

PROVEN, and the proof needs strictly less than the classical account
suggests. Only ONE inclusion is used: for `|k| = p^d` (`FiniteField.card`)
every Teichmüller lift satisfies `τ(a) ^ p ^ d = τ(a ^ |k|) = τ(a)`
(`FiniteField.pow_card`, `teichmuller` being a monoid hom), so

    Set.range (teichmuller p) ⊆ {x | ∃ n, 0 < n ∧ x ^ p ^ n = x}

and the conclusion follows from `span_range_teichmuller_eq_top` because a
subalgebra containing a spanning set contains its `ℤ_[p]`-span, hence
everything. In particular **the reverse inclusion is not needed**: one never
has to show that the displayed set consists of exactly the Teichmüller
lifts, and so `eq_of_mem_teichmullerRootSet` (the downstream uniqueness
statement this file's earlier draft expected to consume) plays no role. The
separability of `X ^ p ^ d - X` plays no role either. -/
theorem adjoin_teichmullerRootSet_eq_top [Finite k] :
    Algebra.adjoin ℤ_[p] {x : WittVector p k | ∃ n : ℕ, 0 < n ∧ x ^ p ^ n = x} = ⊤ := by
  haveI := Fintype.ofFinite k
  obtain ⟨d, -, hd⟩ := FiniteField.card k p
  have hsub : (Set.range fun a : k => teichmuller p a) ⊆
      {x : WittVector p k | ∃ n : ℕ, 0 < n ∧ x ^ p ^ n = x} := by
    rintro _ ⟨a, rfl⟩
    refine ⟨(d : ℕ), d.pos, ?_⟩
    rw [← map_pow, ← hd, FiniteField.pow_card]
  refine Algebra.eq_top_iff.mpr fun x => ?_
  have hx : x ∈ Submodule.span ℤ_[p] (Set.range fun a : k => teichmuller p a) := by
    rw [span_range_teichmuller_eq_top p k]; trivial
  have hle : Submodule.span ℤ_[p] (Set.range fun a : k => teichmuller p a) ≤
      Subalgebra.toSubmodule
        (Algebra.adjoin ℤ_[p] {x : WittVector p k | ∃ n : ℕ, 0 < n ∧ x ^ p ^ n = x}) :=
    Submodule.span_le.mpr fun y hy => Algebra.subset_adjoin (hsub hy)
  simpa using hle hx

end PadicIntModule

/-! ### The Hecke narrowing: the ring-theoretic package of the local factor -/

section HeckeNarrowing

variable (p : ℕ) [Fact p.Prime] (k : Type*) [Field k] [CharP k p]

/-- **The unramified base change `W(k) ⊗_{ℤ_[p]} 𝕋`.** Written with `W(k)` on
the left so that `Module.Finite.base_change` and `Module.Free.tensor` apply as
instances; it is `𝕋 ⊗_{ℤ_[p]} W(k)` up to the commutation isomorphism. -/
abbrev wittBaseChange (T : Type*) [CommRing T] [Algebra ℤ_[p] T] : Type _ :=
  TensorProduct ℤ_[p] (WittVector p k) T

/-- **Cofinal filtrations have the same completions.** If `I ≤ J` and
`J ^ (c+1) ≤ I`, then `I`-adic completeness of a module transfers to
`J`-adic completeness.

Both halves are index reparametrisations. Hausdorffness: `⨅ J ^ n • ⊤` is
below every `J ^ ((c+1)*n) • ⊤ ≤ I ^ n • ⊤`, so it is below `⨅ I ^ n • ⊤ = ⊥`.
Precompleteness: a `J`-Cauchy sequence `f` becomes `I`-Cauchy after
thinning to `n ↦ f ((c+1) * n)`, whose `I`-limit is a `J`-limit of `f`
because `I ^ n • ⊤ ≤ J ^ n • ⊤` and `f n ≡ f ((c+1) * n)` already holds
modulo `J ^ n • ⊤`.

Stated for a module rather than for `A` itself because that is what
`IsAdicComplete` is stated for, and it costs nothing. -/
theorem isAdicComplete_of_pow_le {A : Type*} [CommRing A] {I J : Ideal A}
    {M : Type*} [AddCommGroup M] [Module A M]
    (hIJ : I ≤ J) (c : ℕ) (hJI : J ^ (c + 1) ≤ I) [IsAdicComplete I M] :
    IsAdicComplete J M := by
  have key : ∀ n : ℕ, (J ^ ((c + 1) * n) • ⊤ : Submodule A M) ≤ I ^ n • ⊤ := fun n =>
    Submodule.smul_mono_left (by rw [pow_mul]; exact Ideal.pow_right_mono hJI n)
  have key2 : ∀ n : ℕ, (I ^ n • ⊤ : Submodule A M) ≤ J ^ n • ⊤ := fun n =>
    Submodule.smul_mono_left (Ideal.pow_right_mono hIJ n)
  have hmul : ∀ n : ℕ, n ≤ (c + 1) * n := fun n =>
    le_mul_of_one_le_left (Nat.zero_le n) (by omega)
  haveI : IsHausdorff J M :=
    ⟨fun x hx => IsHausdorff.haus (inferInstance : IsHausdorff I M) x fun n =>
      SModEq.mono (key n) (hx ((c + 1) * n))⟩
  haveI : IsPrecomplete J M := by
    refine ⟨fun f hf => ?_⟩
    obtain ⟨L, hL⟩ := IsPrecomplete.prec' (I := I) (M := M) (fun n => f ((c + 1) * n))
      (fun {m n} hmn => SModEq.mono (key m) (hf (Nat.mul_le_mul le_rfl hmn)))
    exact ⟨L, fun n => (hf (hmul n)).trans (SModEq.mono (key2 n) (hL n))⟩
  exact ⟨⟩

/-- **A module-finite LOCAL algebra over a complete Noetherian local ring is
complete for its OWN maximal-adic topology.**

`IsAdicComplete.of_finite_module` (`AdicCompletion/Finite.lean`) gives
completeness for `maximalIdeal R • A`, i.e. for the ideal coming from the
BASE. `HilbertHeckeAlgebra.isAdicComplete` — and every deformation-theoretic
consumer — asks for `IsAdicComplete (maximalIdeal A) A`, for `A`'s own
maximal ideal. The two agree because the filtrations are cofinal, which is
`isAdicComplete_of_pow_le` above; the content here is producing the two
comparisons.

* `J := 𝔪_R · A ≤ 𝔪_A`. `J ≠ ⊤` is Nakayama
  (`Submodule.eq_bot_of_le_smul_of_le_jacobson_bot` applied to the finitely
  generated `⊤`), and a proper ideal of a local ring lies in the maximal one.
* `𝔪_A ^ (c+1) ≤ J`. `A ⧸ J` is a finite algebra over the field `R ⧸ 𝔪_R`,
  hence artinian, and it is local (surjective image of the local `A`), so its
  Jacobson radical — which is its maximal ideal — is nilpotent
  (`IsArtinianRing.isNilpotent_jacobson_bot`). Pulling that back along
  `Ideal.Quotient.mk J` with `Ideal.le_comap_pow` gives the bound, the
  contraction of `𝔪_{A/J}` being `𝔪_A` by maximality plus locality.

This is stated separately because it is a general fact with no Witt vectors
in it, and it is the last purely ring-theoretic clause of the narrowing.

One implementation note worth keeping, since it cost a cycle: the residue
field instance must be introduced with `letI`, not `haveI`. `haveI` forgets
the body, so the `Ring (R ⧸ 𝔪_R)` inside the `Field` no longer reduces to
`Ideal.Quotient.commRing`, and `IsArtinianRing (R ⧸ 𝔪_R)` then fails to
synthesize even though `DivisionRing.instIsArtinianRing` applies. -/
theorem isAdicComplete_maximalIdeal_of_moduleFinite (R : Type*) [CommRing R]
    [IsNoetherianRing R] [IsLocalRing R] [IsAdicComplete (IsLocalRing.maximalIdeal R) R]
    (A : Type*) [CommRing A] [Algebra R A] [Module.Finite R A] [IsLocalRing A] :
    IsAdicComplete (IsLocalRing.maximalIdeal A) A := by
  classical
  haveI h1 : IsAdicComplete (IsLocalRing.maximalIdeal R) A := IsAdicComplete.of_finite_module
  haveI h2 : IsAdicComplete ((IsLocalRing.maximalIdeal R).map (algebraMap R A)) A :=
    (IsAdicComplete.map_algebraMap_iff (IsLocalRing.maximalIdeal R) A).mpr h1
  -- the extended ideal is proper, by Nakayama
  have hJtop : (IsLocalRing.maximalIdeal R).map (algebraMap R A) ≠ ⊤ := by
    intro hcon
    have hle : (⊤ : Submodule R A) ≤ (IsLocalRing.maximalIdeal R) • (⊤ : Submodule R A) := by
      rw [Ideal.smul_top_eq_map, hcon]
      exact fun x _ => Submodule.mem_top
    have hbot := Submodule.eq_bot_of_le_smul_of_le_jacobson_bot (IsLocalRing.maximalIdeal R)
      (⊤ : Submodule R A) Module.Finite.fg_top hle
      (le_of_eq (IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top).symm)
    exact one_ne_zero (α := A) (by
      simpa using (Submodule.eq_bot_iff _).mp hbot (1 : A) Submodule.mem_top)
  have hJle : (IsLocalRing.maximalIdeal R).map (algebraMap R A) ≤ IsLocalRing.maximalIdeal A :=
    IsLocalRing.le_maximalIdeal hJtop
  haveI : Nontrivial (A ⧸ (IsLocalRing.maximalIdeal R).map (algebraMap R A)) :=
    Ideal.Quotient.nontrivial_iff.mpr hJtop
  haveI : IsLocalRing (A ⧸ (IsLocalRing.maximalIdeal R).map (algebraMap R A)) :=
    IsLocalRing.of_surjective' _ Ideal.Quotient.mk_surjective
  haveI : Module.Finite R (A ⧸ (IsLocalRing.maximalIdeal R).map (algebraMap R A)) :=
    Module.Finite.of_surjective
      (Ideal.Quotient.mkₐ R ((IsLocalRing.maximalIdeal R).map (algebraMap R A))).toLinearMap
      Ideal.Quotient.mk_surjective
  haveI : Module.Finite (R ⧸ IsLocalRing.maximalIdeal R)
      (A ⧸ (IsLocalRing.maximalIdeal R).map (algebraMap R A)) :=
    Module.Finite.of_restrictScalars_finite R _ _
  letI : Field (R ⧸ IsLocalRing.maximalIdeal R) :=
    Ideal.Quotient.field (IsLocalRing.maximalIdeal R)
  haveI : IsArtinianRing (A ⧸ (IsLocalRing.maximalIdeal R).map (algebraMap R A)) :=
    IsArtinianRing.of_finite (R ⧸ IsLocalRing.maximalIdeal R) _
  obtain ⟨c, hc⟩ := IsArtinianRing.isNilpotent_jacobson_bot
    (R := A ⧸ (IsLocalRing.maximalIdeal R).map (algebraMap R A))
  rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top] at hc
  -- pull the nilpotence back along the quotient map
  have hmaxeq : IsLocalRing.maximalIdeal A =
      (IsLocalRing.maximalIdeal
          (A ⧸ (IsLocalRing.maximalIdeal R).map (algebraMap R A))).comap
        (Ideal.Quotient.mk ((IsLocalRing.maximalIdeal R).map (algebraMap R A))) :=
    (IsLocalRing.eq_maximalIdeal
      (Ideal.comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective)).symm
  have hc1 : IsLocalRing.maximalIdeal
      (A ⧸ (IsLocalRing.maximalIdeal R).map (algebraMap R A)) ^ (c + 1) ≤ ⊥ :=
    calc IsLocalRing.maximalIdeal
          (A ⧸ (IsLocalRing.maximalIdeal R).map (algebraMap R A)) ^ (c + 1)
        ≤ IsLocalRing.maximalIdeal
            (A ⧸ (IsLocalRing.maximalIdeal R).map (algebraMap R A)) ^ c :=
          Ideal.pow_le_pow_right (Nat.le_succ c)
      _ ≤ ⊥ := le_of_eq (by simpa using hc)
  have hpow : IsLocalRing.maximalIdeal A ^ (c + 1) ≤
      (IsLocalRing.maximalIdeal R).map (algebraMap R A) := by
    rw [hmaxeq]
    refine (Ideal.le_comap_pow ..).trans ((Ideal.comap_mono hc1).trans ?_)
    rw [← RingHom.ker_eq_comap_bot, Ideal.mk_ker]
  exact isAdicComplete_of_pow_le hJle c hpow

/-- **THE NARROWING, ring-theoretic half: the local factor of
`W(k) ⊗_{ℤ_[p]} 𝕋` carries every ring-theoretic field that
`HilbertHeckeAlgebra` currently POSITS.**

This is the Lean content of "the `W(k)` base change should be PROVEN, not
cited", recorded as the next real reduction under "NARROWINGS IDENTIFIED" in
the docstring of `nonempty_potentialHeckeDatum_of_five_le`
(`HardlyRamified/HilbertModularity.lean`). Given only

* `k` a finite field of characteristic `p` — the residual coefficient field;
* `𝕋` a CLASSICAL `ℤ_[p]`-Hecke algebra, i.e. module-finite and free over
  `ℤ_[p]` and nothing else; and
* a maximal ideal `𝔪` of the unramified base change `W(k) ⊗_{ℤ_[p]} 𝕋`,

the local factor cut out by `𝔪` is LOCAL, module-finite and FREE over
`ℤ_[p]`, and maximal-adically complete — i.e. exactly
`HilbertHeckeAlgebra`'s `isLocalRing`, `moduleFinite`, `moduleFree` and
`isAdicComplete`, DERIVED instead of assumed. It comes with the direct-factor
decomposition, which is what identifies it as "the localization of `𝕋` at
`𝔪`" rather than an arbitrary quotient.

What is deliberately NOT here, and why: `πT_surjective` needs `𝔪` to be
chosen with residue field exactly `k` (a hypothesis ON `𝔪`, the "chosen
embedding of the residue field" of the audit at
`HilbertModularity.lean`'s `HilbertHeckeAlgebra` docstring), and
`adjoin_heckeT` needs `adjoin_teichmullerRootSet_eq_top` above together with
the Hecke operators; both are packaging on top of this, not part of it. The
arithmetic fields (`ρT`, `isHilbertHardlyRamified`, `charFrobT`, `residT`)
are untouched by the narrowing — they are what the potential-modularity
citation supplies, and no commutative algebra reaches them. -/
theorem exists_localFactor_wittBaseChange [Finite k]
    (T : Type*) [CommRing T] [Algebra ℤ_[p] T] [Module.Finite ℤ_[p] T]
    [Module.Free ℤ_[p] T]
    (𝔪 : Ideal (wittBaseChange p k T)) (h𝔪 : 𝔪.IsMaximal) :
    ∃ e : wittBaseChange p k T,
      IsIdempotentElem e ∧ 1 - e ∈ 𝔪 ∧
      Module.Finite ℤ_[p] (wittBaseChange p k T ⧸ Ideal.span {1 - e}) ∧
      Module.Free ℤ_[p] (wittBaseChange p k T ⧸ Ideal.span {1 - e}) ∧
      Nonempty (wittBaseChange p k T ≃ₐ[WittVector p k]
        (wittBaseChange p k T ⧸ Ideal.span {1 - e}) ×
        (wittBaseChange p k T ⧸ Ideal.span {e})) ∧
      ∃ _ : IsLocalRing (wittBaseChange p k T ⧸ Ideal.span {1 - e}),
        IsAdicComplete
          (IsLocalRing.maximalIdeal (wittBaseChange p k T ⧸ Ideal.span {1 - e}))
          (wittBaseChange p k T ⧸ Ideal.span {1 - e}) := by
  haveI := moduleFinite_padicInt p k
  haveI := moduleFree_padicInt p k
  -- `W(k) ⊗ 𝕋` is module-finite over `ℤ_[p]`, being a tensor product of two
  -- module-finite `ℤ_[p]`-modules.
  haveI hSfin : Module.Finite ℤ_[p] (wittBaseChange p k T) :=
    Module.Finite.tensorProduct ..
  obtain ⟨e, he, hem, hloc, hsplit⟩ :=
    exists_isIdempotentElem_isLocalRing_quotient_baseChange p k T 𝔪 h𝔪
  haveI := hloc
  -- module-finite: a quotient of a module-finite module
  haveI hQfin : Module.Finite ℤ_[p] (wittBaseChange p k T ⧸ Ideal.span {1 - e}) :=
    Module.Finite.of_surjective
      (Submodule.mkQ ((Ideal.span {1 - e}).restrictScalars ℤ_[p]))
      (Submodule.mkQ_surjective _)
  obtain ⟨eqv⟩ := hsplit
  -- torsion-free: the local factor injects into the free module `W(k) ⊗ 𝕋`
  -- as a direct factor, along `x ↦ eqv.symm (x, 0)`
  haveI hQtf : Module.IsTorsionFree ℤ_[p]
      (wittBaseChange p k T ⧸ Ideal.span {1 - e}) :=
    Function.Injective.moduleIsTorsionFree
      (fun x => eqv.symm (x, 0))
      (fun x y hxy => by simpa using eqv.symm.injective hxy)
      (fun r x => by
        have hp : ((r • x, 0) : (wittBaseChange p k T ⧸ Ideal.span {1 - e}) ×
            (wittBaseChange p k T ⧸ Ideal.span {e})) = r • (x, 0) := by simp
        rw [hp]
        exact map_smul (eqv.symm.restrictScalars ℤ_[p]) r (x, 0))
  exact ⟨e, he, hem, hQfin, Module.free_of_finite_type_torsion_free', ⟨eqv⟩,
    hloc, isAdicComplete_maximalIdeal_of_moduleFinite ℤ_[p] _⟩

end HeckeNarrowing

end WittVector
