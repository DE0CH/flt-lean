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
public import Mathlib.RingTheory.WittVector.DiscreteValuationRing
public import Mathlib.RingTheory.TensorProduct.Finite
public import Mathlib.LinearAlgebra.FreeModule.PID
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

/-! ### `W(k)` over `ℤ_[p]`: injectivity, torsion-freeness, and the two open leaves

Everything above is about `W(k)` as a ring in its own right. The narrowing
also needs `W(k)` as a `ℤ_[p]`-MODULE: module-finite, free, and generated by
Teichmüller roots. Torsion-freeness is elementary and proven here;
module-finiteness and the Teichmüller generation are the two genuinely open
leaves, and mathlib has neither (the refuting check is

    grep -rn 'Module.Finite\|Module.Free' Mathlib/RingTheory/WittVector/

which returns nothing about `𝕎 k` as a module over anything). -/

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

/-- **LEAF (open): `W(k)` is module-finite over `ℤ_[p]` for `k` a FINITE
field.** Classically `W(k)` is the unramified extension of `ℤ_[p]` of degree
`d = [k : 𝔽_p]`, free of rank `d`.

Not in mathlib: `Mathlib/RingTheory/WittVector/` contains no `Module.Finite`
or `Module.Free` statement about `𝕎 k` over any base, and no unramified-
extension theory. The intended route is the `p`-adic one: `𝕎 k / p^n` is
`TruncatedWittVector p n k`, which is FINITE for finite `k`
(`TruncatedWittVector.instFintype`, with `card = |k|^n`), and `𝕎 k` is
`p`-adically complete and separated (`isAdicCompleteIdealSpanP`); a complete
separated ring whose reduction mod `p` is finite over `𝔽_p` is
topologically finitely generated, and complete + topologically f.g. over the
complete local `ℤ_[p]` gives module-finiteness by the formal-Nakayama
argument (lift an `𝔽_p`-basis of `𝕎 k / p`, i.e. of `k`, and conclude by
completeness).

The check that would refute this leaf's being open: a hit from
`grep -rn 'Module.Finite.*WittVector\|WittVector.*Module.Finite' Mathlib/`. -/
theorem moduleFinite_padicInt [Finite k] : Module.Finite ℤ_[p] (WittVector p k) :=
  sorry

/-- **`W(k)` is free over `ℤ_[p]`** (for finite `k`) — PROVEN over
`moduleFinite_padicInt`, since `ℤ_[p]` is a PID and `W(k)` is torsion-free.
This is a derivation, not a second leaf. -/
theorem moduleFree_padicInt [Finite k] : Module.Free ℤ_[p] (WittVector p k) :=
  haveI := moduleFinite_padicInt p k
  Module.free_of_finite_type_torsion_free'

/-- **LEAF (open): the Teichmüller roots generate `W(k)` over `ℤ_[p]`** —
`W(k) = ℤ_[p][μ_{|k|-1}]`.

The set is written out rather than named because
`HilbertModularity.teichmullerRootSet` lives downstream of this file; it is
that set verbatim, at `ℓ = p` and `R = W(k)`.

This is the clause that makes the Teichmüller half of
`HilbertHeckeAlgebra.adjoin_heckeT` a THEOREM about the local factor rather
than an assumption on it: the `W(k)` factor of `W(k) ⊗ 𝕋` is generated by
Teichmüller roots, and the `𝕋` factor by the Hecke operators, so together
they generate the base change and hence its local factor.

Classically: for `|k| = p^d` the Teichmüller lifts of `k^×` are the
`(p^d - 1)`-st roots of unity, they satisfy `x ^ p ^ d = x`, they reduce
bijectively onto `k` (`X ^ p ^ d - X` is separable mod `p`), and
`ℤ_[p][μ_{p^d-1}]` is then a complete subring surjecting onto the residue
field, so it is everything by completeness. `WittVector.teichmuller` supplies
the lifts and `eq_of_mem_teichmullerRootSet` (already proven downstream)
supplies their uniqueness; what is missing is the surjectivity-plus-
completeness step.

The check that would refute this leaf's being open: a hit from
`grep -rn 'Algebra.adjoin.*teichmuller' Mathlib/`. -/
theorem adjoin_teichmullerRootSet_eq_top [Finite k] :
    Algebra.adjoin ℤ_[p] {x : WittVector p k | ∃ n : ℕ, 0 < n ∧ x ^ p ^ n = x} = ⊤ :=
  sorry

end PadicIntModule

/-! ### The Hecke narrowing: the ring-theoretic package of the local factor -/

section HeckeNarrowing

variable (p : ℕ) [Fact p.Prime] (k : Type*) [Field k] [CharP k p]

/-- **The unramified base change `W(k) ⊗_{ℤ_[p]} 𝕋`.** Written with `W(k)` on
the left so that `Module.Finite.base_change` and `Module.Free.tensor` apply as
instances; it is `𝕋 ⊗_{ℤ_[p]} W(k)` up to the commutation isomorphism. -/
abbrev wittBaseChange (T : Type*) [CommRing T] [Algebra ℤ_[p] T] : Type _ :=
  TensorProduct ℤ_[p] (WittVector p k) T

/-- **LEAF (open): a module-finite LOCAL algebra over a complete Noetherian
local ring is complete for its OWN maximal-adic topology.**

`IsAdicComplete.of_finite_module` (`AdicCompletion/Finite.lean`) gives
completeness for `maximalIdeal R • A`, i.e. for the ideal coming from the
BASE. `HilbertHeckeAlgebra.isAdicComplete` — and every deformation-theoretic
consumer — asks for `IsAdicComplete (maximalIdeal A) A`, for `A`'s own
maximal ideal. The two agree because the filtrations are cofinal: `𝔪_R • A ⊆
𝔪_A` since `R → A` is local, and conversely `𝔪_A ^ n ⊆ 𝔪_R • A` for some `n`
because `A / 𝔪_R A` is artinian local, so its maximal ideal is nilpotent.
Cofinal filtrations have the same completions.

This is stated separately because it is a general fact with no Witt vectors
in it, and it is the last purely ring-theoretic clause of the narrowing.

The check that would refute this leaf's being open: a hit from
`grep -rn 'IsAdicComplete.*maximalIdeal.*Finite\|cofinal' Mathlib/RingTheory/AdicCompletion/`. -/
theorem isAdicComplete_maximalIdeal_of_moduleFinite (R : Type*) [CommRing R]
    [IsNoetherianRing R] [IsLocalRing R] [IsAdicComplete (IsLocalRing.maximalIdeal R) R]
    (A : Type*) [CommRing A] [Algebra R A] [Module.Finite R A] [IsLocalRing A] :
    IsAdicComplete (IsLocalRing.maximalIdeal A) A :=
  sorry

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
