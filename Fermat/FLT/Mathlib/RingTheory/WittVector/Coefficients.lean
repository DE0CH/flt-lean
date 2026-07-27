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

end WittVector
