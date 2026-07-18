/-
Copyright (c) 2026 the Fermat project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Fermat.FLT.Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Fermat.FLT.Deformations.RepresentationTheory.IntegralClosure
public import Fermat.FLT.Deformations.RepresentationTheory.AbsoluteGaloisGroup
public import Fermat.FLT.DedekindDomain.AdicValuation
public import Mathlib.NumberTheory.Padics.HeightOneSpectrum
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.RingTheory.Ideal.GoingUp

/-!
# Residue cardinality at a prime's place of `ℚ`

The residue field of the completed integers at the place of `ℚ` attached to a
prime `q` has exactly `q` elements, and the same holds for the quotient by the
contraction of the maximal ideal of the integral closure in `ℚ_qᵃˡᵍ` (the `q`
of the `IsArithFrobAt` specification). Moved out of `Chebotarev.lean` so that
`Deformations.RepresentationTheory.GaloisRep` can consume it.
-/

@[expose] public section

namespace GaloisRepresentation

open IsDedekindDomain
open scoped NumberField

set_option backward.isDefEq.respectTransparency false in
/-- The residue field of `ℤ_[p]` has `p` elements: `toZMod` is surjective
with kernel the maximal ideal. -/
lemma natCard_quotient_maximalIdeal_padicInt (p : ℕ) [Fact p.Prime] :
    Nat.card (ℤ_[p] ⧸ IsLocalRing.maximalIdeal ℤ_[p]) = p := by
  have hsurj : Function.Surjective (PadicInt.toZMod (p := p)) := by
    intro a
    exact ⟨((a.val : ℕ) : ℤ_[p]), by rw [map_natCast, ZMod.natCast_val,
      ZMod.cast_id]⟩
  have e1 : (ℤ_[p] ⧸ IsLocalRing.maximalIdeal ℤ_[p]) ≃+*
      (ℤ_[p] ⧸ RingHom.ker (PadicInt.toZMod (p := p))) :=
    Ideal.quotEquivOfEq (PadicInt.ker_toZMod).symm
  have e2 : (ℤ_[p] ⧸ RingHom.ker (PadicInt.toZMod (p := p))) ≃+* ZMod p :=
    RingHom.quotientKerEquivOfSurjective hsurj
  rw [Nat.card_congr e1.toEquiv, Nat.card_congr e2.toEquiv, Nat.card_zmod]

set_option backward.isDefEq.respectTransparency false in
/-- The natural generator of a prime's place is the prime itself. -/
lemma natGenerator_toHeightOneSpectrum {q : ℕ} (hq : q.Prime) :
    Rat.HeightOneSpectrum.natGenerator
      (Nat.Prime.toHeightOneSpectrumRingOfIntegersRat hq) = q := by
  have hspan := Rat.HeightOneSpectrum.span_natGenerator
    (Nat.Prime.toHeightOneSpectrumRingOfIntegersRat hq)
  -- the place's ideal maps to `span {q}` under the integer equivalence
  have hmap : (Nat.Prime.toHeightOneSpectrumRingOfIntegersRat hq).asIdeal.map
      (Rat.IsIntegralClosure.intEquiv (NumberField.RingOfIntegers ℚ)) =
      Ideal.span {(q : ℤ)} := by
    have h1 : (Nat.Prime.toHeightOneSpectrumRingOfIntegersRat hq).asIdeal =
        Ideal.comap (Rat.ringOfIntegersEquiv.symm.symm)
          (Ideal.span {(q : ℤ)}) := rfl
    rw [h1]
    have h2 : (Rat.IsIntegralClosure.intEquiv (NumberField.RingOfIntegers ℚ) :
        NumberField.RingOfIntegers ℚ ≃+* ℤ) = Rat.ringOfIntegersEquiv := by
      ext x
      exact Rat.IsIntegralClosure.intEquiv_apply_eq_ringOfIntegersEquiv x
    rw [h2]
    have h3 : (Rat.ringOfIntegersEquiv.symm.symm :
        NumberField.RingOfIntegers ℚ ≃+* ℤ) = Rat.ringOfIntegersEquiv := by
      ext x
      rfl
    rw [h3]
    exact Ideal.map_comap_of_surjective _ Rat.ringOfIntegersEquiv.surjective _
  rw [hmap, Ideal.span_singleton_eq_span_singleton] at hspan
  have := Int.associated_iff_natAbs.mp hspan
  simpa using this

/-- **Residue cardinality at a prime's place** (PROVEN): for the place of `ℚ`
attached to a prime `q`, the contraction of the maximal ideal of the integral
closure of the completed integers in `ℚ_qᵃˡᵍ` cuts out a quotient of
cardinality `q` — the residue field of `ℤ_q` is `𝔽_q`. This identifies the
exponent of `IsArithFrobAt` (which is `Nat.card (𝒪ᵥ ⧸ Q.under 𝒪ᵥ)`) with `q`. -/
theorem natCard_residue_quotient_toHeightOneSpectrum {q : ℕ} (hq : q.Prime) :
    Nat.card ((IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ
        (Nat.Prime.toHeightOneSpectrumRingOfIntegersRat hq)) ⧸
      ((IsLocalRing.maximalIdeal (IntegralClosure
          (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ
            (Nat.Prime.toHeightOneSpectrumRingOfIntegersRat hq))
          (AlgebraicClosure
            (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
              (Nat.Prime.toHeightOneSpectrumRingOfIntegersRat hq))))).under
        (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ
          (Nat.Prime.toHeightOneSpectrumRingOfIntegersRat hq)))) = q := by
  haveI hfact : Fact (Rat.HeightOneSpectrum.primesEquiv
      (Nat.Prime.toHeightOneSpectrumRingOfIntegersRat hq)).1.Prime :=
    ⟨(Rat.HeightOneSpectrum.primesEquiv
      (Nat.Prime.toHeightOneSpectrumRingOfIntegersRat hq)).2⟩
  -- the contraction of the maximal ideal is the maximal ideal
  have hunder : ((IsLocalRing.maximalIdeal (IntegralClosure
      (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ
        (Nat.Prime.toHeightOneSpectrumRingOfIntegersRat hq))
      (AlgebraicClosure
        (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
          (Nat.Prime.toHeightOneSpectrumRingOfIntegersRat hq))))).under
      (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ
        (Nat.Prime.toHeightOneSpectrumRingOfIntegersRat hq))) =
      IsLocalRing.maximalIdeal
        (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ
          (Nat.Prime.toHeightOneSpectrumRingOfIntegersRat hq)) :=
    IsLocalRing.eq_maximalIdeal (Ideal.IsMaximal.under
      (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ
        (Nat.Prime.toHeightOneSpectrumRingOfIntegersRat hq))
      (IsLocalRing.maximalIdeal (IntegralClosure
        (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ
          (Nat.Prime.toHeightOneSpectrumRingOfIntegersRat hq))
        (AlgebraicClosure
          (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
            (Nat.Prime.toHeightOneSpectrumRingOfIntegersRat hq))))))
  rw [hunder]
  -- transport to `ℤ_[q]` through the padic equivalence
  have e := (Rat.HeightOneSpectrum.adicCompletionIntegers.padicIntEquiv
    (Nat.Prime.toHeightOneSpectrumRingOfIntegersRat hq)).toRingEquiv
  have hmapmax : IsLocalRing.maximalIdeal
      ℤ_[Rat.HeightOneSpectrum.primesEquiv
        (Nat.Prime.toHeightOneSpectrumRingOfIntegersRat hq)] =
      (IsLocalRing.maximalIdeal
        (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ
          (Nat.Prime.toHeightOneSpectrumRingOfIntegersRat hq))).map e := by
    symm
    rw [← Ideal.comap_symm e]
    exact IsLocalRing.eq_maximalIdeal
      (Ideal.comap_isMaximal_of_surjective _ e.symm.surjective)
  rw [Nat.card_congr (Ideal.quotientEquiv _ _ e hmapmax).toEquiv,
    natCard_quotient_maximalIdeal_padicInt]
  show (Rat.HeightOneSpectrum.primesEquiv
    (Nat.Prime.toHeightOneSpectrumRingOfIntegersRat hq)).1 = q
  rw [show (Rat.HeightOneSpectrum.primesEquiv
    (Nat.Prime.toHeightOneSpectrumRingOfIntegersRat hq)).1 =
    Rat.HeightOneSpectrum.natGenerator
      (Nat.Prime.toHeightOneSpectrumRingOfIntegersRat hq) from rfl,
    natGenerator_toHeightOneSpectrum hq]

end GaloisRepresentation
