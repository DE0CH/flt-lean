module

import Fermat.FLT.Mathlib.NumberTheory.Padics.LocalField
import Fermat.FLT.DedekindDomain.AdicValuation
import Fermat.FLT.Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.AdicCompletion.Noetherian

open IsDedekindDomain HeightOneSpectrum ValuativeRel

noncomputable def v₃ : HeightOneSpectrum (NumberField.RingOfIntegers ℚ) :=
  Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat

local notation "K3" => HeightOneSpectrum.adicCompletion ℚ v₃

#synth IsNoetherianRing (v₃.adicCompletionIntegers ℚ)
#synth IsDomain (v₃.adicCompletionIntegers ℚ)
#synth IsLocalRing (v₃.adicCompletionIntegers ℚ)
#synth UniformSpace K3
#synth IsUniformAddGroup K3
#synth IsNonarchimedeanLocalField K3

-- the ValuativeRel integer ring and its adic completeness
#synth IsAdicComplete 𝓂[K3] 𝒪[K3]

-- compactness/completeness of the adicCompletionIntegers
#synth CompleteSpace (v₃.adicCompletionIntegers ℚ)
#synth CompactSpace (v₃.adicCompletionIntegers ℚ)

-- carrier comparison
example : (𝒪[K3] : Set K3) = ((v₃.adicCompletionIntegers ℚ : ValuationSubring K3) : Set K3) := by
  ext x
  exact (Valuation.isEquiv_iff_val_le_one.mp
    (ValuativeRel.isEquiv (ValuativeRel.valuation K3) Valued.v)).symm ▸ Iff.rfl
