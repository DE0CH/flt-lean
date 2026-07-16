/-
Copyright (c) 2026 Deyao Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Deyao Chen
-/
module

public import Fermat.FLT.Deformations.RepresentationTheory.AbsoluteGaloisGroup

/-!
# The fixed field of the local inertia group is unramified

This file states the LOCAL half of the embedding-prime transport family:
if a finite subextension `M/Kᵥ` of `Kᵥᵃˡᵍ` is fixed pointwise by the
local inertia group `localInertiaGroup v ≤ Γ Kᵥ`, then `M/Kᵥ` is
unramified, in the concrete integral form: the maximal ideal of `𝒪ᵥ`
generates the maximal ideal of the integral closure `𝒪_M` of `𝒪ᵥ` in
`M` (i.e. `e(M/Kᵥ) = 1`).

Classically this is the statement that the fixed field of the inertia
group of `Kᵥᵃˡᵍ/Kᵥ` is the maximal unramified extension `Kᵥᵘⁿʳ`
(Neukirch, *Algebraic Number Theory*, II.9.11 / II.7.5 applied through
finite levels). The planned proof route (see PROGRESS.md): pass to the
Galois closure `N` of `M/Kᵥ`, use `|I(N/Kᵥ)| = e(N/Kᵥ)` at the finite
level (`Ideal.card_inertia_eq_ramificationIdxIn`, applicable because
the integral closure at every finite level is LOCAL — a valuation ring
via the vendored spectral-norm argument — with finite residue field),
tower multiplicativity of `e`, and a compactness lifting of finite-level
inertia elements to `localInertiaGroup v` (finite-level inertia
surjectivity along towers is a counting argument from the same two
ingredients; no henselian lifting is required).

The GLOBAL half (transporting this statement to the trivial-inertia
prime `Q₀` of a number field `L` fixed by the image of the local
inertia) is derived in `Fermat.FLT.FreyCurve.MazurTorsion`.
-/

@[expose] public section

open NumberField IsDedekindDomain

variable {K : Type*} [Field K] [NumberField K]
variable (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))

local notation3 "Γ" K:max => Field.absoluteGaloisGroup K
local notation3 K:max "ᵃˡᵍ" => AlgebraicClosure K
local notation3 "𝔪" => IsLocalRing.maximalIdeal
local notation "Kᵥ" => IsDedekindDomain.HeightOneSpectrum.adicCompletion K v
local notation "𝒪ᵥ" => IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers K v

set_option warn.sorry false in
/-- **The fixed field of the local inertia group is unramified** (the
local half of the embedding-prime transport; Neukirch II.9.11): if a
finite subextension `M/Kᵥ` of `Kᵥᵃˡᵍ` is fixed pointwise by
`localInertiaGroup v`, then the maximal ideal of `𝒪ᵥ` generates the
maximal ideal of the integral closure of `𝒪ᵥ` in `M` — that is,
`e(M/Kᵥ) = 1`. -/
theorem maximalIdeal_map_eq_of_le_fixedField_localInertiaGroup
    (M : IntermediateField Kᵥ (Kᵥᵃˡᵍ)) [FiniteDimensional Kᵥ M]
    (hM : M ≤ IntermediateField.fixedField (localInertiaGroup v)) :
    (𝔪 𝒪ᵥ).map (algebraMap 𝒪ᵥ (IntegralClosure 𝒪ᵥ M)) =
      𝔪 (IntegralClosure 𝒪ᵥ M) :=
  sorry
