/-
Copyright (c) 2026 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll, Claude
-/
module

public import Mathlib.NumberTheory.Padics.RingHoms
public import Mathlib.RingTheory.DiscreteValuationRing.TFAE
public import Fermat.FLT.Mathlib.RingTheory.Polynomial.GaussLemma

/-!
# Reducing a monic rational divisor of an integral polynomial mod `ℓ`

Material for `Mathlib.RingTheory.Polynomial.GaussLemma`.

The classical Gauss step — *a monic rational divisor of a MONIC integral polynomial is
integral* — is `Polynomial.Monic.exists_monic_map_eq_of_monic_dvd_map`.  It is **false**
without monicity (`X + 1/2 ∣ 2X² + 3X + 1`), and the polynomials one actually wants to
apply it to are rarely monic: the `p`-division polynomial `Ψ_p` of an elliptic curve has
leading coefficient `p` (`WeierstrassCurve.leadingCoeff_preΨ'`).

The correct side condition is *local* rather than global, and it is what this file supplies:

> Let `F ∈ ℤ[X]` and let `ℓ` be a prime with `ℓ ∤ leadingCoeff F`.  If `g ∈ ℚ[X]` is monic
> with `g ∣ F` in `ℚ[X]`, then there is a monic `G ∈ (ZMod ℓ)[X]` with `deg G = deg g`
> dividing `F mod ℓ`.

The proof is the two-line one: over the DVR `ℤ_[ℓ]` the leading coefficient of `F` becomes a
UNIT, so `F` is a unit multiple of a monic polynomial and the classical Gauss step applies
verbatim; then reduce along `PadicInt.toZMod`.  Working `ℓ`-adically rather than with the
localisation `ℤ_(ℓ)` is what makes the residue map available as a ring hom to `ZMod ℓ`.

This turns a mod-`ℓ` factorisation-degree computation into an obstruction over `ℚ`: if no
sub-multiset of the degrees of the irreducible factors of `F mod ℓ` sums to `n`, then `F` has
no monic rational divisor of degree `n` at all.
-/

@[expose] public section

open Polynomial

/-- **A monic divisor over the fraction field descends when the leading coefficient is a
unit.**  This is `Polynomial.Monic.exists_monic_map_eq_of_monic_dvd_map` with monicity of `F`
relaxed to `IsUnit F.leadingCoeff`, which is all the proof ever uses: `F` is then the unit
multiple `C (leadingCoeff F) * F₁` of a monic `F₁ ∈ R[X]`, and a unit of `R[X]` is invisible
to divisibility over `K[X]`.

The conclusion carries the divisibility `G ∣ F` in `R[X]` — not merely `G.map = g` — because
that is what a reduction step downstream needs. -/
theorem Polynomial.exists_monic_dvd_of_isUnit_leadingCoeff {R : Type*} [CommRing R] [IsDomain R]
    [IsIntegrallyClosed R] {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
    {F : R[X]} (hlc : IsUnit F.leadingCoeff)
    {g : K[X]} (hg : g.Monic) (hdvd : g ∣ F.map (algebraMap R K)) :
    ∃ G : R[X], G.Monic ∧ G.natDegree = g.natDegree ∧ G ∣ F := by
  obtain ⟨u, hu⟩ := hlc
  set F₁ : R[X] := C ((u⁻¹ : Rˣ) : R) * F with hF₁def
  have hF₁monic : F₁.Monic := by
    have h : F₁.leadingCoeff = ((u⁻¹ : Rˣ) : R) * F.leadingCoeff := by
      rw [hF₁def, leadingCoeff_mul, leadingCoeff_C]
    rw [Monic, h, ← hu, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hdvd₁ : g ∣ F₁.map (algebraMap R K) := by
    rw [hF₁def, Polynomial.map_mul, Polynomial.map_C]
    exact hdvd.mul_left _
  obtain ⟨G, hGmonic, hGmap⟩ := hF₁monic.exists_monic_map_eq_of_monic_dvd_map hg hdvd₁
  have hinj : Function.Injective (algebraMap R K) := IsFractionRing.injective R K
  have hunit : C ((u⁻¹ : Rˣ) : R) * C ((u : R)) = 1 := by
    rw [← C_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, C_1]
  have hGdvdF₁ : G ∣ F₁ := (map_dvd_map _ hinj hGmonic).mp (hGmap ▸ hdvd₁)
  have hF₁dvdF : F₁ ∣ F := ⟨C ((u : R)), by
    calc F = C ((u⁻¹ : Rˣ) : R) * C ((u : R)) * F := by rw [hunit, one_mul]
      _ = F₁ * C ((u : R)) := by rw [hF₁def]; ring⟩
  exact ⟨G, hGmonic, by rw [← hGmonic.natDegree_map (algebraMap R K), hGmap],
    hGdvdF₁.trans hF₁dvdF⟩

/-- **THE GAUSS STEP FOR A NON-MONIC INTEGRAL POLYNOMIAL.**  If the prime `ℓ` does not divide
the leading coefficient of `F ∈ ℤ[X]`, every monic rational divisor of `F` reduces to a monic
divisor of `F mod ℓ` OF THE SAME DEGREE.

The hypothesis `ℓ ∤ leadingCoeff F` cannot be dropped: `X + 1/2` divides `2X² + 3X + 1` over
`ℚ` and has no monic reduction of degree `1` dividing `2X² + 3X + 1 = X + 1` mod `2`.

Contrapositively — and this is how it is used — a mod-`ℓ` degree obstruction rules out a
rational divisor: if `F mod ℓ` has no monic divisor of degree `n`, then `F` has no monic
rational divisor of degree `n`. -/
theorem Polynomial.exists_monic_dvd_map_zmod_of_monic_dvd_map_rat {ℓ : ℕ} [hℓ : Fact ℓ.Prime]
    {F : ℤ[X]} (hlc : ¬ (ℓ : ℤ) ∣ F.leadingCoeff)
    {g : ℚ[X]} (hg : g.Monic) (hdvd : g ∣ F.map (Int.castRingHom ℚ)) :
    ∃ G : (ZMod ℓ)[X], G.Monic ∧ G.natDegree = g.natDegree ∧
      G ∣ F.map (Int.castRingHom (ZMod ℓ)) := by
  haveI : Fact (1 < ℓ) := ⟨hℓ.out.one_lt⟩
  have hinj : Function.Injective (Int.castRingHom ℤ_[ℓ]) :=
    fun a b h => by simpa using (h : ((a : ℤ_[ℓ]) = b))
  set P : ℤ_[ℓ][X] := F.map (Int.castRingHom ℤ_[ℓ]) with hPdef
  have hlcP : P.leadingCoeff = (Int.castRingHom ℤ_[ℓ]) F.leadingCoeff :=
    leadingCoeff_map_of_injective hinj F
  have hu : IsUnit P.leadingCoeff := by
    rw [hlcP]
    by_contra hc
    exact hlc ((PadicInt.norm_int_lt_one_iff_dvd _).mp (PadicInt.not_isUnit_iff.mp hc))
  have hqmonic : (g.map (algebraMap ℚ ℚ_[ℓ])).Monic := hg.map _
  have hmapP : P.map (algebraMap ℤ_[ℓ] ℚ_[ℓ]) = F.map (Int.castRingHom ℚ_[ℓ]) := by
    rw [hPdef, Polynomial.map_map,
      RingHom.ext_int ((algebraMap ℤ_[ℓ] ℚ_[ℓ]).comp (Int.castRingHom ℤ_[ℓ]))
        (Int.castRingHom ℚ_[ℓ])]
  have hqdvd : g.map (algebraMap ℚ ℚ_[ℓ]) ∣ P.map (algebraMap ℤ_[ℓ] ℚ_[ℓ]) := by
    rw [hmapP]
    have h := Polynomial.map_dvd (algebraMap ℚ ℚ_[ℓ]) hdvd
    rwa [Polynomial.map_map,
      RingHom.ext_int ((algebraMap ℚ ℚ_[ℓ]).comp (Int.castRingHom ℚ)) (Int.castRingHom ℚ_[ℓ])] at h
  obtain ⟨Q, hQmonic, hQdeg, hQdvd⟩ :=
    Polynomial.exists_monic_dvd_of_isUnit_leadingCoeff hu hqmonic hqdvd
  refine ⟨Q.map (PadicInt.toZMod), hQmonic.map _, ?_, ?_⟩
  · rw [hQmonic.natDegree_map, hQdeg, hg.natDegree_map]
  · have hmapZ : F.map (Int.castRingHom (ZMod ℓ)) = P.map (PadicInt.toZMod (p := ℓ)) := by
      rw [hPdef, Polynomial.map_map,
        RingHom.ext_int ((PadicInt.toZMod (p := ℓ)).comp (Int.castRingHom ℤ_[ℓ]))
          (Int.castRingHom (ZMod ℓ))]
    rw [hmapZ]
    exact Polynomial.map_dvd _ hQdvd

end
