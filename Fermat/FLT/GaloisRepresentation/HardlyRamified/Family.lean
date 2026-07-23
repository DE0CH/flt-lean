/-
Copyright (c) 2025 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard
-/
module

public import Fermat.FLT.GaloisRepresentation.HardlyRamified.Defs
public import Fermat.FLT.Deformations.RepresentationTheory.GaloisRepFamily
import Mathlib.Algebra.Field.ULift
import Mathlib.Topology.Algebra.IntermediateField
import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Mathlib.LinearAlgebra.Charpoly.BaseChange
-- `IsIntegralClosure.finite`: module-finiteness of the integral closure of a
-- Noetherian integrally closed domain in a finite separable extension of its
-- fraction field (the concrete coefficient rings of the realization stratum)
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
-- `PadicInt.compactSpace`: compactness of `ℤ_ℓ`, used to identify the
-- subspace topology on the concrete rings of integers with the module topology
import Mathlib.NumberTheory.Padics.ProperSpace

/-!
# Hardly ramified representations in compatible families

We show that the property of being hardly ramified is preserved within
compatible families of Galois representations.

VENDORING CHANGES: (1) the conclusion of `mem_isCompatible` (originally
an anonymous `∃`-package) is extracted into the named predicate
`IsInHardlyRamifiedFamily`, so that downstream nodes (the compatibility
bookkeeping in `Lift.lean`) can take it as a hypothesis without
duplicating the package verbatim. (2) 2026-07-16: the package is
STRENGTHENED by recording that the coefficient rings embed into the
`p`-adic algebraic closures (`Function.Injective (algebraMap ...)`, two
occurrences below): the upstream statement omits this, but the charpoly
descent in `residual_charFrob_eq_of_family` requires it and it holds for
the intended coefficient rings (subrings of `ℚ̄_p`). This strengthens
what B6b must prove, deliberately.

AUDIT (2026-07-22): **the hypotheses of `mem_isCompatible` do not rule
out coefficient rings of characteristic `p`, and for those the
conclusion is false** — take `p = 3`, `R = 𝔽₃` (with the discrete =
`ℤ₃`-module topology; it is a local domain, module-finite over `ℤ₃`)
and `ρ = 1 ⊕ χ̄₃` acting diagonally on `Fin 2 → 𝔽₃`: this `ρ` is hardly
ramified (cyclotomic determinant, unramified outside `{2,3}`, flat at
`3` via `μ₃ ⊕ ℤ/3`, tame at `2` with quotient character `χ̄₃|_{G₂}`,
which is unramified with square one), yet the membership clause of
`IsInHardlyRamifiedFamily` demands `∃ (_ : Algebra R ℚ̄_p)` — and there
is no ring hom `𝔽₃ →+* ℚ̄₃` at all (`(1 : ℚ̄₃)` does not have additive
order `3`). The same defect is present in the upstream FLT project's
statement. The intended reading ("`R` is the integers in a finite
extension of `ℚ_p`") forces `algebraMap ℤ_[p] R` to be injective, and
the sole consumer (`residual_charFrob_eq` in `Lift.lean`) instantiates
`R` with such a ring.

RESTATEMENT (2026-07-22, coordinated with the call site in
`Lift.lean`): `mem_isCompatible` now takes the extra hypothesis
`hZinj : Function.Injective (algebraMap ℤ_[p] R)`, which repairs the
defect. The previous revision quarantined exactly this statement as an
inner *sorried step* `hZinj` of the proof skeleton (recording that it
was false-as-stated in full generality); that sorry is superseded by —
and deleted in favour of — the hypothesis. At the sole call site
(`residual_charFrob_eq` in `Lift.lean`) the hypothesis is discharged
by the `algebraMap_injective` field of `HardlyRamifiedLift`, which
holds for the intended `L.O` (integers in a finite extension of
`ℚ_p`). From `hZinj` the coefficient embedding `R ↪ ℚ̄_p` is *proven*
(torsion-free + integral ⇒ `IsAlgClosed.lift`; injectivity by
contracting the kernel to `ℤ_[p]`; continuity from the module
topology). The remaining sorried step `hcore` is the true
automorphy/modularity content of B6b.
-/

@[expose] public section

namespace GaloisRepresentation.IsHardlyRamified

open GaloisRepresentation IsDedekindDomain

open scoped TensorProduct

universe u v

-- let ρ : G_ℚ → GL_2(R) be a representation, where R is the integers in a finite
-- extension of ℚ_p
variable {p : ℕ} (hpodd : Odd p) [hp : Fact p.Prime]
    {R : Type u} [CommRing R] [Algebra ℤ_[p] R] [IsDomain R]
    [Module.Finite ℤ_[p] R] [TopologicalSpace R] [IsTopologicalRing R]
    [IsLocalRing R] [IsModuleTopology ℤ_[p] R]
    {V : Type v} [AddCommGroup V] [Module R V] [Module.Finite R V]
    [Module.Free R V] (hv : Module.rank R V = 2) {ρ : GaloisRep ℚ R V}

/-- `ρ` lives in a compatible family of Galois representations all of whose
odd-residue-characteristic members are hardly ramified, and `ρ` is (the base
extension of) one of the members. (VENDORING CHANGE: this named predicate is
the conclusion of `mem_isCompatible`, extracted verbatim from the FLT
project's statement.) -/
def IsInHardlyRamifiedFamily (ρ : GaloisRep ℚ R V) : Prop :=
    -- there's a family σ of 2-dimensional representations of Γ_ℚ
    -- parametrised by maps from a number field M → ℚ_p-bar
    ∃ (E : Type v) (_ : Field E) (_ : NumberField E) (σ : GaloisRepFamily ℚ E 2),
    -- which are compatible, and
    σ.isCompatible ∧
    -- are "hardly ramified" for ℓ>2,
    (∀ {ℓ : ℕ} (hℓ : Fact ℓ.Prime) (hℓodd : Odd ℓ) (φ : E →+* AlgebraicClosure ℚ_[ℓ]),
      -- by which we mean that for a representation σ_φ in the family,
      -- there's a hardly-ramified representation `τ` to GL_2(A)
      -- for A a module-finite free ℤ_ℓ-algebra
      ∃ (A : Type u) (_ : CommRing A) (_ : TopologicalSpace A) (_ : IsTopologicalRing A)
        (_ : IsLocalRing A) (_ : Algebra ℤ_[ℓ] A) (_ : Module.Finite ℤ_[ℓ] A)
        (_ : Module.Free ℤ_[ℓ] A) (_ : IsDomain A) (_ : Algebra A (AlgebraicClosure ℚ_[ℓ]))
        (_ : IsScalarTower ℤ_[ℓ] A (AlgebraicClosure ℚ_[ℓ])) (_ : IsModuleTopology ℤ_[ℓ] A)
        (_ : ContinuousSMul A (AlgebraicClosure ℚ_[ℓ]))
        -- VENDORING CHANGE (2026-07-16): the coefficient ring embeds into
        -- `ℚ̄_ℓ` — recorded explicitly because the charpoly descent in the
        -- compatibility bookkeeping (`residual_charFrob_eq_of_family`)
        -- needs it, and it is true for the intended `A` (a subring of
        -- `ℚ̄_ℓ`). The upstream statement omits it.
        (_ : Function.Injective (algebraMap A (AlgebraicClosure ℚ_[ℓ])))
        (W : Type v) (_ : AddCommGroup W) (_ : Module A W) (_ : Module.Finite A W)
        (_ : Module.Free A W) (hW : Module.rank A W = 2)
        (τ : GaloisRep ℚ A W)
        (r : AlgebraicClosure ℚ_[ℓ] ⊗[A] W ≃ₗ[AlgebraicClosure ℚ_[ℓ]]
          Fin 2 → AlgebraicClosure ℚ_[ℓ]),
        IsHardlyRamified hℓodd hW τ ∧
        -- whose base extension to GL_2(ℚ_p-bar) is φ_σ
        (τ.baseChange (AlgebraicClosure ℚ_[ℓ])).conj r = σ hℓ φ) ∧
    -- and `ρ` is part of the family.
    (∃ (_ : Algebra R (AlgebraicClosure ℚ_[p])) (_ : ContinuousSMul R (AlgebraicClosure ℚ_[p]))
      -- VENDORING CHANGE (2026-07-16): same injectivity strengthening as
      -- for the family members above, for the same reason.
      (_ : Function.Injective (algebraMap R (AlgebraicClosure ℚ_[p])))
      (ψ : E →+* AlgebraicClosure ℚ_[p])
      (r' : AlgebraicClosure ℚ_[p] ⊗[R] V ≃ₗ[AlgebraicClosure ℚ_[p]]
        Fin 2 → AlgebraicClosure ℚ_[p]),
      (ρ.baseChange (AlgebraicClosure ℚ_[p])).conj r' = σ hp ψ)

omit [IsDomain R] [IsTopologicalRing R] [IsLocalRing R] [IsModuleTopology ℤ_[p] R] in
/-- **Integrality stratum of the eigensystem** (PROVEN): the
coefficients of the Frobenius characteristic polynomials of `ρ`, pushed
into `ℚ̄_p`, are integral over `ℤ_p` — integrality stated with respect
to the composite `ℤ_[p] → R → ℚ̄_p`, so that no compatibility
(`IsScalarTower`) between the arbitrary coefficient embedding
`Algebra R ℚ̄_p` and the two `ℤ_[p]`-structures needs to be assumed
(at the intended coefficient rings the composite IS the canonical
`algebraMap ℤ_[p] ℚ̄_p`). This is the formal half of the eigensystem
stratum: `R` is module-finite over `ℤ_[p]`, so every element of `R` —
in particular every Frobenius trace and determinant — is integral over
`ℤ_[p]`, and integrality pushes forward along ring homomorphisms. -/
theorem charFrob_coeff_isIntegralElem
    [Algebra R (AlgebraicClosure ℚ_[p])]
    (v : HeightOneSpectrum (NumberField.RingOfIntegers ℚ)) (n : ℕ) :
    ((algebraMap R (AlgebraicClosure ℚ_[p])).comp (algebraMap ℤ_[p] R)).IsIntegralElem
      (((ρ.charFrob v).map (algebraMap R (AlgebraicClosure ℚ_[p]))).coeff n) := by
  obtain ⟨P, hPmonic, hPeval⟩ := IsIntegral.of_finite ℤ_[p] ((ρ.charFrob v).coeff n)
  refine ⟨P, hPmonic, ?_⟩
  rw [Polynomial.coeff_map, ← Polynomial.hom_eval₂, hPeval, map_zero]

/-- Every finite place of `ℚ` is the place of a rational prime (PROVEN):
the surjectivity half of the primes ↔ places dictionary, needed to
convert the prime-indexed unramifiedness field of `IsHardlyRamified`
into the place-indexed unramifiedness that
`GaloisRepFamily.isCompatible` consumes. (Moved above the eigensystem
strata 2026-07-23: the coefficient-field assembly consumes it too.) -/
lemma exists_prime_toHeightOneSpectrumRingOfIntegersRat
    (v : HeightOneSpectrum (NumberField.RingOfIntegers ℚ)) :
    ∃ (q : ℕ) (hq : q.Prime), v = hq.toHeightOneSpectrumRingOfIntegersRat := by
  let E := Rat.ringOfIntegersEquiv.symm.heightOneSpectrum
  obtain ⟨g, hg⟩ := (IsPrincipalIdealRing.principal (E.symm v).asIdeal).principal
  have hg0 : g ≠ 0 := by
    rintro rfl
    exact (E.symm v).ne_bot (by simpa using hg)
  have hg' : (E.symm v).asIdeal = Ideal.span {g} := hg
  have hprime : Prime g := (Ideal.span_singleton_prime hg0).mp (hg' ▸ (E.symm v).isPrime)
  refine ⟨g.natAbs, Int.prime_iff_natAbs_prime.mp hprime, ?_⟩
  have hweq : E.symm v =
      (Int.prime_iff_natAbs_prime.mp hprime).toHeightOneSpectrumInt := by
    ext1
    show (E.symm v).asIdeal = Ideal.span {(g.natAbs : ℤ)}
    rw [Int.span_natAbs, hg']
  have hv : v = E (E.symm v) := (E.apply_symm_apply v).symm
  rw [hv, hweq]
  rfl

omit [IsDomain R] [IsTopologicalRing R] [IsLocalRing R] [Module.Finite ℤ_[p] R] in
/-- **Composite = canonical** (PROVEN): the composite `ℤ_[p] → R → ℚ̄_p`
of the structure map with any *continuous* coefficient embedding is the
canonical map `ℤ_[p] → ℚ̄_p`. Indeed `ℕ` is dense in `ℤ_[p]` and both
sides are continuous ring homomorphisms agreeing on `ℕ` (the structure
map is continuous because `R` carries the `ℤ_[p]`-module topology).
This dissolves — for the continuous embeddings the eigensystem strata
actually receive — the composite-vs-canonical caveat recorded in the
docstring of `charFrob_coeff_isIntegralElem`. -/
lemma algebraMap_comp_algebraMap_padicInt
    [Algebra R (AlgebraicClosure ℚ_[p])]
    [ContinuousSMul R (AlgebraicClosure ℚ_[p])] :
    (algebraMap R (AlgebraicClosure ℚ_[p])).comp (algebraMap ℤ_[p] R) =
      algebraMap ℤ_[p] (AlgebraicClosure ℚ_[p]) := by
  have hcontZ : Continuous (algebraMap ℤ_[p] R) := continuous_algebraMap _ _
  have hcontR : Continuous (algebraMap R (AlgebraicClosure ℚ_[p])) :=
    continuous_algebraMap _ _
  have hcontC : Continuous (algebraMap ℤ_[p] (AlgebraicClosure ℚ_[p])) :=
    (continuous_algebraMap ℚ_[p] _).comp continuous_subtype_val
  exact DFunLike.coe_injective <|
    PadicInt.denseRange_natCast.equalizer (hcontR.comp hcontZ) hcontC
      (funext fun n => by simp)

omit [IsDomain R] [IsTopologicalRing R] [IsLocalRing R] in
/-- **`p`-adic confinement stratum of the eigensystem** (PROVEN): ALL
Frobenius-charpoly coefficients of `ρ`, pushed into `ℚ̄_p` along a
continuous coefficient embedding, lie in a single intermediate field
finite-dimensional over **`ℚ_p`** (not `ℚ`!). Formal content: `R` is
module-finite over `ℤ_[p]`, so its image in `ℚ̄_p` is spanned over
`ℤ_[p]` by finitely many `ℤ_[p]`-integral elements, and adjoining those
to `ℚ_p` gives a finite extension containing the image of `R`, hence
every coefficient. This is the exact formal complement of the sorried
trace-field leaf below: over `ℚ_p` the confinement is free; over `ℚ`
it is automorphy. -/
theorem exists_finiteDimensional_padic_coeff_field
    [Algebra R (AlgebraicClosure ℚ_[p])]
    [ContinuousSMul R (AlgebraicClosure ℚ_[p])] :
    ∃ (K : IntermediateField ℚ_[p] (AlgebraicClosure ℚ_[p]))
      (_ : FiniteDimensional ℚ_[p] K),
      ∀ (v : HeightOneSpectrum (NumberField.RingOfIntegers ℚ)) (n : ℕ),
        ((ρ.charFrob v).map (algebraMap R (AlgebraicClosure ℚ_[p]))).coeff n ∈ K := by
  classical
  have htow := algebraMap_comp_algebraMap_padicInt (p := p) (R := R)
  obtain ⟨s, hs⟩ : (⊤ : Submodule ℤ_[p] R).FG := Module.finite_def.mp inferInstance
  -- the image of `R` consists of `ℤ_[p]`-integral elements
  have himg : ∀ r : R, IsIntegral ℤ_[p] (algebraMap R (AlgebraicClosure ℚ_[p]) r) := by
    intro r
    obtain ⟨P, hPmonic, hPeval⟩ := IsIntegral.of_finite ℤ_[p] r
    refine ⟨P, hPmonic, ?_⟩
    rw [← htow, ← Polynomial.hom_eval₂, hPeval, map_zero]
  refine ⟨IntermediateField.adjoin ℚ_[p]
      (algebraMap R (AlgebraicClosure ℚ_[p]) '' ↑s), ?_, ?_⟩
  · -- finite-dimensionality: finitely many integral (hence algebraic) generators
    haveI : Finite ↥(algebraMap R (AlgebraicClosure ℚ_[p]) '' ↑s) :=
      (s.finite_toSet.image _).to_subtype
    exact IntermediateField.finiteDimensional_adjoin fun x hx => by
      obtain ⟨r, -, rfl⟩ := hx
      exact (himg r).tower_top
  · -- membership: the whole image of `R` lies in the adjoined field
    have hmemR : ∀ r : R, algebraMap R (AlgebraicClosure ℚ_[p]) r ∈
        IntermediateField.adjoin ℚ_[p]
          (algebraMap R (AlgebraicClosure ℚ_[p]) '' ↑s) := by
      intro r
      have hr : r ∈ Submodule.span ℤ_[p] (↑s : Set R) := by
        rw [hs]; exact Submodule.mem_top
      induction hr using Submodule.span_induction with
      | mem x hx => exact IntermediateField.subset_adjoin _ _ ⟨x, hx, rfl⟩
      | zero => rw [map_zero]; exact zero_mem _
      | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
      | smul c x _ hx =>
        rw [Algebra.smul_def, map_mul]
        refine mul_mem ?_ hx
        have hc : algebraMap R (AlgebraicClosure ℚ_[p]) (algebraMap ℤ_[p] R c) =
            algebraMap ℤ_[p] (AlgebraicClosure ℚ_[p]) c := RingHom.congr_fun htow c
        rw [hc, IsScalarTower.algebraMap_eq ℤ_[p] ℚ_[p] (AlgebraicClosure ℚ_[p]),
          RingHom.comp_apply]
        exact IntermediateField.algebraMap_mem _ _
    intro v n
    rw [Polynomial.coeff_map]
    exact hmemR _

set_option backward.isDefEq.respectTransparency false in
open scoped algebraMap in
/-- **The completed valuation of `p` at the place of `q ≠ p` is `1`**
(PROVEN): the general-`p` port of the `3`-adic
`valued_natCast_adicCompletionIntegers_eq_one` of
`Fermat.FLT.Deformations.RepresentationTheory.GaloisRep`; the chain
`q ∤ p → p ∈ primeCompl → intValuation p = 1 → Valued.v (p : Kᵥ) = 1`,
with the coprimality now coming from `Nat.prime_dvd_prime_iff_eq`
instead of the template's `omega` on `5 ≤ p`. -/
lemma valued_natCast_adicCompletionIntegers_eq_one_of_ne {q : ℕ}
    (hq : q.Prime) (hqp : q ≠ p) :
    Valued.v ((((p : ℕ) :
        HeightOneSpectrum.adicCompletionIntegers ℚ
          hq.toHeightOneSpectrumRingOfIntegersRat)) :
      HeightOneSpectrum.adicCompletion ℚ
        hq.toHeightOneSpectrumRingOfIntegersRat) = 1 := by
  set v := hq.toHeightOneSpectrumRingOfIntegersRat
  have hcompl : ((p : ℕ) : NumberField.RingOfIntegers ℚ) ∈
      v.asIdeal.primeCompl := by
    intro hmem
    have hdvd := (Nat.Prime.mem_toHeightOneSpectrumRingOfIntegersRat_asIdeal
      hq _).mp hmem
    rw [map_natCast, Int.natCast_dvd_natCast] at hdvd
    exact hqp ((Nat.prime_dvd_prime_iff_eq hq hp.out).mp hdvd)
  have hint1 : HeightOneSpectrum.intValuation v
      ((p : ℕ) : NumberField.RingOfIntegers ℚ) = 1 :=
    (HeightOneSpectrum.intValuation_eq_one_iff_mem_primeCompl
      v _).mpr hcompl
  have hK := (HeightOneSpectrum.valuedAdicCompletion_eq_valuation
      (v := v) (K := ℚ) (((p : ℕ) : NumberField.RingOfIntegers ℚ))).trans
    ((HeightOneSpectrum.valuation_of_algebraMap
      (v := v) (K := ℚ) (((p : ℕ) : NumberField.RingOfIntegers ℚ))).trans hint1)
  have hbridge : ((((p : ℕ) :
        HeightOneSpectrum.adicCompletionIntegers ℚ v)) :
      HeightOneSpectrum.adicCompletion ℚ v) =
      @algebraMap _ _ _ _
        (HeightOneSpectrum.instAlgebraAdicCompletion
          (NumberField.RingOfIntegers ℚ) ℚ v)
        (((p : ℕ) : NumberField.RingOfIntegers ℚ)) := by
    rw [map_natCast]
    simp only [_root_.algebraMap.coe_natCast]
  rw [hbridge]
  exact hK

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1000000 in
/-- **The arithmetic Frobenius at `q ≠ p` raises `p`-power roots of
unity to the `q`-th power** (PROVEN): the general-`p` port of the
`3`-adic `adicArithFrob_rootsOfUnity_pow` of
`Fermat.FLT.Deformations.RepresentationTheory.GaloisRep`: at a prime
`q ≠ p`, the `p`-power roots of unity are unramified, the arithmetic
Frobenius reduces to `x ↦ x^q` on the residue field, and roots of unity
of order coprime to `q` inject into the residue field, so the action is
exactly `ζ ↦ ζ^q`. Stated in the `modularCyclotomicCharacter.unique`
hypothesis shape. -/
theorem adicArithFrob_rootsOfUnity_pow_of_ne {q : ℕ}
    (hq : q.Prime) (hqp : q ≠ p) (n : ℕ) :
    ∀ t ∈ rootsOfUnity (p ^ n) (AlgebraicClosure ℚ),
      ((Field.absoluteGaloisGroup.map (algebraMap ℚ
        (HeightOneSpectrum.adicCompletion ℚ
          hq.toHeightOneSpectrumRingOfIntegersRat))
        (Field.AbsoluteGaloisGroup.adicArithFrob
          hq.toHeightOneSpectrumRingOfIntegersRat)).toRingEquiv) t =
        t ^ ((q : ZMod (p ^ n)).val) := by
  intro t ht
  classical
  -- the `q` of the Frobenius specification is the residue cardinality
  have hcard := GaloisRepresentation.natCard_residue_quotient_toHeightOneSpectrum hq
  set v := hq.toHeightOneSpectrumRingOfIntegersRat
  set f := algebraMap ℚ (HeightOneSpectrum.adicCompletion ℚ v)
  -- the root of unity, its power identity, and its image under the chosen
  -- embedding of algebraic closures
  have htL : ((t : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ) ^ (p ^ n)
      = 1 := by
    have h1 := (mem_rootsOfUnity _ _).mp ht
    calc ((t : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ) ^ (p ^ n)
        = ((t ^ (p ^ n) : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ) := by
          push_cast; rfl
      _ = 1 := by rw [h1]; rfl
  set ζ : AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ v) :=
    AlgebraicClosure.map f ((t : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ)
    with hζdef
  have hζpow : ζ ^ (p ^ n) = 1 := by
    rw [hζdef, ← map_pow, htL, map_one]
  -- the image is integral over the completion integers (it kills `X^{pⁿ}-1`)
  have hint : IsIntegral
      (HeightOneSpectrum.adicCompletionIntegers ℚ v) ζ := by
    refine ⟨Polynomial.X ^ (p ^ n) - 1, ?_, ?_⟩
    · have := Polynomial.monic_X_pow_sub_C
        (R := HeightOneSpectrum.adicCompletionIntegers ℚ v)
        (1 : _) (n := p ^ n) (pow_ne_zero _ hp.out.pos.ne')
      simpa [Polynomial.C_1] using this
    · simp [Polynomial.eval₂_sub, hζpow]
  set ζ' : IntegralClosure
      (HeightOneSpectrum.adicCompletionIntegers ℚ v)
      (AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ v)) :=
    ⟨ζ, hint⟩ with hζ'def
  have hζ'pow : ζ' ^ (p ^ n) = 1 := by
    apply Subtype.ext
    push_cast [hζ'def]
    exact hζpow
  -- `p` is a unit at the `q`-place (`q ≠ p`), so `pⁿ` avoids the maximal ideal
  have hpnotin : ((p : ℕ) ^ n : IntegralClosure
      (HeightOneSpectrum.adicCompletionIntegers ℚ v)
      (AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ v))) ∉
      IsLocalRing.maximalIdeal _ := by
    -- `p ∉ (q)`, so `p` is a unit in `𝒪ᵥ`, hence in the integral closure
    have hunit : IsUnit ((p : ℕ) :
        HeightOneSpectrum.adicCompletionIntegers ℚ v) := by
      by_contra hnu
      have hmem := (IsLocalRing.mem_maximalIdeal _).mpr hnu
      have hlt := (HeightOneSpectrum.mem_completionIdeal_iff
        (K := ℚ) (v := v) _).mp hmem
      have h1 := valued_natCast_adicCompletionIntegers_eq_one_of_ne hq hqp
      exact absurd (lt_of_lt_of_le hlt h1.symm.le) (lt_irrefl _)
    have hunitIC : IsUnit (((p : ℕ) ^ n) : IntegralClosure
        (HeightOneSpectrum.adicCompletionIntegers ℚ v)
        (AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ v))) := by
      have h1 := hunit.map (algebraMap
        (HeightOneSpectrum.adicCompletionIntegers ℚ v)
        (IntegralClosure
          (HeightOneSpectrum.adicCompletionIntegers ℚ v)
          (AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ v))))
      rw [map_natCast] at h1
      exact h1.pow n
    intro hmem
    exact ((IsLocalRing.mem_maximalIdeal _).mp hmem) hunitIC
  -- the Frobenius specification on the integral closure
  have hfrob := AlgHom.IsArithFrobAt.apply_of_pow_eq_one
    (Field.AbsoluteGaloisGroup.isArithFrobAt_adicArithFrob (v := v))
    hζ'pow (by exact_mod_cast hpnotin)
  rw [hcard] at hfrob
  -- read the specification off in `Kᵥᵃˡᵍ`
  have hfrobK : Field.AbsoluteGaloisGroup.adicArithFrob v ζ = ζ ^ q := by
    have h1 := hfrob
    rw [MulSemiringAction.toAlgHom_apply] at h1
    have h2 := congrArg Subtype.val h1
    rw [IntegralClosure.coe_smul] at h2
    have h3 : ((⟨ζ, hint⟩ : IntegralClosure _ _) ^ q).1 = ζ ^ q :=
      SubmonoidClass.coe_pow _ _
    simpa [hζ'def, AlgEquiv.smul_def] using h2.trans h3
  -- globalize through the chosen embedding, which is injective
  have hsq := Field.absoluteGaloisGroup.lift_map f
    (Field.AbsoluteGaloisGroup.adicArithFrob v)
    ((t : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ)
  have hmain : (Field.absoluteGaloisGroup.map f
      (Field.AbsoluteGaloisGroup.adicArithFrob v))
      ((t : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ) =
      ((t : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ) ^ q := by
    apply (AlgebraicClosure.map f).injective
    rw [hsq, map_pow]
    exact hfrobK
  -- the goal's `toRingEquiv` application is the automorphism application
  show (Field.absoluteGaloisGroup.map f
      (Field.AbsoluteGaloisGroup.adicArithFrob v))
      ((t : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ) = _
  rw [hmain]
  -- the exponent-mod juggle: `t^q = t^(q mod pⁿ)` since `t^{pⁿ} = 1`
  haveI : NeZero (p ^ n) := ⟨pow_ne_zero _ hp.out.pos.ne'⟩
  have hval : ((q : ZMod (p ^ n))).val = q % p ^ n := ZMod.val_natCast _ q
  conv_lhs => rw [show q = p ^ n * (q / p ^ n) + q % p ^ n from
    (Nat.div_add_mod q (p ^ n)).symm]
  rw [pow_add, pow_mul, htL, one_pow, one_mul, hval]

/-- **The `p`-adic cyclotomic character at an arithmetic Frobenius**
(PROVEN, general-`p` port of the `3`-adic
`cyclotomicCharacter_adicArithFrob` of
`Fermat.FLT.Deformations.RepresentationTheory.GaloisRep`, derived from
the ported roots-of-unity action `adicArithFrob_rootsOfUnity_pow_of_ne`
by `p`-adic continuity: `PadicInt.ext_of_toZModPow` reduces the
identity to every level `pⁿ`, where `cyclotomicCharacter.toZModPow` and
`modularCyclotomicCharacter.unique` identify the character value with
`q` from the action): at a rational prime `q ≠ p` the `p`-adic
cyclotomic character takes the value `q` on the global image of the
arithmetic Frobenius at `q`. Split off from
the eigensystem finiteness leaf so that the DETERMINANT coefficient of
the Frobenius charpolys becomes rational by PROVEN bookkeeping
(`charFrob_coeff_zero_eq_natCast`) and only the TRACE coefficient
retains automorphy content. -/
theorem cyclotomicCharacter_adicArithFrob_natCast
    {q : ℕ} (hq : q.Prime) (hqp : q ≠ p) :
    ((cyclotomicCharacter (AlgebraicClosure ℚ) p
      ((Field.absoluteGaloisGroup.map (algebraMap ℚ
        (HeightOneSpectrum.adicCompletion ℚ
          hq.toHeightOneSpectrumRingOfIntegersRat))
        (Field.AbsoluteGaloisGroup.adicArithFrob
          hq.toHeightOneSpectrumRingOfIntegersRat)).toRingEquiv) : ℤ_[p]ˣ) :
      ℤ_[p]) = (q : ℤ_[p]) := by
  rw [← PadicInt.ext_of_toZModPow]
  intro n
  rw [map_natCast, cyclotomicCharacter.toZModPow]
  exact (modularCyclotomicCharacter.unique
    (hn := HasEnoughRootsOfUnity.natCard_rootsOfUnity (AlgebraicClosure ℚ)
      (p ^ n))
    _ _ (adicArithFrob_rootsOfUnity_pow_of_ne hq hqp n)).symm

omit [IsDomain R] [Module.Finite ℤ_[p] R] [IsModuleTopology ℤ_[p] R] in
/-- **Rationality of the determinant coefficient** (PROVEN): away from
`p`, the constant
coefficient of the mapped Frobenius charpoly of a hardly ramified
representation is the rational integer `q` — by the
cyclotomic-determinant condition of `IsHardlyRamified` together with
`det = (-1)² · coeff 0` for the rank-`2` charpoly, evaluated through
the (also PROVEN) `cyclotomicCharacter_adicArithFrob_natCast`.
Consequence: the only
coefficient of the Frobenius charpolys carrying automorphy content is
the trace (`coeff 1`); see the DECOMPOSED note on
`exists_finiteDimensional_coeff_field`. -/
lemma charFrob_coeff_zero_eq_natCast
    [Algebra R (AlgebraicClosure ℚ_[p])]
    (hρ : IsHardlyRamified hpodd hv ρ)
    {q : ℕ} (hq : q.Prime) (hqp : q ≠ p) :
    ((ρ.charFrob hq.toHeightOneSpectrumRingOfIntegersRat).map
      (algebraMap R (AlgebraicClosure ℚ_[p]))).coeff 0 =
      (q : AlgebraicClosure ℚ_[p]) := by
  have hfinrank : Module.finrank R V = 2 := Module.finrank_eq_of_rank_eq hv
  -- the constant coefficient of a rank-2 charpoly is the determinant
  have hdet := LinearMap.det_eq_sign_charpoly_coeff
    (ρ.toLocal hq.toHeightOneSpectrumRingOfIntegersRat
      (Field.AbsoluteGaloisGroup.adicArithFrob
        hq.toHeightOneSpectrumRingOfIntegersRat))
  rw [hfinrank, neg_one_sq, one_mul] at hdet
  -- the determinant of the global Frobenius image is `q`, by the
  -- cyclotomic-determinant condition and the sorried evaluation leaf
  have hcyclo := hρ.det (Field.absoluteGaloisGroup.map (algebraMap ℚ
    (HeightOneSpectrum.adicCompletion ℚ hq.toHeightOneSpectrumRingOfIntegersRat))
    (Field.AbsoluteGaloisGroup.adicArithFrob hq.toHeightOneSpectrumRingOfIntegersRat))
  rw [GaloisRep.det_apply, cyclotomicCharacter_adicArithFrob_natCast hq hqp,
    map_natCast] at hcyclo
  -- bridge the local-Frobenius determinant to the global one (the two
  -- spellings differ only in the subsingleton `Algebra ℚ _` instance)
  have hdetq : LinearMap.det (ρ.toLocal hq.toHeightOneSpectrumRingOfIntegersRat
      (Field.AbsoluteGaloisGroup.adicArithFrob
        hq.toHeightOneSpectrumRingOfIntegersRat)) = (q : R) := by
    rw [GaloisRep.toLocal_apply]
    convert hcyclo using 2
    congr 1
    congr 1
    congr 1
    exact Subsingleton.elim _ _
  rw [Polynomial.coeff_map,
    show ρ.charFrob hq.toHeightOneSpectrumRingOfIntegersRat =
      (ρ.toLocal hq.toHeightOneSpectrumRingOfIntegersRat
        (Field.AbsoluteGaloisGroup.adicArithFrob
          hq.toHeightOneSpectrumRingOfIntegersRat)).charpoly from rfl,
    ← hdet, hdetq, map_natCast]

/-! ### Block-triangular linear algebra for the reducible branch

The mathlib pin has `LinearMap.det_eq_det_mul_det` (the determinant of
an endomorphism preserving a submodule is the product of the
determinants of the restriction and of the induced quotient map) but
no characteristic-polynomial analogue, and no API for evaluating the
`1`-dimensional blocks. The reducible-branch trace analysis below
reads the trace coefficient off the factored charpoly, so we prove the
charpoly analogue here by the same `Module.Basis.sumQuot` block-matrix
computation, together with the `1`-dimensional evaluation
`charpoly = X - C (trace)`. -/

open Module.Basis in
/-- **Block-triangular characteristic polynomial** (PROVEN): if the
endomorphism `e` preserves the submodule `W₀`, its characteristic
polynomial factors as the product of the characteristic polynomials of
the restriction to `W₀` and of the induced endomorphism of `V₀ ⧸ W₀`.
Charpoly analogue of the pin's `LinearMap.det_eq_det_mul_det`, proven
by the same block-matrix computation through the mixed basis
`Module.Basis.sumQuot` and `Matrix.charpoly_fromBlocks_zero₂₁`. -/
theorem _root_.LinearMap.charpoly_eq_charpoly_restrict_mul_charpoly_mapQ
    {R₀ V₀ : Type*} [CommRing R₀] [AddCommGroup V₀] [Module R₀ V₀]
    [Module.Finite R₀ V₀] [Module.Free R₀ V₀]
    (W₀ : Submodule R₀ V₀) [Module.Free R₀ W₀] [Module.Finite R₀ W₀]
    [Module.Free R₀ (V₀ ⧸ W₀)] [Module.Finite R₀ (V₀ ⧸ W₀)]
    (e : V₀ →ₗ[R₀] V₀) (he : W₀ ≤ W₀.comap e) :
    e.charpoly = (e.restrict he).charpoly * (W₀.mapQ W₀ e he).charpoly := by
  classical
  let m := Module.Free.ChooseBasisIndex R₀ W₀
  let bW : Module.Basis m R₀ W₀ := Module.Free.chooseBasis R₀ W₀
  let n := Module.Free.ChooseBasisIndex R₀ (V₀ ⧸ W₀)
  let bQ : Module.Basis n R₀ (V₀ ⧸ W₀) := Module.Free.chooseBasis R₀ (V₀ ⧸ W₀)
  let b := sumQuot bW bQ
  let A : Matrix m m R₀ := LinearMap.toMatrix bW bW (e.restrict he)
  let B : Matrix m n R₀ := Matrix.of fun i l ↦
    ((sumQuot bW bQ).repr (e ((sumQuot bW bQ) (Sum.inr l)))) (Sum.inl i)
  let D : Matrix n n R₀ := LinearMap.toMatrix bQ bQ (W₀.mapQ W₀ e he)
  suffices LinearMap.toMatrix b b e = Matrix.fromBlocks A B 0 D by
    rw [← e.charpoly_toMatrix b, this, Matrix.charpoly_fromBlocks_zero₂₁,
      (e.restrict he).charpoly_toMatrix bW, (W₀.mapQ W₀ e he).charpoly_toMatrix bQ]
  ext u v
  cases u with
  | inl i =>
    cases v with
    | inl k =>
      simp only [b, sumQuot_inl, Matrix.fromBlocks_apply₁₁, A, LinearMap.toMatrix_apply]
      apply sumQuot_repr_inl_of_mem
    | inr l => simp [b, LinearMap.toMatrix_apply, Matrix.fromBlocks_apply₁₂, B]
  | inr j =>
    cases v with
    | inl k =>
      suffices W₀.mkQ (e (bW k)) = 0 by simp [LinearMap.toMatrix_apply, b, this]
      rw [← LinearMap.mem_ker, Submodule.ker_mkQ]
      exact he (Submodule.coe_mem (bW k))
    | inr l =>
      simp only [LinearMap.toMatrix_apply, sumQuot_repr_inr,
        Matrix.fromBlocks_apply₂₂, b, D]
      rw [← sumQuot_inr bW bQ l, W₀.mapQ_apply]
      simp

/-- **`1`-dimensional characteristic polynomial** (PROVEN): on a
`1`-dimensional space every endomorphism has characteristic polynomial
`X - C (trace)`. Used to evaluate the two blocks of
`LinearMap.charpoly_eq_charpoly_restrict_mul_charpoly_mapQ` when the
invariant submodule is a line in a plane. -/
theorem _root_.LinearMap.charpoly_eq_X_sub_C_trace_of_finrank_eq_one
    {K₀ V₀ : Type*} [Field K₀] [AddCommGroup V₀] [Module K₀ V₀]
    [Module.Finite K₀ V₀] (h : Module.finrank K₀ V₀ = 1) (f : V₀ →ₗ[K₀] V₀) :
    f.charpoly = Polynomial.X - Polynomial.C (LinearMap.trace K₀ V₀ f) := by
  classical
  let b : Module.Basis Unit K₀ V₀ := Module.basisUnique Unit h
  rw [← f.charpoly_toMatrix b, LinearMap.trace_eq_matrix_trace K₀ b f,
    Matrix.charpoly, Matrix.det_unique, Matrix.charmatrix_apply_eq, Matrix.trace]
  simp

/-- **Characteristic polynomial of a plane along an invariant line**
(PROVEN): if `e` preserves a submodule `W₀` with `1`-dimensional source
and quotient, acting on them by the scalars `a` resp. `b`, then
`charpoly e = (X - C a)(X - C b)`. Combined form of the two lemmas
above, packaged so that consumers only produce the two scalar-action
equations — all charpoly manipulation of submodule/quotient modules
stays inside this generic context (in the concrete consumer below, the
mixed `AddCommGroup`/`AddCommMonoid` instance spellings of submodule
endomorphism types fail to unify during standalone elaboration). -/
theorem _root_.LinearMap.charpoly_eq_mul_of_line
    {K₀ V₀ : Type*} [Field K₀] [AddCommGroup V₀] [Module K₀ V₀]
    [Module.Finite K₀ V₀]
    (W₀ : Submodule K₀ V₀) (e : V₀ →ₗ[K₀] V₀) (he : W₀ ≤ W₀.comap e)
    (hW : Module.finrank K₀ W₀ = 1) (hQ : Module.finrank K₀ (V₀ ⧸ W₀) = 1)
    {a b : K₀}
    (ha : e.restrict he = a • (1 : Module.End K₀ W₀))
    (hb : W₀.mapQ W₀ e he = b • (1 : Module.End K₀ (V₀ ⧸ W₀))) :
    e.charpoly = (Polynomial.X - Polynomial.C a) * (Polynomial.X - Polynomial.C b) := by
  rw [LinearMap.charpoly_eq_charpoly_restrict_mul_charpoly_mapQ W₀ e he, ha, hb,
    LinearMap.charpoly_eq_X_sub_C_trace_of_finrank_eq_one hW,
    LinearMap.charpoly_eq_X_sub_C_trace_of_finrank_eq_one hQ,
    map_smul (LinearMap.trace K₀ ↥W₀) a 1,
    map_smul (LinearMap.trace K₀ (V₀ ⧸ W₀)) b 1,
    LinearMap.trace_one, LinearMap.trace_one, hW, hQ]
  norm_num

omit [Algebra ℤ_[p] R] [IsDomain R] [Module.Finite ℤ_[p] R] [IsTopologicalRing R]
  [IsModuleTopology ℤ_[p] R] in
include hv in
set_option backward.isDefEq.respectTransparency false in
/-- **Diagonal characters of a reducible base change** (PROVEN): if the
base extension of `ρ` to `ℚ̄_p` is not irreducible, there is a pair of
continuous multiplicative characters `χ₁, χ₂ : G_ℚ → ℚ̄_p` splitting
every mapped characteristic polynomial:
`charpoly (ρ g) ↦ (X - χ₁ g)(X - χ₂ g)`. This is the linear-algebra
half of the Eisenstein branch, with no arithmetic content: a proper
invariant subspace of the `2`-dimensional base change is a line with a
line quotient; `χ₁` is the action on the line (extracted by a dual
functional through a complement), `χ₂` the action on the quotient; the
charpoly factors through the invariant line by the block-triangular
`LinearMap.charpoly_eq_mul_of_line`, and continuity is
`IsModuleTopology.continuous_of_linearMap` against the continuity of
`ρ` itself. -/
theorem exists_char_charpoly_map_eq_of_not_isIrreducible
    [Algebra R (AlgebraicClosure ℚ_[p])]
    [ContinuousSMul R (AlgebraicClosure ℚ_[p])]
    (hred : ¬ (ρ.baseChange (AlgebraicClosure ℚ_[p])).IsIrreducible) :
    ∃ χ₁ χ₂ : Field.absoluteGaloisGroup ℚ → AlgebraicClosure ℚ_[p],
      Continuous χ₁ ∧ Continuous χ₂ ∧ χ₁ 1 = 1 ∧ χ₂ 1 = 1 ∧
      (∀ g h, χ₁ (g * h) = χ₁ g * χ₁ h) ∧
      (∀ g h, χ₂ (g * h) = χ₂ g * χ₂ h) ∧
      ∀ g, ((ρ g).charpoly).map (algebraMap R (AlgebraicClosure ℚ_[p])) =
        (Polynomial.X - Polynomial.C (χ₁ g)) * (Polynomial.X - Polynomial.C (χ₂ g)) := by
  classical
  set σ : GaloisRep ℚ (AlgebraicClosure ℚ_[p]) (AlgebraicClosure ℚ_[p] ⊗[R] V) :=
    ρ.baseChange (AlgebraicClosure ℚ_[p]) with hσdef
  -- dimension bookkeeping
  have hfrM : Module.finrank (AlgebraicClosure ℚ_[p]) (AlgebraicClosure ℚ_[p] ⊗[R] V) = 2 := by
    rw [Module.finrank_baseChange]
    exact Module.finrank_eq_of_rank_eq hv
  haveI hMnt : Nontrivial (AlgebraicClosure ℚ_[p] ⊗[R] V) :=
    (Module.finrank_pos_iff (R := AlgebraicClosure ℚ_[p])).mp (by rw [hfrM]; norm_num)
  -- extract a proper invariant subspace from reducibility
  obtain ⟨W, hWbot, hWtop⟩ :
      ∃ W : Subrepresentation σ.toRepresentation, W ≠ ⊥ ∧ W ≠ ⊤ := by
    by_contra hcon
    push Not at hcon
    exact hred
      { toNontrivial :=
          ⟨⊥, ⊤, fun hbt => bot_ne_top
            (congrArg Subrepresentation.toSubmodule hbt)⟩
        eq_bot_or_eq_top := fun a => or_iff_not_imp_left.mpr (hcon a) }
  -- invariance of the subspace
  have hle : ∀ g : Field.absoluteGaloisGroup ℚ,
      W.toSubmodule ≤ W.toSubmodule.comap (σ g) :=
    fun g x hx => W.apply_mem_toSubmodule g hx
  -- the invariant subspace is a line with a line quotient
  have hWfr : Module.finrank (AlgebraicClosure ℚ_[p]) W.toSubmodule = 1 := by
    have h1 : Module.finrank (AlgebraicClosure ℚ_[p]) W.toSubmodule ≠ 0 := fun h =>
      hWbot (Subrepresentation.toSubmodule_injective (Submodule.finrank_eq_zero.mp h))
    have h2 : Module.finrank (AlgebraicClosure ℚ_[p]) W.toSubmodule <
        Module.finrank (AlgebraicClosure ℚ_[p]) (AlgebraicClosure ℚ_[p] ⊗[R] V) :=
      Submodule.finrank_lt fun h => hWtop (Subrepresentation.toSubmodule_injective h)
    rw [hfrM] at h2
    exact Nat.le_antisymm (Nat.lt_succ_iff.mp h2) (Nat.one_le_iff_ne_zero.mpr h1)
  have hQfr : Module.finrank (AlgebraicClosure ℚ_[p])
      ((AlgebraicClosure ℚ_[p] ⊗[R] V) ⧸ W.toSubmodule) = 1 := by
    have hq := Submodule.finrank_quotient_add_finrank W.toSubmodule
    rw [hfrM, hWfr] at hq
    omega
  -- every vector space is free (the instance is not picked up through the
  -- import closure here, so record it by hand for the line and its quotient)
  haveI : Module.Free (AlgebraicClosure ℚ_[p]) W.toSubmodule :=
    Module.Free.of_basis (Module.Basis.ofVectorSpace (AlgebraicClosure ℚ_[p]) W.toSubmodule)
  haveI : Module.Free (AlgebraicClosure ℚ_[p])
      ((AlgebraicClosure ℚ_[p] ⊗[R] V) ⧸ W.toSubmodule) :=
    Module.Free.of_divisionRing _ _
  -- a basis vector of the line and its dual functional through a complement
  let bW : Module.Basis Unit (AlgebraicClosure ℚ_[p]) W.toSubmodule :=
    Module.basisUnique Unit hWfr
  obtain ⟨c, hc⟩ := Submodule.exists_isCompl W.toSubmodule
  let φ : (AlgebraicClosure ℚ_[p] ⊗[R] V) →ₗ[AlgebraicClosure ℚ_[p]]
      AlgebraicClosure ℚ_[p] :=
    (bW.coord default) ∘ₗ (W.toSubmodule.projectionOnto c hc)
  set w : AlgebraicClosure ℚ_[p] ⊗[R] V :=
    ((bW default : W.toSubmodule) : AlgebraicClosure ℚ_[p] ⊗[R] V) with hwdef
  -- a lift of a basis vector of the quotient line and its dual functional
  let bQ : Module.Basis Unit (AlgebraicClosure ℚ_[p])
      ((AlgebraicClosure ℚ_[p] ⊗[R] V) ⧸ W.toSubmodule) :=
    Module.basisUnique Unit hQfr
  obtain ⟨u, hu⟩ := Submodule.mkQ_surjective W.toSubmodule (bQ default)
  let Φ : (AlgebraicClosure ℚ_[p] ⊗[R] V) →ₗ[AlgebraicClosure ℚ_[p]]
      AlgebraicClosure ℚ_[p] :=
    (bQ.coord default) ∘ₗ W.toSubmodule.mkQ
  -- the diagonal characters
  set χ₁ : Field.absoluteGaloisGroup ℚ → AlgebraicClosure ℚ_[p] :=
    fun g => φ (σ g w) with hχ₁def
  set χ₂ : Field.absoluteGaloisGroup ℚ → AlgebraicClosure ℚ_[p] :=
    fun g => Φ (σ g u) with hχ₂def
  -- normalization of the two functionals on the chosen vectors
  have hφw : φ w = 1 := by
    simp only [φ, LinearMap.comp_apply, hwdef]
    rw [Submodule.projectionOnto_apply_of_mem_left hc (bW default).2]
    simp [Module.Basis.coord_apply]
  have hΦu : Φ u = 1 := by
    simp only [Φ, LinearMap.comp_apply, hu]
    simp [Module.Basis.coord_apply]
  -- the line is spanned by `w`: the action on it is by the scalar `χ₁`
  have hscal₁ : ∀ g : Field.absoluteGaloisGroup ℚ, σ g w = χ₁ g • w := by
    intro g
    have hmem : σ g w ∈ W.toSubmodule := hle g (bW default).2
    have hrepr : (⟨σ g w, hmem⟩ : W.toSubmodule) =
        bW.repr ⟨σ g w, hmem⟩ default • bW default := by
      conv_lhs => rw [← bW.sum_repr ⟨σ g w, hmem⟩]
      simp
    have hval : χ₁ g = bW.repr ⟨σ g w, hmem⟩ default := by
      simp only [hχ₁def, φ, LinearMap.comp_apply]
      rw [Submodule.projectionOnto_apply_of_mem_left hc hmem]
      simp [Module.Basis.coord_apply]
    have hcoe := congrArg (W.toSubmodule.subtype) hrepr
    simp only [Submodule.subtype_apply, Submodule.coe_smul] at hcoe
    rw [hval]
    exact hcoe
  -- the quotient line is spanned by `mkQ u`: the quotient action is by `χ₂`
  have hscal₂ : ∀ g : Field.absoluteGaloisGroup ℚ,
      W.toSubmodule.mkQ (σ g u) = χ₂ g • W.toSubmodule.mkQ u := by
    intro g
    have hrepr : W.toSubmodule.mkQ (σ g u) =
        bQ.repr (W.toSubmodule.mkQ (σ g u)) default • bQ default := by
      conv_lhs => rw [← bQ.sum_repr (W.toSubmodule.mkQ (σ g u))]
      simp
    have hval : χ₂ g = bQ.repr (W.toSubmodule.mkQ (σ g u)) default := by
      simp only [hχ₂def, Φ, LinearMap.comp_apply]
      simp [Module.Basis.coord_apply]
    rw [hu, hval]
    exact hrepr
  -- multiplicativity
  have hmul₁ : ∀ g h, χ₁ (g * h) = χ₁ g * χ₁ h := by
    intro g h
    have happ : σ (g * h) w = σ g (σ h w) := by rw [map_mul]; rfl
    calc χ₁ (g * h) = φ (σ g (σ h w)) := by rw [hχ₁def]; exact congrArg φ happ
    _ = φ (σ g (χ₁ h • w)) := by rw [hscal₁ h]
    _ = χ₁ h * φ (σ g w) := by rw [map_smul, map_smul, smul_eq_mul]
    _ = χ₁ g * χ₁ h := mul_comm _ _
  have hΦker : ∀ x ∈ W.toSubmodule, Φ x = 0 := by
    intro x hx
    have hx0 : W.toSubmodule.mkQ x = 0 := (Submodule.Quotient.mk_eq_zero _).mpr hx
    simp [Φ, LinearMap.comp_apply, hx0]
  have hmul₂ : ∀ g h, χ₂ (g * h) = χ₂ g * χ₂ h := by
    intro g h
    have happ : σ (g * h) u = σ g (σ h u) := by rw [map_mul]; rfl
    have hdiff : σ h u - χ₂ h • u ∈ W.toSubmodule := by
      rw [← Submodule.Quotient.mk_eq_zero]
      have : W.toSubmodule.mkQ (σ h u - χ₂ h • u) = 0 := by
        rw [map_sub, map_smul, hscal₂ h, sub_self]
      exact this
    calc χ₂ (g * h) = Φ (σ g (σ h u)) := by rw [hχ₂def]; exact congrArg Φ happ
    _ = Φ (σ g (σ h u - χ₂ h • u)) + χ₂ h * Φ (σ g u) := by
        rw [map_sub (σ g), map_sub Φ, map_smul (σ g), map_smul Φ, smul_eq_mul]
        ring
    _ = χ₂ g * χ₂ h := by
        rw [hΦker _ (hle g hdiff), zero_add]
        exact mul_comm _ _
  -- normalization at the identity
  have hone₁ : χ₁ 1 = 1 := by
    have : σ 1 w = w := by rw [map_one]; rfl
    rw [hχ₁def]
    simpa [this] using hφw
  have hone₂ : χ₂ 1 = 1 := by
    have : σ 1 u = u := by rw [map_one]; rfl
    rw [hχ₂def]
    simpa [this] using hΦu
  -- continuity: evaluation-then-functional is linear in the endomorphism
  have hcont : ∀ (L : (AlgebraicClosure ℚ_[p] ⊗[R] V) →ₗ[AlgebraicClosure ℚ_[p]]
      AlgebraicClosure ℚ_[p]) (x : AlgebraicClosure ℚ_[p] ⊗[R] V),
      Continuous fun g : Field.absoluteGaloisGroup ℚ => L (σ g x) := by
    intro L x
    letI := moduleTopology (AlgebraicClosure ℚ_[p])
      (Module.End (AlgebraicClosure ℚ_[p]) (AlgebraicClosure ℚ_[p] ⊗[R] V))
    haveI : IsModuleTopology (AlgebraicClosure ℚ_[p])
        (Module.End (AlgebraicClosure ℚ_[p]) (AlgebraicClosure ℚ_[p] ⊗[R] V)) := ⟨rfl⟩
    have hL : Continuous fun f : Module.End (AlgebraicClosure ℚ_[p])
        (AlgebraicClosure ℚ_[p] ⊗[R] V) => L (f x) :=
      IsModuleTopology.continuous_of_linearMap (L ∘ₗ LinearMap.applyₗ x)
    exact hL.comp σ.continuous_toFun
  -- the factored characteristic polynomial
  have hchar : ∀ g, ((ρ g).charpoly).map (algebraMap R (AlgebraicClosure ℚ_[p])) =
      (Polynomial.X - Polynomial.C (χ₁ g)) * (Polynomial.X - Polynomial.C (χ₂ g)) := by
    intro g
    have hBC : σ g = LinearMap.baseChange (AlgebraicClosure ℚ_[p]) (ρ g) :=
      LinearMap.ext fun x => by
        induction x using TensorProduct.induction_on with
        | zero => simp
        | add a b ha hb => simp only [map_add, ha, hb]
        | tmul r v => simp [hσdef]
    have hres : (σ g).restrict (hle g) =
        χ₁ g • (1 : Module.End (AlgebraicClosure ℚ_[p]) W.toSubmodule) := by
      refine bW.ext fun i => ?_
      apply Subtype.ext
      have := hscal₁ g
      simpa [LinearMap.restrict_apply] using this
    have hqes : W.toSubmodule.mapQ W.toSubmodule (σ g) (hle g) =
        χ₂ g • (1 : Module.End (AlgebraicClosure ℚ_[p])
          ((AlgebraicClosure ℚ_[p] ⊗[R] V) ⧸ W.toSubmodule)) := by
      refine bQ.ext fun i => ?_
      rw [← hu, Submodule.mkQ_apply, Submodule.mapQ_apply]
      simpa [Submodule.mkQ_apply] using hscal₂ g
    rw [← LinearMap.charpoly_baseChange, ← hBC,
      LinearMap.charpoly_eq_mul_of_line W.toSubmodule (σ g) (hle g) hWfr hQfr hres hqes]
  exact ⟨χ₁, χ₂, hcont φ w, hcont Φ u, hone₁, hone₂, hmul₁, hmul₂, hchar⟩

/-- **The Eisenstein character dichotomy** (sorry node): if a pair of
continuous multiplicative characters `χ₁, χ₂ : G_ℚ → ℚ̄_p` splits every
mapped characteristic polynomial of a hardly ramified `ρ` (i.e.
`charpoly (ρ g) ↦ (X - χ₁ g)(X - χ₂ g)` for every `g`), then
`{χ₁, χ₂} = {1, χ_cyc}` in the symmetric (summed) form
`χ₁ + χ₂ = 1 + χ_cyc` pointwise. This is the class-field-theoretic
core of the reducible branch, isolated from all linear algebra (the
character extraction is the PROVEN
`exists_char_charpoly_map_eq_of_not_isIrreducible`); the intended
proof, with every ingredient determined by the hypotheses:

* comparing coefficients, `χ₁ + χ₂ = trace ∘ ρ` (mapped) and
  `χ₁ · χ₂ = det ∘ ρ = χ_cyc` (mapped, by the cyclotomic-determinant
  condition of `IsHardlyRamified`);
* at inertia away from `{2, p}`: `ρ` is unramified there, so on
  inertia `χ₁ + χ₂ = 2` and (the cyclotomic character being
  unramified there too) `χ₁χ₂ = 1`; hence `χ₁, χ₂` are roots of
  `(X - 1)²` — both unramified;
* at inertia at `2`: the tame-at-two condition makes `ρ|_{G_2}`
  triangular with unramified diagonal (the quotient character is
  unramified by hypothesis, the sub-character is `χ_cyc/δ` with both
  factors unramified at `2` since `p ≠ 2`), so the same
  `(X - 1)²` argument applies — `χ₁, χ₂` are unramified at `2`;
* at `p`: flatness of `ρ` at `p` forces (Raynaud/Fontaine on the
  finite levels) `{χ₁, χ₂}` restricted to inertia at `p` to be
  `{1, χ_cyc}`;
* Minkowski: `ℚ` has no nontrivial extension unramified everywhere,
  so the member of the pair with everywhere-unramified inertia is
  trivial and the other is exactly `χ_cyc`.

The conclusion is stated in the swap-symmetric summed form so that no
choice of matching survives into the statement. -/
theorem char_add_char_eq_one_add_cyclotomicCharacter
    [Algebra R (AlgebraicClosure ℚ_[p])]
    [ContinuousSMul R (AlgebraicClosure ℚ_[p])]
    (hZinj : Function.Injective (algebraMap ℤ_[p] R))
    (hRinj : Function.Injective (algebraMap R (AlgebraicClosure ℚ_[p])))
    (hρ : IsHardlyRamified hpodd hv ρ)
    (χ₁ χ₂ : Field.absoluteGaloisGroup ℚ → AlgebraicClosure ℚ_[p])
    (hcont₁ : Continuous χ₁) (hcont₂ : Continuous χ₂)
    (hone₁ : χ₁ 1 = 1) (hone₂ : χ₂ 1 = 1)
    (hmul₁ : ∀ g h, χ₁ (g * h) = χ₁ g * χ₁ h)
    (hmul₂ : ∀ g h, χ₂ (g * h) = χ₂ g * χ₂ h)
    (hchar : ∀ g, ((ρ g).charpoly).map (algebraMap R (AlgebraicClosure ℚ_[p])) =
      (Polynomial.X - Polynomial.C (χ₁ g)) * (Polynomial.X - Polynomial.C (χ₂ g))) :
    ∀ g, χ₁ g + χ₂ g =
      1 + algebraMap ℤ_[p] (AlgebraicClosure ℚ_[p])
        ((cyclotomicCharacter (AlgebraicClosure ℚ) p g.toRingEquiv : ℤ_[p]ˣ) : ℤ_[p]) :=
  sorry

/-- **Rational traces on the reducible branch** (PROVEN assembly, see
the DECOMPOSED note below): away from
a finite set of places, the TRACE coefficient (`coeff 1`) of the mapped
Frobenius characteristic polynomials of a hardly ramified `p`-adic
representation whose base extension to `ℚ̄_p` is NOT irreducible is a
RATIONAL number. This is the Eisenstein/class-field-theory branch of
the trace shadows — no automorphy enters. Shared
by BOTH trace shadows (a rational number is algebraic, and it lies in
the `ℚ`-span of `{1}`): this is the single reducible-branch node of
the dichotomy decomposition — see the DECOMPOSED notes on
`exists_isAlgebraic_trace_coeff` and
`exists_finiteDimensional_trace_span`.

DECOMPOSED (2026-07-23) into a PROVEN assembly over ONE sorried leaf
and proven linear algebra:

1. `exists_char_charpoly_map_eq_of_not_isIrreducible` (PROVEN) — the
   reducible base change carries a pair of continuous multiplicative
   diagonal characters `χ₁, χ₂` splitting every mapped charpoly as
   `(X - χ₁ g)(X - χ₂ g)` (invariant line + block-triangular charpoly
   infrastructure, built here).
2. `char_add_char_eq_one_add_cyclotomicCharacter` (sorry node) — the
   Eisenstein core: for such a pair, `χ₁ + χ₂ = 1 + χ_cyc` pointwise
   (inertia analysis away from `{2, p}` and at `2`, Raynaud/Fontaine
   flatness at `p`, Minkowski; see its docstring for the full route).
3. The assembly (below): at the place of a prime `q ≠ p`, the trace
   coefficient of the split quadratic is `-(χ₁ + χ₂)` at the
   arithmetic Frobenius, which by 2. and the PROVEN
   `cyclotomicCharacter_adicArithFrob_natCast` is the rational
   `-(1 + q)`; the exceptional set is the single place over `p`. -/
theorem exists_rat_trace_coeff_of_not_isIrreducible
    [Algebra R (AlgebraicClosure ℚ_[p])]
    [ContinuousSMul R (AlgebraicClosure ℚ_[p])]
    (hZinj : Function.Injective (algebraMap ℤ_[p] R))
    (hRinj : Function.Injective (algebraMap R (AlgebraicClosure ℚ_[p])))
    (hρ : IsHardlyRamified hpodd hv ρ)
    (hint : ∀ (v : HeightOneSpectrum (NumberField.RingOfIntegers ℚ)) (n : ℕ),
      ((algebraMap R (AlgebraicClosure ℚ_[p])).comp (algebraMap ℤ_[p] R)).IsIntegralElem
        (((ρ.charFrob v).map (algebraMap R (AlgebraicClosure ℚ_[p]))).coeff n))
    (K : IntermediateField ℚ_[p] (AlgebraicClosure ℚ_[p]))
    (hKfd : FiniteDimensional ℚ_[p] K)
    (hK : ∀ (v : HeightOneSpectrum (NumberField.RingOfIntegers ℚ)) (n : ℕ),
      ((ρ.charFrob v).map (algebraMap R (AlgebraicClosure ℚ_[p]))).coeff n ∈ K)
    (hred : ¬ (ρ.baseChange (AlgebraicClosure ℚ_[p])).IsIrreducible) :
    ∃ (S : Finset (HeightOneSpectrum (NumberField.RingOfIntegers ℚ))),
      ∀ v ∉ S, ∃ r : ℚ,
        ((ρ.charFrob v).map (algebraMap R (AlgebraicClosure ℚ_[p]))).coeff 1 =
          algebraMap ℚ (AlgebraicClosure ℚ_[p]) r := by
  classical
  obtain ⟨χ₁, χ₂, hcont₁, hcont₂, hone₁, hone₂, hmul₁, hmul₂, hchar⟩ :=
    exists_char_charpoly_map_eq_of_not_isIrreducible hv hred
  have hsum := char_add_char_eq_one_add_cyclotomicCharacter hpodd hv hZinj hRinj hρ
    χ₁ χ₂ hcont₁ hcont₂ hone₁ hone₂ hmul₁ hmul₂ hchar
  refine ⟨{hp.out.toHeightOneSpectrumRingOfIntegersRat}, fun v hvS => ?_⟩
  obtain ⟨q, hq, rfl⟩ := exists_prime_toHeightOneSpectrumRingOfIntegersRat v
  have hqp : q ≠ p := by
    rintro rfl
    exact hvS (Finset.mem_singleton_self _)
  refine ⟨-(1 + q), ?_⟩
  -- identify the mapped Frobenius charpoly with the mapped charpoly of the
  -- global Frobenius image, in the spelling of the PROVEN cyclotomic
  -- evaluation (the two spellings differ only in the subsingleton
  -- `Algebra ℚ _` instance)
  have hcp : ρ.charFrob hq.toHeightOneSpectrumRingOfIntegersRat =
      (ρ (Field.absoluteGaloisGroup.map (algebraMap ℚ
        (HeightOneSpectrum.adicCompletion ℚ hq.toHeightOneSpectrumRingOfIntegersRat))
        (Field.AbsoluteGaloisGroup.adicArithFrob
          hq.toHeightOneSpectrumRingOfIntegersRat))).charpoly := by
    rw [show ρ.charFrob hq.toHeightOneSpectrumRingOfIntegersRat =
      (ρ.toLocal hq.toHeightOneSpectrumRingOfIntegersRat
        (Field.AbsoluteGaloisGroup.adicArithFrob
          hq.toHeightOneSpectrumRingOfIntegersRat)).charpoly from rfl,
      GaloisRep.toLocal_apply]
    congr 1
    congr 1
    congr 1
    congr 1
    exact Subsingleton.elim _ _
  rw [hcp, hchar]
  -- the trace coefficient of the split quadratic
  have hcoeff : ∀ a b : AlgebraicClosure ℚ_[p],
      ((Polynomial.X - Polynomial.C a) * (Polynomial.X - Polynomial.C b)).coeff 1 =
        -(a + b) := by
    intro a b
    rw [show (Polynomial.X - Polynomial.C a) * (Polynomial.X - Polynomial.C b) =
      Polynomial.X ^ 2 - (Polynomial.C a + Polynomial.C b) * Polynomial.X +
        Polynomial.C a * Polynomial.C b by ring]
    simp
  rw [hcoeff, hsum, cyclotomicCharacter_adicArithFrob_natCast hq hqp, map_natCast,
    map_neg, map_add, map_one, map_natCast]

/-- **The Hecke field on the irreducible branch** (sorry node): away
from a finite set of places, the TRACE coefficients of the mapped
Frobenius characteristic polynomials of a hardly ramified `p`-adic
representation whose base extension to `ℚ̄_p` IS irreducible lie in a
single subfield of `ℚ̄_p` finite over `ℚ`. This is the automorphy core
of the irreducible branch in one node: an irreducible hardly ramified
representation is attached to a weight-2 cuspidal Hecke eigenform
(Wiles–Taylor–Wiles modularity lifting when the residual
representation is irreducible; Skinner–Wiles in the residually
reducible case), its Frobenius traces are the Hecke eigenvalues, and
they generate the Hecke field — a number field; `E` is its image under
the accompanying embedding into `ℚ̄_p`. The irreducibility hypothesis
is genuinely consumed (Taylor–Wiles patching requires it) — the
reducible branch runs through the disjoint Eisenstein route
(`exists_rat_trace_coeff_of_not_isIrreducible`). The `∃ S` is
load-bearing generality: the eventual proof may take `S` to be the
places dividing the level of ANY eigenform attached to `ρ` — no
level-lowering is demanded.

CONSOLIDATION NOTE (2026-07-23): the two irreducible-branch shadows
below (`exists_isAlgebraic_trace_coeff_of_isIrreducible`,
`exists_linearIndependent_trace_card_le_of_isIrreducible`) were both
atomic automorphy sorries whose eventual proofs would each have been
this whole modularity argument; they are now PROVEN assemblies over
this single node (algebraicity: elements of a finite extension of `ℚ`
are algebraic; batch bound: `d = finrank ℚ E`), so the automorphy
content of the irreducible branch is carried by exactly one sorry. -/
theorem exists_finiteDimensional_trace_field_of_isIrreducible
    [Algebra R (AlgebraicClosure ℚ_[p])]
    [ContinuousSMul R (AlgebraicClosure ℚ_[p])]
    (hZinj : Function.Injective (algebraMap ℤ_[p] R))
    (hRinj : Function.Injective (algebraMap R (AlgebraicClosure ℚ_[p])))
    (hρ : IsHardlyRamified hpodd hv ρ)
    (hint : ∀ (v : HeightOneSpectrum (NumberField.RingOfIntegers ℚ)) (n : ℕ),
      ((algebraMap R (AlgebraicClosure ℚ_[p])).comp (algebraMap ℤ_[p] R)).IsIntegralElem
        (((ρ.charFrob v).map (algebraMap R (AlgebraicClosure ℚ_[p]))).coeff n))
    (K : IntermediateField ℚ_[p] (AlgebraicClosure ℚ_[p]))
    (hKfd : FiniteDimensional ℚ_[p] K)
    (hK : ∀ (v : HeightOneSpectrum (NumberField.RingOfIntegers ℚ)) (n : ℕ),
      ((ρ.charFrob v).map (algebraMap R (AlgebraicClosure ℚ_[p]))).coeff n ∈ K)
    (hirr : (ρ.baseChange (AlgebraicClosure ℚ_[p])).IsIrreducible) :
    ∃ (E : IntermediateField ℚ (AlgebraicClosure ℚ_[p]))
      (_ : FiniteDimensional ℚ E)
      (S : Finset (HeightOneSpectrum (NumberField.RingOfIntegers ℚ))),
      ∀ v ∉ S,
        ((ρ.charFrob v).map (algebraMap R (AlgebraicClosure ℚ_[p]))).coeff 1 ∈ E :=
  sorry

/-- **Algebraicity shadow on the irreducible branch** (PROVEN assembly,
see the DECOMPOSED note below):
away from a finite set of places, the TRACE coefficient (`coeff 1`) of
the mapped Frobenius characteristic polynomials of a hardly ramified
`p`-adic representation whose base extension to `ℚ̄_p` IS irreducible
is algebraic over `ℚ`. The `∃ S` is load-bearing generality: the
eventual proof may take `S` to be the places dividing the level of ANY
eigenform attached to `ρ` — no level-lowering is demanded. No degree
bound and no common field is demanded (that is the orthogonal shadow).

DECOMPOSED (2026-07-23) into a PROVEN assembly over the consolidated
automorphy node `exists_finiteDimensional_trace_field_of_isIrreducible`
(see its CONSOLIDATION NOTE): each trace lies in a subfield `E ⊆ ℚ̄_p`
finite over `ℚ`, and every element of a finite extension of `ℚ` is
integral, hence algebraic, over `ℚ`. -/
theorem exists_isAlgebraic_trace_coeff_of_isIrreducible
    [Algebra R (AlgebraicClosure ℚ_[p])]
    [ContinuousSMul R (AlgebraicClosure ℚ_[p])]
    (hZinj : Function.Injective (algebraMap ℤ_[p] R))
    (hRinj : Function.Injective (algebraMap R (AlgebraicClosure ℚ_[p])))
    (hρ : IsHardlyRamified hpodd hv ρ)
    (hint : ∀ (v : HeightOneSpectrum (NumberField.RingOfIntegers ℚ)) (n : ℕ),
      ((algebraMap R (AlgebraicClosure ℚ_[p])).comp (algebraMap ℤ_[p] R)).IsIntegralElem
        (((ρ.charFrob v).map (algebraMap R (AlgebraicClosure ℚ_[p]))).coeff n))
    (K : IntermediateField ℚ_[p] (AlgebraicClosure ℚ_[p]))
    (hKfd : FiniteDimensional ℚ_[p] K)
    (hK : ∀ (v : HeightOneSpectrum (NumberField.RingOfIntegers ℚ)) (n : ℕ),
      ((ρ.charFrob v).map (algebraMap R (AlgebraicClosure ℚ_[p]))).coeff n ∈ K)
    (hirr : (ρ.baseChange (AlgebraicClosure ℚ_[p])).IsIrreducible) :
    ∃ (S : Finset (HeightOneSpectrum (NumberField.RingOfIntegers ℚ))),
      ∀ v ∉ S, IsAlgebraic ℚ
        (((ρ.charFrob v).map (algebraMap R (AlgebraicClosure ℚ_[p]))).coeff 1) := by
  obtain ⟨E, hEfd, S, hE⟩ := exists_finiteDimensional_trace_field_of_isIrreducible
    hpodd hv hZinj hRinj hρ hint K hKfd hK hirr
  haveI := hEfd
  refine ⟨S, fun v hv' => ?_⟩
  -- an element of a finite extension of `ℚ` inside `ℚ̄_p` is algebraic
  have hint' : IsIntegral ℚ
      ((algebraMap E (AlgebraicClosure ℚ_[p]))
        (⟨_, hE v hv'⟩ : E)) :=
    IsIntegral.algebraMap (IsIntegral.of_finite ℚ _)
  rw [IntermediateField.algebraMap_apply] at hint'
  exact isAlgebraic_iff_isIntegral.mpr hint'

/-- **Bounded-independence shadow on the irreducible branch** (PROVEN
assembly, see the DECOMPOSED note below): away from a finite set of
places there is a uniform bound `d`
such that every `ℚ`-linearly independent finite batch of TRACE
coefficients of the mapped Frobenius characteristic polynomials has at
most `d` elements. This is the finite-generation half of "the traces
are the Hecke eigenvalues of a single eigenform" in its weakest batch
form.
No single common spanning set is demanded here: that packaging of
`exists_finiteDimensional_trace_span` is PROVEN glue (extract a
linearly independent subset of the trace set spanning it via
`exists_linearIndepOn_id_extension`; the cardinality bound forces it
finite).

DECOMPOSED (2026-07-23) into a PROVEN assembly over the consolidated
automorphy node `exists_finiteDimensional_trace_field_of_isIrreducible`
(see its CONSOLIDATION NOTE): with `E` the trace field, take
`d = finrank ℚ E`; a `ℚ`-independent batch of traces lies in `E`,
stays independent when viewed inside `E` (independence transfers
backwards along the injective `ℚ`-linear inclusion), and is therefore
bounded by `LinearIndependent.fintype_card_le_finrank`. -/
theorem exists_linearIndependent_trace_card_le_of_isIrreducible
    [Algebra R (AlgebraicClosure ℚ_[p])]
    [ContinuousSMul R (AlgebraicClosure ℚ_[p])]
    (hZinj : Function.Injective (algebraMap ℤ_[p] R))
    (hRinj : Function.Injective (algebraMap R (AlgebraicClosure ℚ_[p])))
    (hρ : IsHardlyRamified hpodd hv ρ)
    (hint : ∀ (v : HeightOneSpectrum (NumberField.RingOfIntegers ℚ)) (n : ℕ),
      ((algebraMap R (AlgebraicClosure ℚ_[p])).comp (algebraMap ℤ_[p] R)).IsIntegralElem
        (((ρ.charFrob v).map (algebraMap R (AlgebraicClosure ℚ_[p]))).coeff n))
    (K : IntermediateField ℚ_[p] (AlgebraicClosure ℚ_[p]))
    (hKfd : FiniteDimensional ℚ_[p] K)
    (hK : ∀ (v : HeightOneSpectrum (NumberField.RingOfIntegers ℚ)) (n : ℕ),
      ((ρ.charFrob v).map (algebraMap R (AlgebraicClosure ℚ_[p]))).coeff n ∈ K)
    (hirr : (ρ.baseChange (AlgebraicClosure ℚ_[p])).IsIrreducible) :
    ∃ (S : Finset (HeightOneSpectrum (NumberField.RingOfIntegers ℚ))) (d : ℕ),
      ∀ t : Finset (AlgebraicClosure ℚ_[p]),
        (∀ x ∈ t, ∃ v ∉ S,
          ((ρ.charFrob v).map (algebraMap R (AlgebraicClosure ℚ_[p]))).coeff 1 = x) →
        LinearIndepOn ℚ id (t : Set (AlgebraicClosure ℚ_[p])) →
        t.card ≤ d := by
  classical
  obtain ⟨E, hEfd, S, hE⟩ := exists_finiteDimensional_trace_field_of_isIrreducible
    hpodd hv hZinj hRinj hρ hint K hKfd hK hirr
  haveI := hEfd
  refine ⟨S, Module.finrank ℚ E, fun t ht hind => ?_⟩
  -- each batch element lies in `E`
  have hmem : ∀ x ∈ t, x ∈ E := by
    intro x hx
    obtain ⟨v, hv', hvx⟩ := ht x hx
    exact hvx ▸ hE v hv'
  -- view the batch inside `E`: independence transfers backwards along the
  -- (injective, `ℚ`-linear) inclusion, and `E` has `ℚ`-dimension `finrank ℚ E`
  let g : ↑(t : Set (AlgebraicClosure ℚ_[p])) → E := fun x => ⟨x, hmem x x.2⟩
  have hcomp : ((IsScalarTower.toAlgHom ℚ E (AlgebraicClosure ℚ_[p])).toLinearMap ∘ g) =
      fun x : ↑(t : Set (AlgebraicClosure ℚ_[p])) => (x : AlgebraicClosure ℚ_[p]) := by
    funext x
    simp [g]
  have hgind : LinearIndependent ℚ g :=
    LinearIndependent.of_comp _ (by rw [hcomp]; exact hind)
  have hcard := hgind.fintype_card_le_finrank
  simpa [Fintype.card_coe] using hcard

/-- **Algebraicity shadow of the trace field** (PROVEN assembly, see
the DECOMPOSED note below): away from
a finite set of places, the TRACE coefficient (`coeff 1`) of the mapped
Frobenius characteristic polynomials of a hardly ramified `p`-adic
representation is ALGEBRAIC over `ℚ`. Strictly weaker than the
Hecke-field statement `exists_finiteDimensional_trace_field`: no bound
on the degrees and no common field is demanded — even granting
algebraicity of every trace, they could a priori generate an infinite
extension of `ℚ` (`ℚ_p` itself contains `√ℓ` for every square `ℓ` mod
`p`). One of the two orthogonal shadows of the Hecke-field statement
(the other is `exists_finiteDimensional_trace_span`); their
conjunction recovers it by PROVEN linear algebra — see the DECOMPOSED
note on `exists_finiteDimensional_trace_field`.

DECOMPOSED (2026-07-23) into a PROVEN assembly over the
reducible/irreducible dichotomy — the actual first move of the
literature proof (and of the B5/B6 architecture recorded in
`Reducible.lean`), splitting the class-field-theory content from the
automorphy content:

1. `exists_rat_trace_coeff_of_not_isIrreducible` (sorry node, SHARED
   with the span shadow) — if `ρ ⊗ ℚ̄_p` is reducible the traces are
   outright RATIONAL away from finitely many places (Eisenstein
   branch: character analysis + Minkowski, no automorphy).
2. `exists_isAlgebraic_trace_coeff_of_isIrreducible` (sorry node) —
   the irreducible branch, where modularity lifting applies; the
   irreducibility hypothesis is what Taylor–Wiles patching consumes.
3. The assembly (below): case on irreducibility of `ρ ⊗ ℚ̄_p`; on the
   reducible branch a rational trace is algebraic
   (`isAlgebraic_algebraMap`). -/
theorem exists_isAlgebraic_trace_coeff
    [Algebra R (AlgebraicClosure ℚ_[p])]
    [ContinuousSMul R (AlgebraicClosure ℚ_[p])]
    (hZinj : Function.Injective (algebraMap ℤ_[p] R))
    (hRinj : Function.Injective (algebraMap R (AlgebraicClosure ℚ_[p])))
    (hρ : IsHardlyRamified hpodd hv ρ)
    (hint : ∀ (v : HeightOneSpectrum (NumberField.RingOfIntegers ℚ)) (n : ℕ),
      ((algebraMap R (AlgebraicClosure ℚ_[p])).comp (algebraMap ℤ_[p] R)).IsIntegralElem
        (((ρ.charFrob v).map (algebraMap R (AlgebraicClosure ℚ_[p]))).coeff n))
    (K : IntermediateField ℚ_[p] (AlgebraicClosure ℚ_[p]))
    (hKfd : FiniteDimensional ℚ_[p] K)
    (hK : ∀ (v : HeightOneSpectrum (NumberField.RingOfIntegers ℚ)) (n : ℕ),
      ((ρ.charFrob v).map (algebraMap R (AlgebraicClosure ℚ_[p]))).coeff n ∈ K) :
    ∃ (S : Finset (HeightOneSpectrum (NumberField.RingOfIntegers ℚ))),
      ∀ v ∉ S, IsAlgebraic ℚ
        (((ρ.charFrob v).map (algebraMap R (AlgebraicClosure ℚ_[p]))).coeff 1) := by
  by_cases hirr : (ρ.baseChange (AlgebraicClosure ℚ_[p])).IsIrreducible
  · exact exists_isAlgebraic_trace_coeff_of_isIrreducible hpodd hv hZinj hRinj hρ hint
      K hKfd hK hirr
  · obtain ⟨S, hS⟩ := exists_rat_trace_coeff_of_not_isIrreducible hpodd hv hZinj hRinj hρ
      hint K hKfd hK hirr
    refine ⟨S, fun v hv => ?_⟩
    obtain ⟨r, hr⟩ := hS v hv
    rw [hr]
    exact isAlgebraic_algebraMap r

/-- **Finite-span shadow of the trace field** (PROVEN assembly, see the
DECOMPOSED note below): away from a
finite set of places, the TRACE coefficients of the mapped Frobenius
characteristic polynomials of a hardly ramified `p`-adic representation
all lie in the `ℚ`-LINEAR SPAN of finitely many elements of `ℚ̄_p`.
Strictly weaker than the Hecke-field statement
`exists_finiteDimensional_trace_field`: nothing is demanded of the
spanning elements — no algebraicity over `ℚ`, no field structure — so
this captures only the finite-generation half of "the traces are the
Hecke eigenvalues of a single eigenform" (they span a
finite-dimensional `ℚ`-space, e.g. the Hecke field itself). Note the
confinement hypotheses `hKfd`/`hK` do NOT give this formally: `K` is
finite over `ℚ_p`, hence INFINITE-dimensional over `ℚ`. The other
orthogonal shadow is `exists_isAlgebraic_trace_coeff`; their
conjunction recovers the Hecke-field statement by PROVEN linear
algebra — see the DECOMPOSED note on
`exists_finiteDimensional_trace_field`.

DECOMPOSED (2026-07-23) into a PROVEN assembly over the same
reducible/irreducible dichotomy as `exists_isAlgebraic_trace_coeff`
(see the DECOMPOSED note there), with the common-spanning-set
packaging additionally moved into proven glue:

1. `exists_rat_trace_coeff_of_not_isIrreducible` (sorry node, SHARED
   with the algebraicity shadow) — on the reducible branch the traces
   are rational, hence lie in the `ℚ`-span of `{1}`.
2. `exists_linearIndependent_trace_card_le_of_isIrreducible` (sorry
   node) — on the irreducible branch, a uniform cardinality bound `d`
   on `ℚ`-linearly independent batches of traces (the weakest batch
   form of "the traces lie in the `[E : ℚ]`-dimensional Hecke
   field").
3. The assembly (below): on the irreducible branch, extract via
   `exists_linearIndepOn_id_extension` a linearly independent subset
   `b` of the trace set whose span contains every trace; `b` is
   finite — otherwise it would contain an independent batch of `d + 1`
   traces (`Set.Infinite.exists_subset_card_eq`), contradicting the
   bound. -/
theorem exists_finiteDimensional_trace_span
    [Algebra R (AlgebraicClosure ℚ_[p])]
    [ContinuousSMul R (AlgebraicClosure ℚ_[p])]
    (hZinj : Function.Injective (algebraMap ℤ_[p] R))
    (hRinj : Function.Injective (algebraMap R (AlgebraicClosure ℚ_[p])))
    (hρ : IsHardlyRamified hpodd hv ρ)
    (hint : ∀ (v : HeightOneSpectrum (NumberField.RingOfIntegers ℚ)) (n : ℕ),
      ((algebraMap R (AlgebraicClosure ℚ_[p])).comp (algebraMap ℤ_[p] R)).IsIntegralElem
        (((ρ.charFrob v).map (algebraMap R (AlgebraicClosure ℚ_[p]))).coeff n))
    (K : IntermediateField ℚ_[p] (AlgebraicClosure ℚ_[p]))
    (hKfd : FiniteDimensional ℚ_[p] K)
    (hK : ∀ (v : HeightOneSpectrum (NumberField.RingOfIntegers ℚ)) (n : ℕ),
      ((ρ.charFrob v).map (algebraMap R (AlgebraicClosure ℚ_[p]))).coeff n ∈ K) :
    ∃ (S : Finset (HeightOneSpectrum (NumberField.RingOfIntegers ℚ)))
      (t : Finset (AlgebraicClosure ℚ_[p])),
      ∀ v ∉ S,
        ((ρ.charFrob v).map (algebraMap R (AlgebraicClosure ℚ_[p]))).coeff 1 ∈
          Submodule.span ℚ (t : Set (AlgebraicClosure ℚ_[p])) := by
  classical
  by_cases hirr : (ρ.baseChange (AlgebraicClosure ℚ_[p])).IsIrreducible
  · obtain ⟨S, d, hcard⟩ := exists_linearIndependent_trace_card_le_of_isIrreducible
      hpodd hv hZinj hRinj hρ hint K hKfd hK hirr
    -- the set of traces away from `S`
    set A : Set (AlgebraicClosure ℚ_[p]) := {x | ∃ v ∉ S,
      ((ρ.charFrob v).map (algebraMap R (AlgebraicClosure ℚ_[p]))).coeff 1 = x}
      with hAdef
    -- extract a linearly independent subset of `A` whose span contains `A`
    obtain ⟨b, hbA, -, hbspan, hbind⟩ :=
      exists_linearIndepOn_id_extension
        (linearIndependent_empty ℚ (AlgebraicClosure ℚ_[p])) (Set.empty_subset A)
    -- `b` is finite: an infinite `b` would contain an independent batch
    -- of `d + 1` traces, contradicting the cardinality bound
    have hbfin : b.Finite := by
      by_contra hbinf
      obtain ⟨u, hub, hucard⟩ :=
        Set.Infinite.exists_subset_card_eq hbinf (d + 1)
      exact absurd (hcard u (fun x hx => hbA (hub hx)) (hbind.mono hub)) (by omega)
    refine ⟨S, hbfin.toFinset, fun v hv => ?_⟩
    rw [Set.Finite.coe_toFinset]
    exact hbspan ⟨v, hv, rfl⟩
  · obtain ⟨S, hS⟩ := exists_rat_trace_coeff_of_not_isIrreducible hpodd hv hZinj hRinj hρ
      hint K hKfd hK hirr
    refine ⟨S, {1}, fun v hv => ?_⟩
    obtain ⟨r, hr⟩ := hS v hv
    rw [hr, Algebra.algebraMap_eq_smul_one]
    exact Submodule.smul_mem _ r (Submodule.subset_span (by simp))

/-- **Trace-field finiteness core of the eigensystem stratum** (PROVEN
assembly, see the DECOMPOSED note below): away from a finite set of
places, the TRACE coefficient
(`coeff 1`) of the mapped Frobenius characteristic polynomials of a
hardly ramified `p`-adic representation lies in a single subfield of
`ℚ̄_p` finite over `ℚ`. This is the sole surviving automorphy content
of `exists_finiteDimensional_coeff_field` (see the DECOMPOSED note
there): the determinant coefficient is PROVEN rational
(`charFrob_coeff_zero_eq_natCast`) and the coefficients in degrees
`≥ 2` are `1, 0, 0, …`, but the traces are the Hecke eigenvalues of the
cuspidal eigenform underlying `ρ`, and their generating a number field
(the Hecke field) is where automorphy enters. The confinement
hypotheses `hKfd`/`hK` (discharged at the call site by the PROVEN
`exists_finiteDimensional_padic_coeff_field`) record the formal half:
the traces already lie in one finite extension of `ℚ_p`. A finite
extension of `ℚ_p` contains algebraic-over-`ℚ` subfields of infinite
degree (e.g. `ℚ(√ℓ : ℓ a square mod p)` inside `ℚ_p` itself), so
`ℚ`-finiteness is genuinely not formal even given the confinement.

DECOMPOSED (2026-07-23) into a PROVEN assembly over TWO strictly
weaker leaves — the two orthogonal shadows of "the traces are
the Hecke eigenvalues of one eigenform":

1. `exists_isAlgebraic_trace_coeff` (as of 2026-07-23 itself a PROVEN
   assembly over the reducible/irreducible dichotomy; see its
   DECOMPOSED note) — each trace is
   algebraic over `ℚ` (no degree bound, no common field);
2. `exists_finiteDimensional_trace_span` (as of 2026-07-23 itself a
   PROVEN assembly over the same dichotomy plus the
   `exists_linearIndependent` span-packaging glue; see its DECOMPOSED
   note) — the traces lie
   in the `ℚ`-linear span of finitely many elements of `ℚ̄_p` (no
   algebraicity, no field structure).

Neither shadow alone suffices (1. allows infinite compositum of small
fields; 2. allows transcendental spanning sets), but their conjunction
is pure linear algebra (the assembly below): intersect the
finite-dimensional span with the `ℚ`-subalgebra of integral elements —
a finite-dimensional space every element of which is algebraic — pick
a finite generating set, and adjoin it to `ℚ`: a finite extension
(finitely many algebraic generators) containing every trace (each
trace is an algebraic member of the span, hence of the intersection,
hence of the span of its generators). -/
theorem exists_finiteDimensional_trace_field
    [Algebra R (AlgebraicClosure ℚ_[p])]
    [ContinuousSMul R (AlgebraicClosure ℚ_[p])]
    (hZinj : Function.Injective (algebraMap ℤ_[p] R))
    (hRinj : Function.Injective (algebraMap R (AlgebraicClosure ℚ_[p])))
    (hρ : IsHardlyRamified hpodd hv ρ)
    (hint : ∀ (v : HeightOneSpectrum (NumberField.RingOfIntegers ℚ)) (n : ℕ),
      ((algebraMap R (AlgebraicClosure ℚ_[p])).comp (algebraMap ℤ_[p] R)).IsIntegralElem
        (((ρ.charFrob v).map (algebraMap R (AlgebraicClosure ℚ_[p]))).coeff n))
    (K : IntermediateField ℚ_[p] (AlgebraicClosure ℚ_[p]))
    (hKfd : FiniteDimensional ℚ_[p] K)
    (hK : ∀ (v : HeightOneSpectrum (NumberField.RingOfIntegers ℚ)) (n : ℕ),
      ((ρ.charFrob v).map (algebraMap R (AlgebraicClosure ℚ_[p]))).coeff n ∈ K) :
    ∃ (E : IntermediateField ℚ (AlgebraicClosure ℚ_[p]))
      (_ : FiniteDimensional ℚ E)
      (S : Finset (HeightOneSpectrum (NumberField.RingOfIntegers ℚ))),
      ∀ v ∉ S,
        ((ρ.charFrob v).map (algebraMap R (AlgebraicClosure ℚ_[p]))).coeff 1 ∈ E := by
  classical
  obtain ⟨S₁, halg⟩ :=
    exists_isAlgebraic_trace_coeff hpodd hv hZinj hRinj hρ hint K hKfd hK
  obtain ⟨S₂, t, hspan⟩ :=
    exists_finiteDimensional_trace_span hpodd hv hZinj hRinj hρ hint K hKfd hK
  -- the algebraic part of the span: a finite-dimensional `ℚ`-space all
  -- of whose elements are algebraic over `ℚ`
  set M : Submodule ℚ (AlgebraicClosure ℚ_[p]) :=
    Submodule.span ℚ (t : Set (AlgebraicClosure ℚ_[p])) ⊓
      Subalgebra.toSubmodule (integralClosure ℚ (AlgebraicClosure ℚ_[p])) with hMdef
  haveI : FiniteDimensional ℚ M := Submodule.finiteDimensional_of_le inf_le_left
  obtain ⟨s, hs⟩ : (⊤ : Submodule ℚ M).FG := Module.finite_def.mp inferInstance
  -- the generators of `M` are finitely many algebraic elements
  have hgen : ∀ x ∈ ⇑M.subtype '' ↑s, IsIntegral ℚ x := by
    rintro x ⟨m, -, rfl⟩
    -- membership in `toSubmodule (integralClosure ℚ _)` is definitionally
    -- integrality
    exact (Submodule.mem_inf.mp m.2).2
  refine ⟨IntermediateField.adjoin ℚ (⇑M.subtype '' ↑s), ?_, S₁ ∪ S₂,
    fun v hv' => ?_⟩
  · -- finitely many algebraic generators span a finite extension
    haveI : Finite ↥(⇑M.subtype '' ↑s) := (s.finite_toSet.image _).to_subtype
    exact IntermediateField.finiteDimensional_adjoin hgen
  · -- each trace is an algebraic member of the span, hence in `M`,
    -- hence in the span of the generators, hence in the adjoined field
    have hv₁ : v ∉ S₁ := fun h => hv' (Finset.mem_union_left _ h)
    have hv₂ : v ∉ S₂ := fun h => hv' (Finset.mem_union_right _ h)
    have hmem : ((ρ.charFrob v).map (algebraMap R (AlgebraicClosure ℚ_[p]))).coeff 1
        ∈ M := Submodule.mem_inf.mpr ⟨hspan v hv₂,
      isAlgebraic_iff_isIntegral.mp (halg v hv₁)⟩
    have hMspan : Submodule.span ℚ (⇑M.subtype '' ↑s) = M := by
      rw [← Submodule.map_span, hs, Submodule.map_subtype_top]
    have hle : Submodule.span ℚ (⇑M.subtype '' ↑s) ≤
        Subalgebra.toSubmodule
          (IntermediateField.adjoin ℚ (⇑M.subtype '' ↑s)).toSubalgebra :=
      Submodule.span_le.mpr fun x hx => IntermediateField.subset_adjoin ℚ _ hx
    exact hle (hMspan.symm ▸ hmem)

/-- **Algebraicity/finiteness core of the eigensystem stratum** (PROVEN
assembly, see the DECOMPOSED note below): away from a finite set of
places, the coefficients of the mapped
Frobenius characteristic polynomials of a hardly ramified `p`-adic
representation all lie in a single subfield of `ℚ̄_p` that is **finite
over `ℚ`**. This is where the automorphy of `ρ` enters: the coefficients
are a priori only integral over `ℤ_p` (hypothesis `hint`, the proven
integrality stratum `charFrob_coeff_isIntegralElem`), and a finite
extension of `ℚ_p` contains algebraic-over-`ℚ` subfields of infinite
degree, so the finite-degree bound is not formal — it is the statement
that the Frobenius traces are the Hecke eigenvalues of a cuspidal
eigenform, which generate a number field (the Hecke field). The
number-field/embedding/polynomial *packaging* of this statement is
proven downstream in `exists_numberField_eigensystem`; this leaf is the
bare mathematical content in minimal vocabulary.

DECOMPOSED (2026-07-23) into a PROVEN assembly over ONE sorried leaf
and proven strata:

1. `exists_finiteDimensional_padic_coeff_field` (PROVEN) — all
   coefficients lie in a single subfield finite over `ℚ_p` (formal,
   from module-finiteness of `R`, via the PROVEN composite-vs-canonical
   identity `algebraMap_comp_algebraMap_padicInt`).
2. `charFrob_coeff_zero_eq_natCast` (PROVEN) — the determinant
   coefficient at the place of `q ≠ p` is the rational integer
   `q`, by the cyclotomic-determinant condition of `IsHardlyRamified`
   and the cyclotomic-Frobenius evaluation
   `cyclotomicCharacter_adicArithFrob_natCast` (PROVEN 2026-07-23 by
   the general-`p` port of the `3`-adic lemma chain).
3. `exists_finiteDimensional_trace_field` (as of 2026-07-23 itself a
   PROVEN assembly over the two orthogonal sorried shadows
   `exists_isAlgebraic_trace_coeff` and
   `exists_finiteDimensional_trace_span`; see its DECOMPOSED note) —
   the TRACE coefficient lands in a number field away from finitely
   many places: the sole surviving automorphy content (the Hecke
   field), taking the confinement of stratum 1 as a hypothesis.
4. The assembly (PROVEN, below): coefficients in degrees `≥ 2` are
   `1, 0, 0, …` (the mapped charpoly is monic of degree `2`), the
   degree-`0` coefficient is `q ∈ ℚ ⊆ E` by 2., the degree-`1`
   coefficient lies in `E` by 3. (fed with 1.), and the exceptional
   set is `S ∪ {the places over 2 and p}`. -/
theorem exists_finiteDimensional_coeff_field
    [Algebra R (AlgebraicClosure ℚ_[p])]
    [ContinuousSMul R (AlgebraicClosure ℚ_[p])]
    (hZinj : Function.Injective (algebraMap ℤ_[p] R))
    (hRinj : Function.Injective (algebraMap R (AlgebraicClosure ℚ_[p])))
    (hρ : IsHardlyRamified hpodd hv ρ)
    (hint : ∀ (v : HeightOneSpectrum (NumberField.RingOfIntegers ℚ)) (n : ℕ),
      ((algebraMap R (AlgebraicClosure ℚ_[p])).comp (algebraMap ℤ_[p] R)).IsIntegralElem
        (((ρ.charFrob v).map (algebraMap R (AlgebraicClosure ℚ_[p]))).coeff n)) :
    ∃ (E : IntermediateField ℚ (AlgebraicClosure ℚ_[p]))
      (_ : FiniteDimensional ℚ E)
      (S : Finset (HeightOneSpectrum (NumberField.RingOfIntegers ℚ))),
      ∀ v ∉ S, ∀ n : ℕ,
        ((ρ.charFrob v).map (algebraMap R (AlgebraicClosure ℚ_[p]))).coeff n ∈ E := by
  classical
  obtain ⟨K, hKfd, hK⟩ := exists_finiteDimensional_padic_coeff_field (p := p) (ρ := ρ)
  obtain ⟨E, hEfd, S₀, htr⟩ :=
    exists_finiteDimensional_trace_field hpodd hv hZinj hRinj hρ hint K hKfd hK
  refine ⟨E, hEfd,
    insert Nat.prime_two.toHeightOneSpectrumRingOfIntegersRat
      (insert (hp.out.toHeightOneSpectrumRingOfIntegersRat) S₀),
    fun v hvS n => ?_⟩
  obtain ⟨q, hq, rfl⟩ := exists_prime_toHeightOneSpectrumRingOfIntegersRat v
  -- the mapped charpoly is (the map of) the charpoly of the local Frobenius
  have hcp : ρ.charFrob hq.toHeightOneSpectrumRingOfIntegersRat =
      (ρ.toLocal hq.toHeightOneSpectrumRingOfIntegersRat
        (Field.AbsoluteGaloisGroup.adicArithFrob
          hq.toHeightOneSpectrumRingOfIntegersRat)).charpoly := rfl
  have hdeg : ((ρ.charFrob hq.toHeightOneSpectrumRingOfIntegersRat).map
      (algebraMap R (AlgebraicClosure ℚ_[p]))).natDegree = 2 := by
    rw [hcp, (LinearMap.charpoly_monic _).natDegree_map, LinearMap.charpoly_natDegree]
    exact Module.finrank_eq_of_rank_eq hv
  match n with
  | 0 =>
    -- the determinant coefficient is the rational integer `q`
    have hqp : q ≠ p := by
      rintro rfl
      exact hvS (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
    rw [charFrob_coeff_zero_eq_natCast hpodd hv hρ hq hqp]
    exact natCast_mem E q
  | 1 =>
    -- the trace coefficient: the sorried automorphy leaf
    exact htr _ fun h => hvS (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem h))
  | 2 =>
    -- the leading coefficient of the mapped monic degree-2 charpoly
    have hmon : ((ρ.charFrob hq.toHeightOneSpectrumRingOfIntegersRat).map
        (algebraMap R (AlgebraicClosure ℚ_[p]))).Monic := by
      rw [hcp]
      exact (LinearMap.charpoly_monic _).map _
    have h1 := hmon.coeff_natDegree
    rw [hdeg] at h1
    rw [h1]
    exact one_mem E
  | (m + 3) =>
    -- coefficients above the degree vanish
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [hdeg]; omega)]
    exact zero_mem E

/-- **Eigensystem stratum** (PROVEN assembly, see the DECOMPOSED note
below): the Frobenius characteristic
polynomials of a hardly ramified `p`-adic representation over a
characteristic-zero coefficient ring embedded in `ℚ̄_p` descend, away
from a finite set of places, to a single **number field** `E`.

This is the trace-level shadow of "`ρ` is congruent to a cuspidal Hecke
eigenform": the number field `E` is the Hecke field, `Pv v` is
`X² − a_v X + q_v`, and the finite exceptional set is the level. The
genuine content is the *algebraicity and finiteness* of the trace field:
the Frobenius traces of `ρ` live in the module-finite `ℤ_p`-algebra `R`,
hence in a finite extension of `ℚ_p` — but a finite extension of `ℚ_p`
contains algebraic subfields of infinite degree over `ℚ`, so the
existence of a *number* field `E` capturing all of them (with a single
embedding `ψ` matching the two sides) is not formal; it is where the
automorphy of `ρ` first enters (Hecke eigenvalues are algebraic integers
generating a finite extension).

VOCABULARY NOTE (2026-07-22): the mathlib pin has modular forms
(`CuspForm` etc.) but no Hecke operators, no eigenforms and no attached
Galois representations, so the requested "cuspidal eigenform congruence"
split can only be stated at this trace level; this leaf is its faithful
shadow in the available vocabulary.

DECOMPOSED (2026-07-22) into a PROVEN assembly over two strata:

1. `charFrob_coeff_isIntegralElem` (PROVEN) — the coefficients are
   integral over `ℤ_[p]` (formal, from module-finiteness of `R`).
2. `exists_finiteDimensional_coeff_field` (sorry node) — the
   coefficients lie, away from finitely many places, in a subfield of
   `ℚ̄_p` finite over `ℚ`. The sole surviving automorphy content at
   this level.
3. The packaging (PROVEN, below): the intermediate field is upgraded to
   an abstract `NumberField` in the required universe via `ULift`, the
   embedding `ψ` is the inclusion, and the polynomials `Pv` are
   rebuilt over the subfield coefficient-by-coefficient
   (`Polynomial.as_sum_support_C_mul_X_pow`), with value `0` at the
   finitely many exceptional places. -/
theorem exists_numberField_eigensystem
    [Algebra R (AlgebraicClosure ℚ_[p])]
    [ContinuousSMul R (AlgebraicClosure ℚ_[p])]
    (hZinj : Function.Injective (algebraMap ℤ_[p] R))
    (hRinj : Function.Injective (algebraMap R (AlgebraicClosure ℚ_[p])))
    (hρ : IsHardlyRamified hpodd hv ρ) :
    ∃ (E : Type v) (_ : Field E) (_ : NumberField E)
      (ψ : E →+* AlgebraicClosure ℚ_[p])
      (S : Finset (HeightOneSpectrum (NumberField.RingOfIntegers ℚ)))
      (Pv : HeightOneSpectrum (NumberField.RingOfIntegers ℚ) → Polynomial E),
      ∀ v : HeightOneSpectrum (NumberField.RingOfIntegers ℚ), v ∉ S →
        (ρ.charFrob v).map (algebraMap R (AlgebraicClosure ℚ_[p])) =
          (Pv v).map ψ := by
  classical
  obtain ⟨E₀, hFD, S, hmem⟩ :=
    exists_finiteDimensional_coeff_field hpodd hv hZinj hRinj hρ
      (charFrob_coeff_isIntegralElem (ρ := ρ))
  haveI : FiniteDimensional ℚ E₀ := hFD
  haveI : CharZero E₀ := charZero_of_injective_algebraMap (algebraMap ℚ E₀).injective
  haveI : CharZero (ULift.{v} E₀) :=
    charZero_of_injective_algebraMap (algebraMap ℚ (ULift.{v} E₀)).injective
  haveI : Module.Finite ℚ (ULift.{v} E₀) := Module.Finite.equiv (ULift.moduleEquiv).symm
  haveI : NumberField (ULift.{v} E₀) := ⟨⟩
  -- rebuild each mapped characteristic polynomial over the subfield `E₀`
  have hP₀ : ∀ w, w ∉ S → ∃ P : Polynomial E₀,
      P.map (algebraMap E₀ (AlgebraicClosure ℚ_[p])) =
        (ρ.charFrob w).map (algebraMap R (AlgebraicClosure ℚ_[p])) := by
    intro w hw
    refine ⟨∑ n ∈ ((ρ.charFrob w).map (algebraMap R (AlgebraicClosure ℚ_[p]))).support,
      Polynomial.C
        (⟨((ρ.charFrob w).map (algebraMap R (AlgebraicClosure ℚ_[p]))).coeff n,
          hmem w hw n⟩ : E₀) * Polynomial.X ^ n, ?_⟩
    rw [Polynomial.map_sum]
    simp only [Polynomial.map_mul, Polynomial.map_C, Polynomial.map_pow, Polynomial.map_X,
      IntermediateField.algebraMap_apply]
    exact (Polynomial.as_sum_support_C_mul_X_pow _).symm
  choose P₀ hP₀eq using hP₀
  refine ⟨ULift.{v} E₀, inferInstance, inferInstance,
    (algebraMap E₀ (AlgebraicClosure ℚ_[p])).comp (ULift.ringEquiv.toRingHom), S,
    fun w => if h : w ∈ S then 0 else
      (P₀ w h).map (ULift.ringEquiv (R := E₀)).symm.toRingHom, ?_⟩
  intro w hw
  simp only [dif_neg hw, Polynomial.map_map]
  have hcomp : ((algebraMap E₀ (AlgebraicClosure ℚ_[p])).comp
        (ULift.ringEquiv.toRingHom)).comp
      (ULift.ringEquiv (R := E₀)).symm.toRingHom
        = algebraMap E₀ (AlgebraicClosure ℚ_[p]) := by
    ext x
    simp
  rw [hcomp, hP₀eq w hw]

set_option backward.isDefEq.respectTransparency false in
/-- Characteristic-polynomial-of-Frobenius transport through base change
and framing (PROVEN): the Frobenius characteristic polynomial of a
conjugated base change is the image of the original one under the
coefficient map. Local (`charFrob`-level) analog of the global
`charpoly_baseChange_conj` of `Lift.lean` (which lives downstream and
cannot be imported here); an ingredient of the spreading-stratum
assembly below. -/
lemma charFrob_baseChange_conj {A : Type*} [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] {B : Type*} [CommRing B] [TopologicalSpace B]
    [IsTopologicalRing B] [Algebra A B] [ContinuousSMul A B]
    {W : Type*} [AddCommGroup W] [Module A W] [Module.Finite A W]
    [Module.Free A W] {N : Type*} [AddCommGroup N] [Module B N]
    [Module.Finite B N] [Module.Free B N]
    (τ : GaloisRep ℚ A W) (e : (B ⊗[A] W) ≃ₗ[B] N)
    (v : HeightOneSpectrum (NumberField.RingOfIntegers ℚ)) :
    ((τ.baseChange B).conj e).charFrob v = (τ.charFrob v).map (algebraMap A B) := by
  have hBC : ∀ g : Field.absoluteGaloisGroup ℚ,
      (τ.baseChange B) g = LinearMap.baseChange B (τ g) := fun g =>
    LinearMap.ext fun x => by
      induction x using TensorProduct.induction_on with
      | zero => simp
      | add a b ha hb => simp only [map_add, ha, hb]
      | tmul c w => simp
  show ((((τ.baseChange B).conj e)).toLocal v
      (Field.AbsoluteGaloisGroup.adicArithFrob v)).charpoly = _
  rw [GaloisRep.toLocal_apply, GaloisRep.conj_apply, LinearEquiv.charpoly_conj,
    hBC, LinearMap.charpoly_baseChange]
  rfl

/-- Unramifiedness transfers along conjugation by a linear isomorphism
of the representation space (PROVEN): the kernel of the local
representation is unchanged by conjugation. (Mirrors the unramifiedness
bullet of `isHardlyRamified_conj` in `Lift.lean`, which lives downstream
and cannot be imported here.) -/
lemma isUnramifiedAt_conj {A : Type*} [CommRing A] [TopologicalSpace A]
    {W : Type*} [AddCommGroup W] [Module A W]
    {N : Type*} [AddCommGroup N] [Module A N]
    (τ : GaloisRep ℚ A W) (e : W ≃ₗ[A] N)
    (v : HeightOneSpectrum (NumberField.RingOfIntegers ℚ))
    [τ.IsUnramifiedAt v] :
    (τ.conj e).IsUnramifiedAt v := by
  refine ⟨le_trans (GaloisRep.IsUnramifiedAt.localInertiaGroup_le (ρ := τ)) ?_⟩
  intro σ hσ
  have h1 : τ.toLocal v σ = 1 := hσ
  show (τ.conj e).toLocal v σ = 1
  rw [GaloisRep.toLocal_apply, GaloisRep.conj_apply,
    ← GaloisRep.toLocal_apply, h1]
  refine LinearMap.ext fun w => ?_
  simp

omit [IsDomain R] in
/-- Away from `2` and `p`, a hardly ramified `p`-adic representation is
unramified at every finite place of `ℚ` (PROVEN): the prime-indexed
unramifiedness field of `IsHardlyRamified` in the place-indexed form
that the compatibility clause of the spreading stratum consumes. -/
lemma isUnramifiedAt_of_ne (hρ : IsHardlyRamified hpodd hv ρ)
    (v : HeightOneSpectrum (NumberField.RingOfIntegers ℚ))
    (hv2 : v ≠ Nat.prime_two.toHeightOneSpectrumRingOfIntegersRat)
    (hvp : (p : NumberField.RingOfIntegers ℚ) ∉ v.asIdeal) :
    ρ.IsUnramifiedAt v := by
  obtain ⟨q, hq, rfl⟩ := exists_prime_toHeightOneSpectrumRingOfIntegersRat v
  refine hρ.isUnramified q hq ⟨?_, ?_⟩
  · rintro rfl
    exact hv2 rfl
  · rintro rfl
    exact hvp
      ((Nat.Prime.mem_toHeightOneSpectrumRingOfIntegersRat_asIdeal hq _).mpr (by simp))

section ConcreteCoefficientRing

/- The concrete coefficient rings of the realization stratum: for a
finite extension `L` of `ℚ_ℓ` inside `ℚ̄_ℓ`, the ring of integers
`IntegralClosure ℤ_[ℓ] L` (the vendored type synonym for
`integralClosure`), with the subspace topology inherited from the
spectral norm on `ℚ̄_ℓ`. The instance layer below equips it with
everything needed to STATE a hardly ramified representation over it —
topology, topological ring, local ring (via the spectral-norm
valuation dichotomy), the `ℤ_ℓ`-algebra structure and the embedding
into `ℚ̄_ℓ` — and proves module-finiteness over `ℤ_ℓ`
(`IsIntegralClosure.finite`, using that `ℤ_ℓ` is Noetherian and
integrally closed with fraction field `ℚ_ℓ`). -/

variable {ℓ : ℕ} [Fact ℓ.Prime] (L : IntermediateField ℚ_[ℓ] (AlgebraicClosure ℚ_[ℓ]))

/-- The subspace topology on the ring of integers of `L/ℚ_ℓ`, inherited
through `L ⊆ ℚ̄_ℓ` from the spectral-norm topology (PROVEN glue). -/
noncomputable instance instTopologicalSpaceIntegralClosurePadicInt :
    TopologicalSpace (IntegralClosure ℤ_[ℓ] L) :=
  inferInstanceAs (TopologicalSpace (integralClosure ℤ_[ℓ] L))

/-- The subspace topology makes the ring of integers a topological ring
(PROVEN glue: the subring instance on the underlying subtype). -/
instance instIsTopologicalRingIntegralClosurePadicInt :
    IsTopologicalRing (IntegralClosure ℤ_[ℓ] L) :=
  inferInstanceAs (IsTopologicalRing (integralClosure ℤ_[ℓ] L))

/-- The coefficient embedding `IntegralClosure ℤ_ℓ L → ℚ̄_ℓ`, the
composite of the subalgebra inclusion with `L ⊆ ℚ̄_ℓ` (PROVEN glue). -/
noncomputable instance instAlgebraIntegralClosurePadicIntAlgebraicClosure :
    Algebra (IntegralClosure ℤ_[ℓ] L) (AlgebraicClosure ℚ_[ℓ]) :=
  ((algebraMap L (AlgebraicClosure ℚ_[ℓ])).comp
    (algebraMap (IntegralClosure ℤ_[ℓ] L) L)).toAlgebra

/-- The embedding factors through `L` (PROVEN glue, definitional). -/
instance instIsScalarTowerIntegralClosureIntermediateFieldAlgebraicClosure :
    IsScalarTower (IntegralClosure ℤ_[ℓ] L) L (AlgebraicClosure ℚ_[ℓ]) :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

/-- `ℤ_ℓ → L → ℚ̄_ℓ` commutes (PROVEN glue: both routes factor through
`ℚ_ℓ`). -/
instance instIsScalarTowerPadicIntIntermediateFieldAlgebraicClosure :
    IsScalarTower ℤ_[ℓ] L (AlgebraicClosure ℚ_[ℓ]) :=
  IsScalarTower.of_algebraMap_eq fun x => by
    rw [IsScalarTower.algebraMap_apply ℤ_[ℓ] ℚ_[ℓ] (AlgebraicClosure ℚ_[ℓ]) x,
      IsScalarTower.algebraMap_apply ℤ_[ℓ] ℚ_[ℓ] L x,
      ← IsScalarTower.algebraMap_apply ℚ_[ℓ] L (AlgebraicClosure ℚ_[ℓ])]

/-- `ℤ_ℓ → IntegralClosure ℤ_ℓ L → ℚ̄_ℓ` commutes (PROVEN glue). -/
instance instIsScalarTowerPadicIntIntegralClosureAlgebraicClosure :
    IsScalarTower ℤ_[ℓ] (IntegralClosure ℤ_[ℓ] L) (AlgebraicClosure ℚ_[ℓ]) :=
  IsScalarTower.of_algebraMap_eq fun x => by
    rw [IsScalarTower.algebraMap_apply ℤ_[ℓ] L (AlgebraicClosure ℚ_[ℓ]) x]
    rfl

/-- The coefficient embedding of the concrete ring of integers into
`ℚ̄_ℓ` is injective (PROVEN glue: a composite of subtype inclusions). -/
lemma algebraMap_integralClosure_padicInt_injective : Function.Injective
    (algebraMap (IntegralClosure ℤ_[ℓ] L) (AlgebraicClosure ℚ_[ℓ])) := by
  have h1 : Function.Injective (algebraMap L (AlgebraicClosure ℚ_[ℓ])) :=
    (algebraMap L (AlgebraicClosure ℚ_[ℓ])).injective
  have h2 : Function.Injective (algebraMap (IntegralClosure ℤ_[ℓ] L) L) :=
    fun x y hxy => Subtype.ext hxy
  rw [IsScalarTower.algebraMap_eq (IntegralClosure ℤ_[ℓ] L) L (AlgebraicClosure ℚ_[ℓ])]
  exact h1.comp h2

/-- The type synonym is an integral closure of `ℤ_ℓ` in `L` (PROVEN
glue: the instance on the underlying subalgebra). -/
instance instIsIntegralClosureIntegralClosurePadicInt :
    IsIntegralClosure (IntegralClosure ℤ_[ℓ] L) ℤ_[ℓ] L :=
  inferInstanceAs (IsIntegralClosure (integralClosure ℤ_[ℓ] L) ℤ_[ℓ] L)

/-- The ring of integers of a finite extension `L/ℚ_ℓ` is module-finite
over `ℤ_ℓ` (PROVEN: `IsIntegralClosure.finite` — `ℤ_ℓ` is Noetherian
and integrally closed with fraction field `ℚ_ℓ`, and `L/ℚ_ℓ` is finite
separable in characteristic zero). -/
instance instModuleFiniteIntegralClosurePadicInt [FiniteDimensional ℚ_[ℓ] L] :
    Module.Finite ℤ_[ℓ] (IntegralClosure ℤ_[ℓ] L) :=
  IsIntegralClosure.finite ℤ_[ℓ] ℚ_[ℓ] L _

/-- **Spectral-norm integrality over `ℤ_ℓ`** (PROVEN): an element of an
algebraic extension of `ℚ_ℓ` with spectral norm at most `1` is integral
over `ℤ_ℓ` — its monic minimal polynomial over `ℚ_ℓ` has coefficients
of norm at most `1`, which lift termwise to `ℤ_ℓ`. (The `ℤ_ℓ`-avatar of
`isIntegral_of_spectralNorm_le_one` in `AbsoluteGaloisGroup.lean`,
which is stated for the `Valued.v.integer` subring of an abstractly
valued base field and so does not directly apply to `ℤ_[ℓ]`.) -/
lemma isIntegral_padicInt_of_spectralNorm_le_one
    {M : Type*} [Field M] [Algebra ℚ_[ℓ] M] [Algebra.IsAlgebraic ℚ_[ℓ] M]
    [Algebra ℤ_[ℓ] M] [IsScalarTower ℤ_[ℓ] ℚ_[ℓ] M]
    {x : M} (hx : spectralNorm ℚ_[ℓ] M x ≤ 1) : IsIntegral ℤ_[ℓ] x := by
  have hlift : minpoly ℚ_[ℓ] x ∈ Polynomial.lifts (algebraMap ℤ_[ℓ] ℚ_[ℓ]) := by
    refine (Polynomial.lifts_iff_coeff_lifts _).mpr fun i => ?_
    have hterm := (ciSup_le_iff (spectralValueTerms_bddAbove ..)).mp hx i
    simp only [spectralValueTerms] at hterm
    split_ifs at hterm with h
    · conv_rhs at hterm =>
        rw [← Real.one_rpow (1 / ((minpoly ℚ_[ℓ] x).natDegree - i : ℝ))]
      rw [Real.rpow_le_rpow_iff (by positivity) (by positivity) (by aesop)] at hterm
      exact ⟨⟨(minpoly ℚ_[ℓ] x).coeff i, hterm⟩, rfl⟩
    · obtain h | h := (le_of_not_gt h).eq_or_lt
      · refine ⟨1, ?_⟩
        rw [map_one, ← h]
        exact ((minpoly.monic
          (Algebra.IsAlgebraic.isAlgebraic x).isIntegral).coeff_natDegree).symm
      · exact ⟨0, by simp [Polynomial.coeff_eq_zero_of_natDegree_lt h]⟩
  obtain ⟨P, hP, _, hP'⟩ := Polynomial.lifts_and_degree_eq_and_monic hlift
    (minpoly.monic (Algebra.IsAlgebraic.isAlgebraic x).isIntegral)
  refine ⟨P, hP', ?_⟩
  rw [← Polynomial.aeval_def, ← Polynomial.aeval_map_algebraMap ℚ_[ℓ], hP, minpoly.aeval]

/-- The ring of integers of `L/ℚ_ℓ` is a valuation ring (PROVEN): the
spectral-norm dichotomy — every element of `L` of spectral norm at most
`1` is integral over `ℤ_ℓ`, and every element of larger norm has
integral inverse. (The `ℤ_ℓ`-avatar of `valuationRing_integralClosure`
in `AbsoluteGaloisGroup.lean`.) With `IsDomain`, this yields the
`IsLocalRing` instance that `IsHardlyRamified` statements over this
ring consume. -/
instance instValuationRingIntegralClosurePadicInt :
    ValuationRing (IntegralClosure ℤ_[ℓ] L) := by
  refine ValuationSubring.instValuationRingSubtypeMem
    ⟨(integralClosure ℤ_[ℓ] L).toSubring, ?_⟩
  intro x
  obtain hx | hx := le_total (spectralNorm ℚ_[ℓ] L x) 1
  · exact .inl (isIntegral_padicInt_of_spectralNorm_le_one hx)
  · have h1 := inv_le_one_of_one_le₀ hx
    rw [← spectralNorm_inv] at h1
    exact .inr (isIntegral_padicInt_of_spectralNorm_le_one h1)

/-- **Compact-Hausdorff criterion for the module topology** (PROVEN,
general): a topological module, finitely generated over a compact
topological ring, whose own topology is Hausdorff, carries the module
topology. The continuous identity map from the (compact — coinduced
along a surjection `Rⁿ ↠ M` from a compact space,
`ModuleTopology.eq_coinduced_of_surjective`) module topology to the
(Hausdorff) given topology is a homeomorphism
(`Continuous.homeoOfEquivCompactToT2`), so the two topologies agree.
(The abstraction of steps 3–5 of the PROVEN
`isModuleTopology_of_isAdic_maximalIdeal` in `Lift.lean`, which lives
downstream and cannot be imported here; stated over an abstract module
because instance synthesis at the `IntegralClosure` type synonym is
unreliable inside tactic blocks — binders sidestep it.) -/
theorem isModuleTopology_of_compactSpace_t2Space {R M : Type*} [CommRing R]
    [TopologicalSpace R] [IsTopologicalRing R] [CompactSpace R] [AddCommGroup M]
    [Module R M] [Module.Finite R M] [TopologicalSpace M] [T2Space M]
    [ContinuousSMul R M] [ContinuousAdd M] :
    IsModuleTopology R M := by
  obtain ⟨n, φ, hφ⟩ := Module.Finite.exists_fin' R M
  have hcoind : moduleTopology R M = TopologicalSpace.coinduced φ inferInstance :=
    ModuleTopology.eq_coinduced_of_surjective hφ
  have hφc : @Continuous (Fin n → R) M _ (moduleTopology R M) φ :=
    continuous_iff_coinduced_le.mpr (le_of_eq hcoind.symm)
  have hcompact : @CompactSpace M (moduleTopology R M) :=
    @Function.Surjective.compactSpace _ _ _ (moduleTopology R M) _ hφc
      inferInstance hφ
  have hid : @Continuous M M (moduleTopology R M) _ id :=
    continuous_id_iff_le.mpr (moduleTopology_le R M)
  exact IsModuleTopology.of_continuous_id
    (@Homeomorph.continuous_symm M _ (moduleTopology R M) _
      (@Continuous.homeoOfEquivCompactToT2 _ _ (moduleTopology R M) _ hcompact
        ‹T2Space M› (Equiv.refl _) hid))

/-- The structure map `ℤ_ℓ → 𝒪_L` is continuous for the subspace
topology (PROVEN): through the inclusions into `ℚ̄_ℓ` it is the
composite of the continuous `ℤ_ℓ ⊆ ℚ_ℓ → ℚ̄_ℓ`. (Stated at the
underlying `integralClosure` subalgebra.) -/
theorem continuous_algebraMap_integralClosure_padicInt :
    Continuous (algebraMap ℤ_[ℓ] (integralClosure ℤ_[ℓ] L)) := by
  have hcomp : Continuous (algebraMap ℤ_[ℓ] (AlgebraicClosure ℚ_[ℓ])) := by
    rw [IsScalarTower.algebraMap_eq ℤ_[ℓ] ℚ_[ℓ] (AlgebraicClosure ℚ_[ℓ])]
    exact (continuous_algebraMap ℚ_[ℓ] (AlgebraicClosure ℚ_[ℓ])).comp
      continuous_subtype_val
  have halgL : Continuous (algebraMap ℤ_[ℓ] L) := by
    refine continuous_induced_rng.mpr ?_
    have heq : ∀ z : ℤ_[ℓ],
        ((algebraMap ℤ_[ℓ] L z : L) : AlgebraicClosure ℚ_[ℓ]) =
          algebraMap ℤ_[ℓ] (AlgebraicClosure ℚ_[ℓ]) z := fun z =>
      (IsScalarTower.algebraMap_apply ℤ_[ℓ] L (AlgebraicClosure ℚ_[ℓ]) z).symm
    exact hcomp.congr fun z => (heq z).symm
  refine continuous_induced_rng.mpr ?_
  exact halgL.congr fun z => rfl

/-- **Module topology on the concrete ring of integers, subtype
spelling** (PROVEN): the compact-Hausdorff criterion applied to
`integralClosure ℤ_ℓ L` — the scalar action is continuous
(`continuous_algebraMap_integralClosure_padicInt`), `ℤ_ℓ` is compact,
the ring of integers is module-finite over it
(`IsIntegralClosure.finite`), and the subspace topology is Hausdorff
(metric). Stated at the underlying subalgebra, where instance synthesis
is reliable; the type-synonym form below is definitionally the same. -/
theorem isModuleTopology_integralClosure_subtype_padicInt
    [FiniteDimensional ℚ_[ℓ] L] :
    IsModuleTopology ℤ_[ℓ] (integralClosure ℤ_[ℓ] L) := by
  haveI : ContinuousSMul ℤ_[ℓ] (integralClosure ℤ_[ℓ] L) :=
    continuousSMul_of_algebraMap ℤ_[ℓ] (integralClosure ℤ_[ℓ] L)
      (continuous_algebraMap_integralClosure_padicInt L)
  haveI : Module.Finite ℤ_[ℓ] (integralClosure ℤ_[ℓ] L) :=
    IsIntegralClosure.finite ℤ_[ℓ] ℚ_[ℓ] L _
  exact isModuleTopology_of_compactSpace_t2Space
    (R := ℤ_[ℓ]) (M := integralClosure ℤ_[ℓ] L)

/-- **Module topology on the concrete ring of integers** (PROVEN): the
subspace topology on `IntegralClosure ℤ_ℓ L ⊆ L ⊆ ℚ̄_ℓ` (inherited
from the spectral norm) is the `ℤ_ℓ`-module topology, for `L/ℚ_ℓ`
finite — the subtype-spelling proof transported along the definitional
equality of the type synonym. -/
theorem isModuleTopology_integralClosure_padicInt [FiniteDimensional ℚ_[ℓ] L] :
    IsModuleTopology ℤ_[ℓ] (IntegralClosure ℤ_[ℓ] L) :=
  isModuleTopology_integralClosure_subtype_padicInt L

/-- **Universe/abstraction transport of a concrete realization** (sorry
node, purely formal — no arithmetic content): a hardly ramified
representation `τ₀` over a coefficient ring `A₀` in `Type 0` carrying
the full coefficient-ring package (module-finite local topological
`ℤ_ℓ`-algebra with the module topology, embedded in `ℚ̄_ℓ`), together
with its framing and its unramified/charpoly-matching behaviour away
from `T`, transports to the SAME package with the coefficient ring in
an arbitrary universe `Type u` — the shape demanded by the abstract
realization telescope. Proof plan: take `A := ULift.{u} A₀` with the
instances transported along `ULift.ringEquiv` (mathlib provides the
ring, topology and `IsTopologicalRing` instances; the module structure
on `W₀` restricts along the equivalence), conjugate `τ₀` by the
identity-on-elements equivalence of endomorphism monoids (the module
topologies correspond along the homeomorphic ring equivalence),
transport `IsHardlyRamified` field by field (`det` via the commuting
triangle of structure maps, unramifiedness via equality of kernels,
flatness via `HasFlatProlongationAt.of_equiv`, tameness by composing
`π` with `ULift.up`), and match Frobenius characteristic polynomials
via invariance of `LinearMap.charpoly` under the scalar-relabeling
equivalence. -/
theorem exists_realization_package_of_concrete (hℓodd : Odd ℓ)
    {A₀ : Type} [CommRing A₀] [TopologicalSpace A₀] [IsTopologicalRing A₀]
    [IsLocalRing A₀] [Algebra ℤ_[ℓ] A₀] [Module.Finite ℤ_[ℓ] A₀]
    [Algebra A₀ (AlgebraicClosure ℚ_[ℓ])]
    [IsScalarTower ℤ_[ℓ] A₀ (AlgebraicClosure ℚ_[ℓ])]
    [IsModuleTopology ℤ_[ℓ] A₀]
    (hA₀inj : Function.Injective (algebraMap A₀ (AlgebraicClosure ℚ_[ℓ])))
    {W₀ : Type v} [AddCommGroup W₀] [Module A₀ W₀] [Module.Finite A₀ W₀]
    [Module.Free A₀ W₀]
    (hW₀ : Module.rank A₀ W₀ = 2) (τ₀ : GaloisRep ℚ A₀ W₀)
    (r₀ : AlgebraicClosure ℚ_[ℓ] ⊗[A₀] W₀ ≃ₗ[AlgebraicClosure ℚ_[ℓ]]
      Fin 2 → AlgebraicClosure ℚ_[ℓ])
    (hτ₀ : IsHardlyRamified hℓodd hW₀ τ₀)
    (T : Finset (HeightOneSpectrum (NumberField.RingOfIntegers ℚ)))
    (Q : HeightOneSpectrum (NumberField.RingOfIntegers ℚ) →
      Polynomial (AlgebraicClosure ℚ_[ℓ]))
    (hmatch : ∀ v ∉ T, (ℓ : NumberField.RingOfIntegers ℚ) ∉ v.asIdeal →
      τ₀.IsUnramifiedAt v ∧
      (τ₀.charFrob v).map (algebraMap A₀ (AlgebraicClosure ℚ_[ℓ])) = Q v) :
    ∃ (A : Type u) (_ : CommRing A) (_ : TopologicalSpace A)
      (_ : IsTopologicalRing A) (_ : IsLocalRing A) (_ : Algebra ℤ_[ℓ] A)
      (_ : Module.Finite ℤ_[ℓ] A)
      (_ : Algebra A (AlgebraicClosure ℚ_[ℓ]))
      (_ : IsScalarTower ℤ_[ℓ] A (AlgebraicClosure ℚ_[ℓ]))
      (_ : IsModuleTopology ℤ_[ℓ] A)
      (_ : Function.Injective (algebraMap A (AlgebraicClosure ℚ_[ℓ])))
      (W : Type v) (_ : AddCommGroup W) (_ : Module A W) (_ : Module.Finite A W)
      (_ : Module.Free A W) (hW : Module.rank A W = 2)
      (τ : GaloisRep ℚ A W)
      (_r : AlgebraicClosure ℚ_[ℓ] ⊗[A] W ≃ₗ[AlgebraicClosure ℚ_[ℓ]]
        Fin 2 → AlgebraicClosure ℚ_[ℓ]),
      IsHardlyRamified hℓodd hW τ ∧
      ∀ v ∉ T, (ℓ : NumberField.RingOfIntegers ℚ) ∉ v.asIdeal →
        τ.IsUnramifiedAt v ∧
        (τ.charFrob v).map (algebraMap A (AlgebraicClosure ℚ_[ℓ])) = Q v :=
  sorry

end ConcreteCoefficientRing

/-- **Automorphy core over concrete rings of integers, odd residue
characteristics** (sorry node): the eigensystem `(E, S, Pv)` attached
to a hardly ramified `p`-adic representation is realized *integrally*
at every odd prime `ℓ` and embedding `φ : E →+* ℚ̄_ℓ`, with the
coefficient ring CONCRETE: there are a finite extension `L/ℚ_ℓ` inside
`ℚ̄_ℓ` and a hardly ramified representation `τ` over its ring of
integers `IntegralClosure ℤ_ℓ L` (with a framing `r` of its base
extension) which, away from a single finite exceptional set `T` ("the
level", uniform in `(ℓ, φ)`) and the places over `ℓ`, is unramified
with Frobenius characteristic polynomials mapping to `(Pv v).map φ`.
This is Eichler–Shimura/Deligne (the `λ`-adic representations attached
to the weight-2 eigenform underlying the eigensystem) with the lattice
argument giving the integral model — the coefficient field of the
`λ`-adic representation is the finite extension of `ℚ_ℓ` generated by
the Hecke eigenvalues, and stabilizing a lattice puts the
representation over its ring of integers, which is exactly
`IntegralClosure ℤ_ℓ L` — plus local–global compatibility (Carayol,
Saito) for the unramifiedness and charpoly matching, plus the weight-2
level-2 analysis showing the model is hardly ramified. Strictly
shallower than the abstract-coefficient core below (DECOMPOSITION
2026-07-23): the whole instance telescope of the abstract statement is
here replaced by the single geometric datum `(L, FiniteDimensional)` —
the topology, topological-ring, local-ring, `ℤ_ℓ`-algebra,
module-finiteness and embedding fields are all PROVEN instances of the
`ConcreteCoefficientRing` layer above, and the universe quantification
is gone (the transport back to `Type u` is the separate formal leaf
`exists_realization_package_of_concrete`).

The VOCABULARY OBSTRUCTION and SOUNDNESS AUDIT notes on the abstract
core below apply verbatim to this leaf: the integral hardly ramified
model must be produced by the automorphy argument itself (matching
charpolys outside a finite set do not pin the isomorphism class), and
no Hecke-eigenform carrier type is statable on this mathlib pin, so
the leaf keeps the fused Eichler–Shimura + integrality + hardly
ramified shape. -/
theorem exists_hardlyRamified_ringOfIntegers_realizations
    [Algebra R (AlgebraicClosure ℚ_[p])]
    [ContinuousSMul R (AlgebraicClosure ℚ_[p])]
    (hZinj : Function.Injective (algebraMap ℤ_[p] R))
    (hRinj : Function.Injective (algebraMap R (AlgebraicClosure ℚ_[p])))
    (hρ : IsHardlyRamified hpodd hv ρ)
    {E : Type v} [Field E] [NumberField E] (ψ : E →+* AlgebraicClosure ℚ_[p])
    (S : Finset (HeightOneSpectrum (NumberField.RingOfIntegers ℚ)))
    (Pv : HeightOneSpectrum (NumberField.RingOfIntegers ℚ) → Polynomial E)
    (heig : ∀ v ∉ S,
      (ρ.charFrob v).map (algebraMap R (AlgebraicClosure ℚ_[p])) = (Pv v).map ψ) :
    ∃ (T : Finset (HeightOneSpectrum (NumberField.RingOfIntegers ℚ))),
      ∀ (ℓ : ℕ) (hℓ : Fact ℓ.Prime) (hℓodd : Odd ℓ)
        (φ : E →+* AlgebraicClosure ℚ_[ℓ]),
      ∃ (L : IntermediateField ℚ_[ℓ] (AlgebraicClosure ℚ_[ℓ]))
        (_ : FiniteDimensional ℚ_[ℓ] L)
        (W : Type v) (_ : AddCommGroup W)
        (_ : Module (IntegralClosure ℤ_[ℓ] L) W)
        (_ : Module.Finite (IntegralClosure ℤ_[ℓ] L) W)
        (_ : Module.Free (IntegralClosure ℤ_[ℓ] L) W)
        (hW : Module.rank (IntegralClosure ℤ_[ℓ] L) W = 2)
        (τ : GaloisRep ℚ (IntegralClosure ℤ_[ℓ] L) W)
        (r : AlgebraicClosure ℚ_[ℓ] ⊗[IntegralClosure ℤ_[ℓ] L] W
          ≃ₗ[AlgebraicClosure ℚ_[ℓ]] Fin 2 → AlgebraicClosure ℚ_[ℓ]),
        IsHardlyRamified hℓodd hW τ ∧
        ∀ v ∉ T, (ℓ : NumberField.RingOfIntegers ℚ) ∉ v.asIdeal →
          τ.IsUnramifiedAt v ∧
          (τ.charFrob v).map
              (algebraMap (IntegralClosure ℤ_[ℓ] L) (AlgebraicClosure ℚ_[ℓ])) =
            (Pv v).map φ :=
  sorry

/-- **Automorphy core of the realization stratum, odd residue
characteristics** (DECOMPOSED 2026-07-23 into the concrete automorphy
leaf `exists_hardlyRamified_ringOfIntegers_realizations`, the formal
transport leaf `exists_realization_package_of_concrete` and the
topology leaf `isModuleTopology_integralClosure_padicInt`, glued by the
PROVEN `ConcreteCoefficientRing` instance layer; the assembly below is
proven): the eigensystem `(E, S, Pv)` attached
to a hardly ramified `p`-adic representation is realized *integrally*
at every odd prime `ℓ` and embedding `φ : E →+* ℚ̄_ℓ`: there is a
hardly ramified representation `τ` over a module-finite local
`ℤ_ℓ`-algebra `A ↪ ℚ̄_ℓ` (with a framing `r` of its base extension)
which, away from a single finite exceptional set `T` ("the level",
uniform in `(ℓ, φ)`) and the places over `ℓ`, is unramified with
Frobenius characteristic polynomials mapping to `(Pv v).map φ`. This
is Eichler–Shimura/Deligne (the `λ`-adic representations attached to
the weight-2 eigenform underlying the eigensystem) with the lattice
argument giving the integral model, plus local–global compatibility
(Carayol, Saito) for the unramifiedness and charpoly matching, plus
the weight-2 level-2 analysis showing the model is hardly ramified.

VOCABULARY OBSTRUCTION (2026-07-23, recording why the requested
"(a) a weight-2 newform-like eigensystem datum matching `Pv`;
(b) Deligne: the datum yields each `(ℓ, φ)` member" split is NOT
statable on this pin: the pattern established at
`exists_numberField_eigensystem`): mathlib has `ModularForm`/`CuspForm`
but no Hecke operators, no eigenforms, and no Galois representations
attached to them, so a "newform-like datum" has no carrier type. The
reference FLT project states the datum as an `ℤ_p`-algebra hom
`π : HeckeAlgebra D … →ₐ[ℤ_[p]] A` out of a quaternionic Hecke algebra
(`GaloisRep.IsAutomorphicOfLevel`,
`FLT/GaloisRepresentation/Automorphic.lean`), but its entire
`AutomorphicForm/QuaternionAlgebra` tower is absent from both the
mathlib pin and the vendored subset, so that interface cannot be
vendored as a leaf statement here.

SOUNDNESS AUDIT (2026-07-23, why the hardly ramified model is fused
with the member existence instead of derived from it): the tempting
intermediate interface "any member `m` matching `Pv` outside `T`
admits a hardly ramified integral model" is FALSE — the same
Brauer–Nesbitt trap as the rejected alternative in the DECOMPOSITION
AUDIT on `exists_family_of_eigensystem`: matching Frobenius charpolys
outside a finite set do not pin the isomorphism class of `m`, and a
rogue non-semisimple `m` ramified at an auxiliary prime matches the
charpolys of a hardly ramified representation without being one. So
the integral model must be produced BY the automorphy leaf, and the
`(ℓ, φ)` member of `exists_realizations_of_eigensystem` is DERIVED
from it by the proven base-change/conjugation glue there — i.e. the
"datum ⇒ member" (Deligne-direction) arrow is the PROVEN half, and
this leaf is the sole surviving automorphy sorry at odd `ℓ`.

TELESCOPE NOTE (2026-07-23): this is the MINIMAL instance telescope for
the integral model — of the coefficient-ring package demanded by
`IsInHardlyRamifiedFamily`, the fields `Module.Free ℤ_[ℓ] A`,
`IsDomain A` and `ContinuousSMul A ℚ̄_ℓ` are OMITTED here because they
are formally derivable from the remaining ones (torsion-free + finite
over the PID `ℤ_[ℓ]` gives freeness; injectivity into the field `ℚ̄_ℓ`
gives the domain; the module topology makes the `ℤ_[ℓ]`-linear
coefficient embedding automatically continuous): the derivations are
the PROVEN assembly `exists_hardlyRamified_integral_realizations`
below. The fields kept are either statement-relevant
(`IsTopologicalRing`/`IsLocalRing` are binders of `IsHardlyRamified`
itself; the topology carries the continuity of `τ`) or genuinely
pin data (`IsModuleTopology`, the `ℤ_[ℓ]`-structure, the embedding). -/
theorem exists_hardlyRamified_integral_realizations_core
    [Algebra R (AlgebraicClosure ℚ_[p])]
    [ContinuousSMul R (AlgebraicClosure ℚ_[p])]
    (hZinj : Function.Injective (algebraMap ℤ_[p] R))
    (hRinj : Function.Injective (algebraMap R (AlgebraicClosure ℚ_[p])))
    (hρ : IsHardlyRamified hpodd hv ρ)
    {E : Type v} [Field E] [NumberField E] (ψ : E →+* AlgebraicClosure ℚ_[p])
    (S : Finset (HeightOneSpectrum (NumberField.RingOfIntegers ℚ)))
    (Pv : HeightOneSpectrum (NumberField.RingOfIntegers ℚ) → Polynomial E)
    (heig : ∀ v ∉ S,
      (ρ.charFrob v).map (algebraMap R (AlgebraicClosure ℚ_[p])) = (Pv v).map ψ) :
    ∃ (T : Finset (HeightOneSpectrum (NumberField.RingOfIntegers ℚ))),
      ∀ (ℓ : ℕ) (_hℓ : Fact ℓ.Prime) (hℓodd : Odd ℓ)
        (φ : E →+* AlgebraicClosure ℚ_[ℓ]),
      ∃ (A : Type u) (_ : CommRing A) (_ : TopologicalSpace A)
        (_ : IsTopologicalRing A) (_ : IsLocalRing A) (_ : Algebra ℤ_[ℓ] A)
        (_ : Module.Finite ℤ_[ℓ] A)
        (_ : Algebra A (AlgebraicClosure ℚ_[ℓ]))
        (_ : IsScalarTower ℤ_[ℓ] A (AlgebraicClosure ℚ_[ℓ]))
        (_ : IsModuleTopology ℤ_[ℓ] A)
        (_ : Function.Injective (algebraMap A (AlgebraicClosure ℚ_[ℓ])))
        (W : Type v) (_ : AddCommGroup W) (_ : Module A W) (_ : Module.Finite A W)
        (_ : Module.Free A W) (hW : Module.rank A W = 2)
        (τ : GaloisRep ℚ A W)
        (_r : AlgebraicClosure ℚ_[ℓ] ⊗[A] W ≃ₗ[AlgebraicClosure ℚ_[ℓ]]
          Fin 2 → AlgebraicClosure ℚ_[ℓ]),
        IsHardlyRamified hℓodd hW τ ∧
        ∀ v ∉ T, (ℓ : NumberField.RingOfIntegers ℚ) ∉ v.asIdeal →
          τ.IsUnramifiedAt v ∧
          (τ.charFrob v).map (algebraMap A (AlgebraicClosure ℚ_[ℓ])) =
            (Pv v).map φ := by
  obtain ⟨T, hT⟩ := exists_hardlyRamified_ringOfIntegers_realizations hpodd hv
    hZinj hRinj hρ ψ S Pv heig
  refine ⟨T, ?_⟩
  intro ℓ hℓ hℓodd φ
  haveI := hℓ
  obtain ⟨L, hLfin, W₀, iW1, iW2, iW3, iW4, hW₀, τ₀, r₀, hτ₀, hmatch⟩ :=
    hT ℓ hℓ hℓodd φ
  letI := iW1; letI := iW2; letI := iW3; letI := iW4
  haveI := hLfin
  haveI : IsModuleTopology ℤ_[ℓ] (IntegralClosure ℤ_[ℓ] L) :=
    isModuleTopology_integralClosure_padicInt L
  exact exists_realization_package_of_concrete hℓodd
    (algebraMap_integralClosure_padicInt_injective L) hW₀ τ₀ r₀ hτ₀ T
    (fun w => (Pv w).map φ) hmatch

/-- **Automorphy core of the realization stratum, odd residue
characteristics — full instance package** (PROVEN assembly): the
statement of the former sorry node in the shape its consumer
`exists_realizations_of_eigensystem` uses, DECOMPOSED (2026-07-23)
into a PROVEN assembly over the strictly shallower
`exists_hardlyRamified_integral_realizations_core` (see the TELESCOPE
NOTE there): the three omitted coefficient-ring fields are derived
here — `Module.Free ℤ_[ℓ] A` from module-finiteness plus
torsion-freeness (the coefficient embedding into `ℚ̄_ℓ` is injective
and `ℤ_[ℓ] → ℚ̄_ℓ` is injective, so `ℤ_[ℓ] → A` is injective and `A`
is torsion-free over the PID `ℤ_[ℓ]`), `IsDomain A` by pulling back
along the injective embedding into the field `ℚ̄_ℓ`, and
`ContinuousSMul A ℚ̄_ℓ` because the coefficient embedding is
`ℤ_[ℓ]`-linear out of the module topology
(`IsModuleTopology.continuous_of_linearMap`). -/
theorem exists_hardlyRamified_integral_realizations
    [Algebra R (AlgebraicClosure ℚ_[p])]
    [ContinuousSMul R (AlgebraicClosure ℚ_[p])]
    (hZinj : Function.Injective (algebraMap ℤ_[p] R))
    (hRinj : Function.Injective (algebraMap R (AlgebraicClosure ℚ_[p])))
    (hρ : IsHardlyRamified hpodd hv ρ)
    {E : Type v} [Field E] [NumberField E] (ψ : E →+* AlgebraicClosure ℚ_[p])
    (S : Finset (HeightOneSpectrum (NumberField.RingOfIntegers ℚ)))
    (Pv : HeightOneSpectrum (NumberField.RingOfIntegers ℚ) → Polynomial E)
    (heig : ∀ v ∉ S,
      (ρ.charFrob v).map (algebraMap R (AlgebraicClosure ℚ_[p])) = (Pv v).map ψ) :
    ∃ (T : Finset (HeightOneSpectrum (NumberField.RingOfIntegers ℚ))),
      ∀ (ℓ : ℕ) (_hℓ : Fact ℓ.Prime) (hℓodd : Odd ℓ)
        (φ : E →+* AlgebraicClosure ℚ_[ℓ]),
      ∃ (A : Type u) (_ : CommRing A) (_ : TopologicalSpace A)
        (_ : IsTopologicalRing A) (_ : IsLocalRing A) (_ : Algebra ℤ_[ℓ] A)
        (_ : Module.Finite ℤ_[ℓ] A) (_ : Module.Free ℤ_[ℓ] A) (_ : IsDomain A)
        (_ : Algebra A (AlgebraicClosure ℚ_[ℓ]))
        (_ : IsScalarTower ℤ_[ℓ] A (AlgebraicClosure ℚ_[ℓ]))
        (_ : IsModuleTopology ℤ_[ℓ] A)
        (_ : ContinuousSMul A (AlgebraicClosure ℚ_[ℓ]))
        (_ : Function.Injective (algebraMap A (AlgebraicClosure ℚ_[ℓ])))
        (W : Type v) (_ : AddCommGroup W) (_ : Module A W) (_ : Module.Finite A W)
        (_ : Module.Free A W) (hW : Module.rank A W = 2)
        (τ : GaloisRep ℚ A W)
        (_r : AlgebraicClosure ℚ_[ℓ] ⊗[A] W ≃ₗ[AlgebraicClosure ℚ_[ℓ]]
          Fin 2 → AlgebraicClosure ℚ_[ℓ]),
        IsHardlyRamified hℓodd hW τ ∧
        ∀ v ∉ T, (ℓ : NumberField.RingOfIntegers ℚ) ∉ v.asIdeal →
          τ.IsUnramifiedAt v ∧
          (τ.charFrob v).map (algebraMap A (AlgebraicClosure ℚ_[ℓ])) =
            (Pv v).map φ := by
  obtain ⟨T, hT⟩ :=
    exists_hardlyRamified_integral_realizations_core hpodd hv hZinj hRinj hρ ψ S Pv heig
  refine ⟨T, ?_⟩
  intro ℓ hℓ hℓodd φ
  haveI := hℓ
  obtain ⟨A, iA1, iA2, iA3, iA4, iA5, iA6, iA10, iA11, iA12, hAinj,
    W, iW1, iW2, iW3, iW4, hW, τ, r, hτ, hmatch⟩ := hT ℓ hℓ hℓodd φ
  letI := iA1; letI := iA2; letI := iA3; letI := iA4; letI := iA5; letI := iA6
  letI := iA10; letI := iA11; letI := iA12
  -- `ℤ_[ℓ]` embeds into `ℚ̄_ℓ`, hence into `A` through the tower
  have hZbarinj : Function.Injective (algebraMap ℤ_[ℓ] (AlgebraicClosure ℚ_[ℓ])) := by
    rw [IsScalarTower.algebraMap_eq ℤ_[ℓ] ℚ_[ℓ] (AlgebraicClosure ℚ_[ℓ])]
    exact (algebraMap ℚ_[ℓ] (AlgebraicClosure ℚ_[ℓ])).injective.comp
      (FaithfulSMul.algebraMap_injective ℤ_[ℓ] ℚ_[ℓ])
  have hZAinj : Function.Injective (algebraMap ℤ_[ℓ] A) := by
    intro x y hxy
    apply hZbarinj
    rw [IsScalarTower.algebraMap_eq ℤ_[ℓ] A (AlgebraicClosure ℚ_[ℓ]),
      RingHom.comp_apply, RingHom.comp_apply, hxy]
  -- the three derived coefficient-ring fields
  haveI iA8 : IsDomain A := hAinj.isDomain _
  haveI : Module.IsTorsionFree ℤ_[ℓ] A :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr hZAinj
  haveI iA7 : Module.Free ℤ_[ℓ] A := Module.free_of_finite_type_torsion_free'
  haveI : ContinuousSMul ℤ_[ℓ] (AlgebraicClosure ℚ_[ℓ]) :=
    continuousSMul_of_algebraMap _ _
      ((continuous_algebraMap ℚ_[ℓ] _).comp continuous_subtype_val)
  haveI iA13 : ContinuousSMul A (AlgebraicClosure ℚ_[ℓ]) :=
    continuousSMul_of_algebraMap _ _
      (IsModuleTopology.continuous_of_linearMap
        (IsScalarTower.toAlgHom ℤ_[ℓ] A (AlgebraicClosure ℚ_[ℓ])).toLinearMap)
  exact ⟨A, iA1, iA2, iA3, iA4, iA5, iA6, iA7, iA8, iA10, iA11, iA12, iA13, hAinj,
    W, iW1, iW2, iW3, iW4, hW, τ, r, hτ, hmatch⟩

/-- **Automorphy atom at the even prime, generated coefficients** (sorry
node): given a finite-dimensional coefficient subfield `K ⊆ ℚ̄_₂` which
is EXACTLY the subfield generated over `ℚ_2` by the image of the
eigensystem's number field under `φ₀ : E →+* K` (the hypothesis
`hgen`), the eigensystem `(E, S, Pv)` is realized over `K` itself: a
representation `τ : G_ℚ → GL₂(K)`, unramified outside a finite
exceptional `T` (which absorbs the single place of `ℚ` above `2`) with
Frobenius characteristic polynomials `(Pv v).map φ₀` there. This is
EXACTLY the output shape of Eichler–Shimura/Deligne at `λ | 2`
(Diamond–Shurman §9.5–9.6) plus local–global compatibility
(Carayol/Saito): the `λ`-adic representation attached to the weight-2
eigenform underlying the eigensystem is defined over the completion
`E_λ = ℚ_2(φ₀(E))` — which `hgen` makes equal to `K`, with zero
base-change slack left inside the sorry (the spreading to a LARGER
finite-dimensional coefficient field is the PROVEN glue
`exists_realization_at_two_confined` below). No hardly-ramifiedness
demand is made (the notion requires odd residue characteristic) and no
`ℤ_2`-integral model is demanded — contrast the SOUNDNESS AUDIT at
`exists_hardlyRamified_integral_realizations_core`, where the hardly
ramified clause forces the integral model into the leaf; at `ℓ = 2`
the consumer needs only the bare member, so this atom stays at the
field level. The VOCABULARY OBSTRUCTION note there applies verbatim:
no Hecke-eigenform carrier type is statable on this pin, so the leaf
keeps the fused Eichler–Shimura + local–global shape. -/
theorem exists_realization_at_two_generated
    [Algebra R (AlgebraicClosure ℚ_[p])]
    [ContinuousSMul R (AlgebraicClosure ℚ_[p])]
    (hZinj : Function.Injective (algebraMap ℤ_[p] R))
    (hRinj : Function.Injective (algebraMap R (AlgebraicClosure ℚ_[p])))
    (hρ : IsHardlyRamified hpodd hv ρ)
    {E : Type v} [Field E] [NumberField E] (ψ : E →+* AlgebraicClosure ℚ_[p])
    (S : Finset (HeightOneSpectrum (NumberField.RingOfIntegers ℚ)))
    (Pv : HeightOneSpectrum (NumberField.RingOfIntegers ℚ) → Polynomial E)
    (heig : ∀ v ∉ S,
      (ρ.charFrob v).map (algebraMap R (AlgebraicClosure ℚ_[p])) = (Pv v).map ψ)
    (K : IntermediateField ℚ_[2] (AlgebraicClosure ℚ_[2]))
    [FiniteDimensional ℚ_[2] K] (φ₀ : E →+* K)
    (hgen : K = IntermediateField.adjoin ℚ_[2]
      (Set.range fun x : E => (φ₀ x : AlgebraicClosure ℚ_[2]))) :
    ∃ (T : Finset (HeightOneSpectrum (NumberField.RingOfIntegers ℚ)))
      (τ : GaloisRep ℚ K (Fin 2 → K)),
      ∀ v ∉ T, τ.IsUnramifiedAt v ∧ τ.charFrob v = (Pv v).map φ₀ :=
  sorry

/-- **Automorphy stratum at the even prime, confined coefficients**
(PROVEN assembly, see the DECOMPOSED note below): given ANY
finite-dimensional coefficient subfield `K ⊆ ℚ̄_₂` and
an embedding `φ₀ : E →+* K` of the eigensystem's number field, the
eigensystem `(E, S, Pv)` is realized over `K` itself: a representation
`τ : G_ℚ → GL₂(K)`, unramified outside a finite exceptional `T` (which
absorbs the single place of `ℚ` above `2`) with Frobenius
characteristic polynomials `(Pv v).map φ₀` there.

DECOMPOSITION AUDIT (2026-07-23): this stratum is
`exists_realization_at_two_of_embedding_core` below with its entire
existential coefficient telescope `(K, FiniteDimensional, φ₀, compat)`
peeled off into hypotheses — the assembly there constructs the
concrete `K₀ = ℚ_2(φ('' spanning set of E))` and corestricts `φ`
through it, all PROVEN.

DECOMPOSED (2026-07-23) into a PROVEN assembly over the strictly
shallower sorried atom `exists_realization_at_two_generated` above,
which fixes the coefficient field to be EXACTLY the subfield generated
by the image of `E` — the literal Eichler–Shimura output `E_λ`. The
spreading from the generated subfield `Kmin = ℚ_2(φ₀(E)) ≤ K` to `K`
is base-change slack, PROVEN here: `Kmin` is finite-dimensional
because the `IntermediateField.inclusion` into `K` is an injective
`ℚ_2`-linear map, the coefficient extension is framed by
`Basis.baseChange` of the standard basis followed by `Basis.equivFun`,
the scalar action of `Kmin` on `K` is continuous because the inclusion
of subspace topologies is, unramifiedness transports through the
`baseChange` instance of `GaloisRep.IsUnramifiedAt` plus
`isUnramifiedAt_conj`, and the charpoly matching through
`charFrob_baseChange_conj` and `Polynomial.map_map` (the corestriction
of `φ₀` through `Kmin` recombines the coefficient maps
definitionally). -/
theorem exists_realization_at_two_confined
    [Algebra R (AlgebraicClosure ℚ_[p])]
    [ContinuousSMul R (AlgebraicClosure ℚ_[p])]
    (hZinj : Function.Injective (algebraMap ℤ_[p] R))
    (hRinj : Function.Injective (algebraMap R (AlgebraicClosure ℚ_[p])))
    (hρ : IsHardlyRamified hpodd hv ρ)
    {E : Type v} [Field E] [NumberField E] (ψ : E →+* AlgebraicClosure ℚ_[p])
    (S : Finset (HeightOneSpectrum (NumberField.RingOfIntegers ℚ)))
    (Pv : HeightOneSpectrum (NumberField.RingOfIntegers ℚ) → Polynomial E)
    (heig : ∀ v ∉ S,
      (ρ.charFrob v).map (algebraMap R (AlgebraicClosure ℚ_[p])) = (Pv v).map ψ)
    (K : IntermediateField ℚ_[2] (AlgebraicClosure ℚ_[2]))
    [FiniteDimensional ℚ_[2] K] (φ₀ : E →+* K) :
    ∃ (T : Finset (HeightOneSpectrum (NumberField.RingOfIntegers ℚ)))
      (τ : GaloisRep ℚ K (Fin 2 → K)),
      ∀ v ∉ T, τ.IsUnramifiedAt v ∧ τ.charFrob v = (Pv v).map φ₀ := by
  classical
  -- the subfield of `K` generated by the image of `E`
  let Φ : E →+* AlgebraicClosure ℚ_[2] :=
    (algebraMap K (AlgebraicClosure ℚ_[2])).comp φ₀
  let Kmin : IntermediateField ℚ_[2] (AlgebraicClosure ℚ_[2]) :=
    IntermediateField.adjoin ℚ_[2] (Set.range fun x : E => Φ x)
  let φ₀min : E →+* Kmin :=
    Φ.codRestrict _ fun x => IntermediateField.subset_adjoin _ _ ⟨x, rfl⟩
  -- the generated subfield sits inside `K` ...
  have hle : Kmin ≤ K := IntermediateField.adjoin_le_iff.mpr (by
    rintro - ⟨x, rfl⟩
    exact (φ₀ x).2)
  -- ... hence is finite-dimensional over `ℚ_2`
  haveI : FiniteDimensional ℚ_[2] Kmin :=
    FiniteDimensional.of_injective (IntermediateField.inclusion hle).toLinearMap
      (IntermediateField.inclusion_injective hle)
  -- the minimal realization, over exactly the generated subfield
  obtain ⟨T, τ, hT⟩ := exists_realization_at_two_generated hpodd hv hZinj hRinj hρ ψ S Pv
    heig Kmin φ₀min rfl
  -- coefficient extension along `Kmin ↪ K`
  letI : Algebra Kmin K := (IntermediateField.inclusion hle).toRingHom.toAlgebra
  haveI : ContinuousSMul Kmin K :=
    continuousSMul_of_algebraMap _ _ (continuous_subtype_val.subtype_mk _)
  -- the framing of the base extension
  let r : K ⊗[Kmin] (Fin 2 → Kmin) ≃ₗ[K] (Fin 2 → K) :=
    ((Pi.basisFun Kmin (Fin 2)).baseChange K).equivFun
  -- `φ₀` factors through `Kmin` as ring homomorphisms
  have hcomp : (algebraMap Kmin K).comp φ₀min = φ₀ :=
    RingHom.ext fun x => Subtype.ext rfl
  refine ⟨T, (τ.baseChange K).conj r, ?_⟩
  intro v hvT
  obtain ⟨hunr, hchar⟩ := hT v hvT
  haveI := hunr
  refine ⟨isUnramifiedAt_conj (τ.baseChange K) r v, ?_⟩
  rw [charFrob_baseChange_conj τ r v, hchar, Polynomial.map_map, hcomp]

/-- **Automorphy core at the even prime, per embedding** (PROVEN
assembly, see the DECOMPOSED note below): the eigensystem `(E, S, Pv)`
is realized at `λ | 2` at a single given
embedding `φ : E →+* ℚ̄_₂` by a representation over a coefficient field
`K` which is a FINITE-DIMENSIONAL subfield of `ℚ̄_₂` through which `φ`
factors — the exact output shape of Eichler–Shimura/Deligne: the
`λ`-adic representation attached to the weight-2 eigenform underlying
the eigensystem is defined over the completion `E_λ = ℚ_2(φ(E))`, a
finite extension of `ℚ_2` (Diamond–Shurman §9.5–9.6; Carayol/Saito
local–global compatibility for the unramifiedness and the charpoly
matching). The exceptional set `T` absorbs the (single!) place of
`ℚ` above `2`, so no "away from `2`" proviso appears; the
finite-dimensionality of `K` over `ℚ_2` is the even-prime counterpart
of the coefficient confinement demanded by the odd-`ℓ` core's
module-finite `ℤ_ℓ`-algebra.

DECOMPOSED (2026-07-23) into a PROVEN assembly over one strictly
shallower sorried leaf, `exists_realization_at_two_confined` above,
which receives the coefficient pair `(K, φ₀)` as HYPOTHESES: the whole
existential coefficient telescope is constructed here — `K` is `ℚ_2`
with the `φ`-images of a finite `ℚ`-spanning set of the number field
`E` adjoined (finite-dimensional because each generator is integral
over `ℚ_2`: it is a root of the image of its monic `ℚ`-minimal
polynomial, ring homs out of `ℚ` being unique), the image of ALL of
`E` lands in `K` by span induction (the `ℚ`-scalars fall into `K`
through `ℚ ⊆ ℚ_2`), `φ₀` is the corestriction of `φ`, and the
compatibility `(φ₀ x : ℚ̄_₂) = φ x` is definitional. Only the confined
member retains automorphy content. -/
theorem exists_realization_at_two_of_embedding_core
    [Algebra R (AlgebraicClosure ℚ_[p])]
    [ContinuousSMul R (AlgebraicClosure ℚ_[p])]
    (hZinj : Function.Injective (algebraMap ℤ_[p] R))
    (hRinj : Function.Injective (algebraMap R (AlgebraicClosure ℚ_[p])))
    (hρ : IsHardlyRamified hpodd hv ρ)
    {E : Type v} [Field E] [NumberField E] (ψ : E →+* AlgebraicClosure ℚ_[p])
    (S : Finset (HeightOneSpectrum (NumberField.RingOfIntegers ℚ)))
    (Pv : HeightOneSpectrum (NumberField.RingOfIntegers ℚ) → Polynomial E)
    (heig : ∀ v ∉ S,
      (ρ.charFrob v).map (algebraMap R (AlgebraicClosure ℚ_[p])) = (Pv v).map ψ)
    (φ : E →+* AlgebraicClosure ℚ_[2]) :
    ∃ (T : Finset (HeightOneSpectrum (NumberField.RingOfIntegers ℚ)))
      (K : IntermediateField ℚ_[2] (AlgebraicClosure ℚ_[2]))
      (_ : FiniteDimensional ℚ_[2] K)
      (φ₀ : E →+* K)
      (τ : GaloisRep ℚ K (Fin 2 → K)),
        (∀ x : E, (φ₀ x : AlgebraicClosure ℚ_[2]) = φ x) ∧
        ∀ v ∉ T, τ.IsUnramifiedAt v ∧ τ.charFrob v = (Pv v).map φ₀ := by
  classical
  -- a finite `ℚ`-spanning set of the number field `E`
  obtain ⟨s, hs⟩ : (⊤ : Submodule ℚ E).FG := Module.finite_def.mp inferInstance
  -- ring homs out of `ℚ` are unique, so `φ` restricts to the canonical map
  have hQcomp : (algebraMap ℚ_[2] (AlgebraicClosure ℚ_[2])).comp (algebraMap ℚ ℚ_[2]) =
      φ.comp (algebraMap ℚ E) := Subsingleton.elim _ _
  -- the `φ`-image of `E` is integral over `ℚ_2`
  have hint : ∀ x : E, IsIntegral ℚ_[2] (φ x) := by
    intro x
    obtain ⟨P, hPmonic, hPeval⟩ := IsIntegral.of_finite ℚ x
    refine ⟨P.map (algebraMap ℚ ℚ_[2]), hPmonic.map _, ?_⟩
    rw [Polynomial.eval₂_map, hQcomp, ← Polynomial.hom_eval₂, hPeval, map_zero]
  -- finite-dimensionality: finitely many integral generators
  have hKfin : FiniteDimensional ℚ_[2]
      (IntermediateField.adjoin ℚ_[2] (⇑φ '' ↑s)) := by
    haveI : Finite ↥(⇑φ '' ↑s) := (s.finite_toSet.image _).to_subtype
    exact IntermediateField.finiteDimensional_adjoin fun x hx => by
      obtain ⟨y, -, rfl⟩ := hx
      exact hint y
  -- the whole image of `E` lies in the adjoined field
  have hmem : ∀ x : E, φ x ∈ IntermediateField.adjoin ℚ_[2] (⇑φ '' ↑s) := by
    intro x
    have hx : x ∈ Submodule.span ℚ (↑s : Set E) := by rw [hs]; exact Submodule.mem_top
    induction hx using Submodule.span_induction with
    | mem y hy => exact IntermediateField.subset_adjoin _ _ ⟨y, hy, rfl⟩
    | zero => rw [map_zero]; exact zero_mem _
    | add y z _ _ hy hz => rw [map_add]; exact add_mem hy hz
    | smul c y _ hy =>
      rw [Algebra.smul_def, map_mul]
      refine mul_mem ?_ hy
      have hc := RingHom.congr_fun hQcomp c
      rw [RingHom.comp_apply, RingHom.comp_apply] at hc
      rw [← hc]
      exact IntermediateField.algebraMap_mem _ _
  haveI := hKfin
  obtain ⟨T, τ, hT⟩ := exists_realization_at_two_confined hpodd hv hZinj hRinj hρ ψ S Pv
    heig (IntermediateField.adjoin ℚ_[2] (⇑φ '' ↑s)) (φ.codRestrict _ hmem)
  exact ⟨T, IntermediateField.adjoin ℚ_[2] (⇑φ '' ↑s), hKfin, φ.codRestrict _ hmem, τ,
    fun x => rfl, hT⟩

/-- **Per-embedding member at residue characteristic 2** (PROVEN
assembly, see the DECOMPOSED note below): the eigensystem `(E, S, Pv)`
is realized at the even prime at a SINGLE
given embedding `φ : E →+* ℚ̄_₂` — there is a 2-dimensional `2`-adic
representation, unramified away from a finite exceptional set `T`
(allowed to depend on `φ`) and the places over `2`, whose Frobenius
characteristic polynomials there are `(Pv v).map φ`. This is
Eichler–Shimura/Deligne at `λ | 2` plus local–global compatibility for
the one member; no hardly-ramifiedness demand is made (the notion
requires odd residue characteristic). Strictly shallower than the
φ-uniform `exists_realizations_at_two` below: the uniformity of the
exceptional set over the (finitely many!) embeddings of the number
field `E` into `ℚ̄_₂` is PROVEN glue there, not automorphy content.

DECOMPOSED (2026-07-23) into a PROVEN assembly over one strictly
shallower sorried leaf: `exists_realization_at_two_of_embedding_core`
realizes the member over a finite-dimensional subfield `K ⊆ ℚ̄_₂`
through which `φ` factors — the coefficient-field shape
Eichler–Shimura/Deligne actually outputs. The assembly (below) spreads
it to `ℚ̄_₂` by framed base change along `K ↪ ℚ̄_₂`: the framing is
`Basis.baseChange` of the standard basis followed by `Basis.equivFun`,
the coefficient scalar action is continuous by the
`IntermediateField.continuousSMul` instance, unramifiedness transports
through the `baseChange` instance of `GaloisRep.IsUnramifiedAt` plus
`isUnramifiedAt_conj`, the charpoly matching through
`charFrob_baseChange_conj` and `Polynomial.map_map` (the factoring of
`φ` through `K` recombines the two coefficient maps), and the
`2 ∤ v` proviso is dropped in the core — its `T` already absorbs the
single place of `ℚ` above `2`. Only the confined realization retains
automorphy content. -/
theorem exists_realization_at_two_of_embedding
    [Algebra R (AlgebraicClosure ℚ_[p])]
    [ContinuousSMul R (AlgebraicClosure ℚ_[p])]
    (hZinj : Function.Injective (algebraMap ℤ_[p] R))
    (hRinj : Function.Injective (algebraMap R (AlgebraicClosure ℚ_[p])))
    (hρ : IsHardlyRamified hpodd hv ρ)
    {E : Type v} [Field E] [NumberField E] (ψ : E →+* AlgebraicClosure ℚ_[p])
    (S : Finset (HeightOneSpectrum (NumberField.RingOfIntegers ℚ)))
    (Pv : HeightOneSpectrum (NumberField.RingOfIntegers ℚ) → Polynomial E)
    (heig : ∀ v ∉ S,
      (ρ.charFrob v).map (algebraMap R (AlgebraicClosure ℚ_[p])) = (Pv v).map ψ)
    (φ : E →+* AlgebraicClosure ℚ_[2]) :
    ∃ (T : Finset (HeightOneSpectrum (NumberField.RingOfIntegers ℚ)))
      (m : GaloisRep ℚ (AlgebraicClosure ℚ_[2]) (Fin 2 → AlgebraicClosure ℚ_[2])),
        ∀ v ∉ T, ((2 : ℕ) : NumberField.RingOfIntegers ℚ) ∉ v.asIdeal →
          m.IsUnramifiedAt v ∧
          (m.toLocal v (Field.AbsoluteGaloisGroup.adicArithFrob v)).charpoly =
            (Pv v).map φ := by
  obtain ⟨T, K, hKfin, φ₀, τ, hφ₀, hT⟩ :=
    exists_realization_at_two_of_embedding_core hpodd hv hZinj hRinj hρ ψ S Pv heig φ
  -- the framing of the base extension along `K ↪ ℚ̄_₂`
  let r : AlgebraicClosure ℚ_[2] ⊗[K] (Fin 2 → K) ≃ₗ[AlgebraicClosure ℚ_[2]]
      (Fin 2 → AlgebraicClosure ℚ_[2]) :=
    ((Pi.basisFun K (Fin 2)).baseChange (AlgebraicClosure ℚ_[2])).equivFun
  -- `φ` factors through `K` as ring homomorphisms
  have hcomp : (algebraMap K (AlgebraicClosure ℚ_[2])).comp φ₀ = φ :=
    RingHom.ext fun x => hφ₀ x
  refine ⟨T, (τ.baseChange (AlgebraicClosure ℚ_[2])).conj r, ?_⟩
  intro v hvT _hv2
  obtain ⟨hunr, hchar⟩ := hT v hvT
  refine ⟨isUnramifiedAt_conj (τ.baseChange (AlgebraicClosure ℚ_[2])) r v, ?_⟩
  calc (((τ.baseChange (AlgebraicClosure ℚ_[2])).conj r).toLocal v
        (Field.AbsoluteGaloisGroup.adicArithFrob v)).charpoly
      = ((τ.baseChange (AlgebraicClosure ℚ_[2])).conj r).charFrob v := rfl
    _ = (τ.charFrob v).map (algebraMap K (AlgebraicClosure ℚ_[2])) :=
        charFrob_baseChange_conj τ r v
    _ = ((Pv v).map φ₀).map (algebraMap K (AlgebraicClosure ℚ_[2])) := by rw [hchar]
    _ = (Pv v).map φ := by rw [Polynomial.map_map, hcomp]

/-- **Residue characteristic 2 member of the realization stratum**
(PROVEN assembly, see the DECOMPOSED note below): the eigensystem
`(E, S, Pv)` is realized at the even
prime as well — for each embedding `φ : E →+* ℚ̄_₂` there is a
2-dimensional `2`-adic representation, unramified away from a finite
exceptional set `T` (uniform in `φ`) and the places over `2`, whose
Frobenius characteristic polynomials there are `(Pv v).map φ`. This is
Eichler–Shimura/Deligne at `λ | 2` plus local–global compatibility;
no hardly-ramifiedness demand is made (the notion requires odd residue
characteristic), so this is the bare member existence — the reason it
is a separate leaf from
`exists_hardlyRamified_integral_realizations`, whose conclusion
packages the member together with its hardly ramified integral
model.

DECOMPOSED (2026-07-23) into a PROVEN assembly over one strictly
shallower leaf: `exists_realization_at_two_of_embedding` (itself as of
2026-07-23 a PROVEN assembly over the confined sorried core
`exists_realization_at_two_of_embedding_core`)
realizes the eigensystem at each single embedding `φ` with a
`φ`-dependent exceptional set `T φ`; the assembly (below) removes the
`φ`-dependence by taking the union of the `T φ` over ALL embeddings —
a finite union, because a number field has only finitely many ring
homomorphisms into any field (every `φ : E →+* ℚ̄_₂` is a `ℚ`-algebra
map by `RingHom.equivRatAlgHom`, and `Finite (E →ₐ[ℚ] ℚ̄_₂)` holds by
`Finite.algHom` since `E` is finite-dimensional over `ℚ`). The
uniformity demanded by `GaloisRepFamily.isCompatible` downstream is
thus proven bookkeeping; only the per-embedding realization retains
automorphy content. -/
theorem exists_realizations_at_two
    [Algebra R (AlgebraicClosure ℚ_[p])]
    [ContinuousSMul R (AlgebraicClosure ℚ_[p])]
    (hZinj : Function.Injective (algebraMap ℤ_[p] R))
    (hRinj : Function.Injective (algebraMap R (AlgebraicClosure ℚ_[p])))
    (hρ : IsHardlyRamified hpodd hv ρ)
    {E : Type v} [Field E] [NumberField E] (ψ : E →+* AlgebraicClosure ℚ_[p])
    (S : Finset (HeightOneSpectrum (NumberField.RingOfIntegers ℚ)))
    (Pv : HeightOneSpectrum (NumberField.RingOfIntegers ℚ) → Polynomial E)
    (heig : ∀ v ∉ S,
      (ρ.charFrob v).map (algebraMap R (AlgebraicClosure ℚ_[p])) = (Pv v).map ψ) :
    ∃ (T : Finset (HeightOneSpectrum (NumberField.RingOfIntegers ℚ))),
      ∀ (φ : E →+* AlgebraicClosure ℚ_[2]),
      ∃ (m : GaloisRep ℚ (AlgebraicClosure ℚ_[2]) (Fin 2 → AlgebraicClosure ℚ_[2])),
        ∀ v ∉ T, ((2 : ℕ) : NumberField.RingOfIntegers ℚ) ∉ v.asIdeal →
          m.IsUnramifiedAt v ∧
          (m.toLocal v (Field.AbsoluteGaloisGroup.adicArithFrob v)).charpoly =
            (Pv v).map φ := by
  classical
  -- the number field `E` has only finitely many embeddings into `ℚ̄_₂`
  haveI : Finite (E →+* AlgebraicClosure ℚ_[2]) :=
    Finite.of_equiv (E →ₐ[ℚ] AlgebraicClosure ℚ_[2]) RingHom.equivRatAlgHom.symm
  haveI := Fintype.ofFinite (E →+* AlgebraicClosure ℚ_[2])
  -- realize the eigensystem at each embedding separately
  choose T m hm using fun φ : E →+* AlgebraicClosure ℚ_[2] =>
    exists_realization_at_two_of_embedding hpodd hv hZinj hRinj hρ ψ S Pv heig φ
  -- the uniform exceptional set is the finite union of the per-embedding ones
  refine ⟨Finset.univ.biUnion T, fun φ => ⟨m φ, fun v hvT hv2 =>
    hm φ v (fun h => hvT (Finset.mem_biUnion.mpr ⟨φ, Finset.mem_univ _, h⟩)) hv2⟩⟩

/-- **Realization stratum of the spreading** (PROVEN assembly, see the
DECOMPOSED note below): the
eigensystem `(E, S, Pv)` attached to a hardly ramified `p`-adic
representation is realized at every finite place of every residue
characteristic: for each prime `ℓ` and each embedding `φ : E →+* ℚ̄_ℓ`
there is a 2-dimensional `ℓ`-adic representation, unramified at the
places outside a single finite exceptional set `T` (uniform in
`(ℓ, φ)`) not dividing `ℓ`, whose Frobenius characteristic polynomials
there are `(Pv v).map φ` — the *same* `Pv` for all `(ℓ, φ)`: the
cross-`ℓ` charpoly agreement of the family is carried entirely by this
sharing — and which for odd `ℓ` is the framed base extension of a
hardly ramified representation over a module-finite local
`ℤ_ℓ`-algebra.

This is Eichler–Shimura/Deligne (the `λ`-adic representations attached
to the weight-2 eigenform underlying the eigensystem), plus
local–global compatibility (Carayol, Saito) for the unramifiedness and
the charpoly matching, plus the weight-2 level-2 analysis showing the
odd-residue-characteristic members are hardly ramified. The anchoring
of the family AT `(p, ψ)` to `ρ` itself is deliberately NOT part of
this leaf — recovering `ρ` from its charpolys alone is the
Brauer–Nesbitt-unsound direction (see the DECOMPOSITION AUDIT on
`exists_family_of_eigensystem`); the assembly there instead places
`ρ ⊗ ℚ̄_p` at `(p, ψ)` by hand and uses this leaf everywhere else.

DECOMPOSED (2026-07-23) into a PROVEN assembly over two sorried
leaves, split along residue characteristic:

1. `exists_hardlyRamified_integral_realizations` (as of 2026-07-23 a
   PROVEN assembly over the minimal-telescope sorried leaf
   `exists_hardlyRamified_integral_realizations_core`) — at odd
   `ℓ`, the hardly ramified integral model `τ` over `A ↪ ℚ̄_ℓ` with
   the unramifiedness and charpoly matching stated at the integral
   level (with exceptional set `T₁`). The sole automorphy content at
   odd `ℓ`; see the core leaf's docstring for the vocabulary
   obstruction to a further newform-datum split and the Brauer–Nesbitt
   soundness constraint forcing the model to be produced there.
2. `exists_realizations_at_two` (as of 2026-07-23 a PROVEN assembly
   over the per-embedding leaf
   `exists_realization_at_two_of_embedding`, itself a PROVEN assembly
   over the confined sorried core
   `exists_realization_at_two_of_embedding_core`) — the bare member at
   `ℓ = 2` (with exceptional set `T₂`), where no integral-model demand
   is made.
3. The assembly (PROVEN, below) takes `T := T₁ ∪ T₂` and derives the
   odd-`ℓ` member as `(τ.baseChange ℚ̄_ℓ).conj r` — its
   unramifiedness by the `baseChange` instance of
   `GaloisRep.IsUnramifiedAt` plus `isUnramifiedAt_conj`, its
   charpoly matching by `charFrob_baseChange_conj`, and its
   integral-model clause by `rfl` — i.e. the Deligne-direction
   "datum ⇒ member" arrow is proven glue; at `ℓ = 2` (the only
   non-odd prime) it uses leaf 2's member, the integral-model clause
   holding vacuously. -/
theorem exists_realizations_of_eigensystem
    [Algebra R (AlgebraicClosure ℚ_[p])]
    [ContinuousSMul R (AlgebraicClosure ℚ_[p])]
    (hZinj : Function.Injective (algebraMap ℤ_[p] R))
    (hRinj : Function.Injective (algebraMap R (AlgebraicClosure ℚ_[p])))
    (hρ : IsHardlyRamified hpodd hv ρ)
    {E : Type v} [Field E] [NumberField E] (ψ : E →+* AlgebraicClosure ℚ_[p])
    (S : Finset (HeightOneSpectrum (NumberField.RingOfIntegers ℚ)))
    (Pv : HeightOneSpectrum (NumberField.RingOfIntegers ℚ) → Polynomial E)
    (heig : ∀ v ∉ S,
      (ρ.charFrob v).map (algebraMap R (AlgebraicClosure ℚ_[p])) = (Pv v).map ψ) :
    ∃ (T : Finset (HeightOneSpectrum (NumberField.RingOfIntegers ℚ))),
      ∀ (ℓ : ℕ) (_hℓ : Fact ℓ.Prime) (φ : E →+* AlgebraicClosure ℚ_[ℓ]),
      ∃ (m : GaloisRep ℚ (AlgebraicClosure ℚ_[ℓ]) (Fin 2 → AlgebraicClosure ℚ_[ℓ])),
        (∀ v ∉ T, (ℓ : NumberField.RingOfIntegers ℚ) ∉ v.asIdeal →
          m.IsUnramifiedAt v ∧
          (m.toLocal v (Field.AbsoluteGaloisGroup.adicArithFrob v)).charpoly =
            (Pv v).map φ) ∧
        ∀ (hℓodd : Odd ℓ),
          ∃ (A : Type u) (_ : CommRing A) (_ : TopologicalSpace A)
            (_ : IsTopologicalRing A) (_ : IsLocalRing A) (_ : Algebra ℤ_[ℓ] A)
            (_ : Module.Finite ℤ_[ℓ] A) (_ : Module.Free ℤ_[ℓ] A) (_ : IsDomain A)
            (_ : Algebra A (AlgebraicClosure ℚ_[ℓ]))
            (_ : IsScalarTower ℤ_[ℓ] A (AlgebraicClosure ℚ_[ℓ]))
            (_ : IsModuleTopology ℤ_[ℓ] A)
            (_ : ContinuousSMul A (AlgebraicClosure ℚ_[ℓ]))
            (_ : Function.Injective (algebraMap A (AlgebraicClosure ℚ_[ℓ])))
            (W : Type v) (_ : AddCommGroup W) (_ : Module A W) (_ : Module.Finite A W)
            (_ : Module.Free A W) (hW : Module.rank A W = 2)
            (τ : GaloisRep ℚ A W)
            (r : AlgebraicClosure ℚ_[ℓ] ⊗[A] W ≃ₗ[AlgebraicClosure ℚ_[ℓ]]
              Fin 2 → AlgebraicClosure ℚ_[ℓ]),
            IsHardlyRamified hℓodd hW τ ∧
            (τ.baseChange (AlgebraicClosure ℚ_[ℓ])).conj r = m := by
  classical
  obtain ⟨T₁, hT₁⟩ :=
    exists_hardlyRamified_integral_realizations hpodd hv hZinj hRinj hρ ψ S Pv heig
  obtain ⟨T₂, hT₂⟩ :=
    exists_realizations_at_two hpodd hv hZinj hRinj hρ ψ S Pv heig
  refine ⟨T₁ ∪ T₂, ?_⟩
  intro ℓ hℓ φ
  by_cases hℓodd : Odd ℓ
  · -- odd `ℓ`: the member is the framed base extension of the integral model
    obtain ⟨A, iA1, iA2, iA3, iA4, iA5, iA6, iA7, iA8, iA9, iA10, iA11, iA12,
      hAinj, W, iW1, iW2, iW3, iW4, hW, τ, r, hτ, hmatch⟩ := hT₁ ℓ hℓ hℓodd φ
    refine ⟨(τ.baseChange (AlgebraicClosure ℚ_[ℓ])).conj r, ?_, ?_⟩
    · intro v hvT hvℓ
      obtain ⟨hunr, hchar⟩ :=
        hmatch v (fun h => hvT (Finset.mem_union_left _ h)) hvℓ
      refine ⟨isUnramifiedAt_conj (τ.baseChange (AlgebraicClosure ℚ_[ℓ])) r v, ?_⟩
      calc (((τ.baseChange (AlgebraicClosure ℚ_[ℓ])).conj r).toLocal v
            (Field.AbsoluteGaloisGroup.adicArithFrob v)).charpoly
          = ((τ.baseChange (AlgebraicClosure ℚ_[ℓ])).conj r).charFrob v := rfl
        _ = (τ.charFrob v).map (algebraMap A (AlgebraicClosure ℚ_[ℓ])) :=
            charFrob_baseChange_conj τ r v
        _ = (Pv v).map φ := hchar
    · intro hℓodd'
      refine ⟨A, iA1, iA2, iA3, iA4, iA5, iA6, iA7, iA8, iA9, iA10, iA11, iA12,
        hAinj, W, iW1, iW2, iW3, iW4, hW, τ, r, hτ, ?_⟩
      rfl
  · -- `ℓ = 2`: the bare member from the even-prime leaf
    have hℓ2 : ℓ = 2 := (hℓ.out.eq_two_or_odd').resolve_right hℓodd
    subst hℓ2
    obtain ⟨m, hm⟩ := hT₂ φ
    refine ⟨m, ?_, fun hℓodd' => absurd hℓodd' (by decide)⟩
    intro v hvT hvℓ
    exact hm v (fun h => hvT (Finset.mem_union_right _ h)) hvℓ

/-- **Spreading stratum** (PROVEN assembly, see the DECOMPOSED note
below): a hardly ramified `p`-adic
representation whose Frobenius characteristic polynomials descend to a
number field `E` spreads out into a compatible family of Galois
representations with hardly ramified odd-residue-characteristic members,
containing `ρ` as its member at some embedding of (a possibly larger)
number field into `ℚ̄_p`.

This is the construction of the compatible family attached to the
eigensystem — Eichler–Shimura/Deligne's construction of the `λ`-adic
representations attached to the eigenform underlying the eigensystem,
plus local-global compatibility (Carayol, Saito) and the weight-2,
level-2 analysis showing each odd-residue member is hardly ramified.
The eigensystem hypothesis `heig` is the data the construction consumes;
the conclusion is stated verbatim as the automorphy core of
`mem_isCompatible` below.

DECOMPOSITION AUDIT (2026-07-22, recording a rejected alternative): the
seemingly natural split "(i) `ρ` lies in *some* compatible family; (ii)
any compatible family with one hardly ramified member has hardly
ramified odd members" is UNSOUND at (ii): `GaloisRepFamily.isCompatible`
pins only charpoly data outside a finite set, so a compatible family
containing the hardly ramified member `1 ⊕ χ_p` can place at another
prime a *non-semisimple* extension of `1` by `χ_ℓ` ramified at an
auxiliary prime (a Kummer class of `5`, say) — same Frobenius
charpolys, but ramified outside `{2, ℓ}`, hence not isomorphic to any
hardly ramified representation. The eigensystem/spreading split used
here avoids quantifying over abstract families in the hypotheses.

AUDIT RESTATEMENT #2 (2026-07-23, coordinated with the sole call site
`mem_isCompatible`, following the precedent of the `hZinj` restatement
in the module docstring): the hypothesis
`[IsScalarTower ℤ_[p] R ℚ̄_p]` is ADDED. Without it the conclusion
resists proof at the anchor: the membership clause pins `σ (p, ψ)` to
the base change of `ρ` along the AMBIENT `Algebra R ℚ̄_p`, and the
hardly-ramified clause at `(p, ψ)` then demands an integral model over
a coefficient ring `A` whose embedding `A → ℚ̄_p` IS
`IsScalarTower`-compatible and whose framed base change EQUALS that
member — for a rogue (non-tower) ambient algebra the natural witness
`A := R` is unavailable, and conjugation cannot repair a coefficient
embedding. At the call site the instance is discharged from the
compatibility component of `hembed` (previously discarded).

DECOMPOSED (2026-07-23) into a PROVEN assembly over one sorried leaf:
`exists_realizations_of_eigensystem` provides members at all `(ℓ, φ)`
matching the shared `Pv` (with hardly ramified integral models at odd
`ℓ`); the assembly defines `σ` as those members overridden at `(p, ψ)`
by `ρ ⊗ ℚ̄_p` — whose compatibility clauses come from `heig` via
`charFrob_baseChange_conj` and from `isUnramifiedAt_of_ne`, and whose
hardly ramified integral model is `ρ` over `R` itself (`hZinj` gives
`Module.Free ℤ_[p] R` over the PID `ℤ_[p]`; the tower hypothesis gives
the coefficient compatibility) — and takes the exceptional set
`{place over 2} ∪ S ∪ T`. -/
theorem exists_family_of_eigensystem
    [Algebra R (AlgebraicClosure ℚ_[p])]
    [ContinuousSMul R (AlgebraicClosure ℚ_[p])]
    [IsScalarTower ℤ_[p] R (AlgebraicClosure ℚ_[p])]
    (hZinj : Function.Injective (algebraMap ℤ_[p] R))
    (hRinj : Function.Injective (algebraMap R (AlgebraicClosure ℚ_[p])))
    (hρ : IsHardlyRamified hpodd hv ρ)
    (heig : ∃ (E : Type v) (_ : Field E) (_ : NumberField E)
      (ψ : E →+* AlgebraicClosure ℚ_[p])
      (S : Finset (HeightOneSpectrum (NumberField.RingOfIntegers ℚ)))
      (Pv : HeightOneSpectrum (NumberField.RingOfIntegers ℚ) → Polynomial E),
      ∀ v : HeightOneSpectrum (NumberField.RingOfIntegers ℚ), v ∉ S →
        (ρ.charFrob v).map (algebraMap R (AlgebraicClosure ℚ_[p])) =
          (Pv v).map ψ) :
    ∃ (E : Type v) (_ : Field E) (_ : NumberField E) (σ : GaloisRepFamily ℚ E 2),
      σ.isCompatible ∧
      (∀ {ℓ : ℕ} (hℓ : Fact ℓ.Prime) (hℓodd : Odd ℓ) (φ : E →+* AlgebraicClosure ℚ_[ℓ]),
        ∃ (A : Type u) (_ : CommRing A) (_ : TopologicalSpace A) (_ : IsTopologicalRing A)
          (_ : IsLocalRing A) (_ : Algebra ℤ_[ℓ] A) (_ : Module.Finite ℤ_[ℓ] A)
          (_ : Module.Free ℤ_[ℓ] A) (_ : IsDomain A) (_ : Algebra A (AlgebraicClosure ℚ_[ℓ]))
          (_ : IsScalarTower ℤ_[ℓ] A (AlgebraicClosure ℚ_[ℓ])) (_ : IsModuleTopology ℤ_[ℓ] A)
          (_ : ContinuousSMul A (AlgebraicClosure ℚ_[ℓ]))
          (_ : Function.Injective (algebraMap A (AlgebraicClosure ℚ_[ℓ])))
          (W : Type v) (_ : AddCommGroup W) (_ : Module A W) (_ : Module.Finite A W)
          (_ : Module.Free A W) (hW : Module.rank A W = 2)
          (τ : GaloisRep ℚ A W)
          (r : AlgebraicClosure ℚ_[ℓ] ⊗[A] W ≃ₗ[AlgebraicClosure ℚ_[ℓ]]
            Fin 2 → AlgebraicClosure ℚ_[ℓ]),
          IsHardlyRamified hℓodd hW τ ∧
          (τ.baseChange (AlgebraicClosure ℚ_[ℓ])).conj r = σ hℓ φ) ∧
      (∃ (ψ : E →+* AlgebraicClosure ℚ_[p])
        (r' : AlgebraicClosure ℚ_[p] ⊗[R] V ≃ₗ[AlgebraicClosure ℚ_[p]]
          Fin 2 → AlgebraicClosure ℚ_[p]),
        (ρ.baseChange (AlgebraicClosure ℚ_[p])).conj r' = σ hp ψ) := by
  classical
  obtain ⟨E, iE, iNE, ψ, S, Pv, heigS⟩ := heig
  obtain ⟨T, hreal⟩ :=
    exists_realizations_of_eigensystem hpodd hv hZinj hRinj hρ ψ S Pv heigS
  choose m hm using hreal
  -- the anchor: `ρ ⊗ ℚ̄_p`, framed by a basis of `V`
  haveI : Module.IsTorsionFree ℤ_[p] R :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr hZinj
  haveI hRfree : Module.Free ℤ_[p] R := Module.free_of_finite_type_torsion_free'
  have hfinrank : Module.finrank R V = 2 := Module.finrank_eq_of_rank_eq hv
  let r' : AlgebraicClosure ℚ_[p] ⊗[R] V ≃ₗ[AlgebraicClosure ℚ_[p]]
      (Fin 2 → AlgebraicClosure ℚ_[p]) :=
    ((Module.finBasisOfFinrankEq R V hfinrank).baseChange
      (AlgebraicClosure ℚ_[p])).equivFun
  let anchorRep : GaloisRep ℚ (AlgebraicClosure ℚ_[p])
      (Fin 2 → AlgebraicClosure ℚ_[p]) :=
    (ρ.baseChange (AlgebraicClosure ℚ_[p])).conj r'
  -- the family: the realization members, overridden at `(p, ψ)`
  let σ : GaloisRepFamily ℚ E 2 := fun {ℓ} hℓ φ =>
    if h : ℓ = p then
      (by subst h
          exact if φ = ψ then anchorRep else m ℓ hℓ φ)
    else m ℓ hℓ φ
  -- evaluation of `σ` at the anchor and away from it
  have hσ_anchor : ∀ (hfp : Fact p.Prime), σ hfp ψ = anchorRep := by
    intro hfp
    show dite (p = p) _ _ = _
    rw [dif_pos rfl]
    show (if ψ = ψ then anchorRep else m p hfp ψ) = anchorRep
    rw [if_pos rfl]
  have hσ_p_ne : ∀ (hfp : Fact p.Prime) (φ : E →+* AlgebraicClosure ℚ_[p]),
      φ ≠ ψ → σ hfp φ = m p hfp φ := by
    intro hfp φ hφ
    show dite (p = p) _ _ = _
    rw [dif_pos rfl]
    show (if φ = ψ then anchorRep else m p hfp φ) = m p hfp φ
    rw [if_neg hφ]
  have hσ_ne : ∀ (ℓ : ℕ) (hℓ : Fact ℓ.Prime) (φ : E →+* AlgebraicClosure ℚ_[ℓ]),
      ℓ ≠ p → σ hℓ φ = m ℓ hℓ φ := by
    intro ℓ hℓ φ hℓp
    show dite (ℓ = p) _ _ = _
    rw [dif_neg hℓp]
  refine ⟨E, iE, iNE, σ, ⟨insert Nat.prime_two.toHeightOneSpectrumRingOfIntegersRat
    (S ∪ T), Pv, ?_⟩, ?_, ψ, r', (hσ_anchor hp).symm⟩
  · -- compatibility of the family
    intro ℓ hfp φ v hvS hvℓ
    have hvS' : v ∉ S := fun h =>
      hvS (Finset.mem_insert_of_mem (Finset.mem_union_left _ h))
    have hvT : v ∉ T := fun h =>
      hvS (Finset.mem_insert_of_mem (Finset.mem_union_right _ h))
    have hv2 : v ≠ Nat.prime_two.toHeightOneSpectrumRingOfIntegersRat := fun h =>
      hvS (h ▸ Finset.mem_insert_self _ _)
    by_cases hℓp : ℓ = p
    · subst hℓp
      -- (the ambient prime is now named `ℓ`)
      show (σ hfp φ).IsUnramifiedAt v ∧
        ((σ hfp φ).toLocal v
          (Field.AbsoluteGaloisGroup.adicArithFrob v)).charpoly = (Pv v).map φ
      by_cases hφ : φ = ψ
      · rw [hφ, hσ_anchor hfp]
        constructor
        · -- unramifiedness of the anchor
          haveI : ρ.IsUnramifiedAt v := isUnramifiedAt_of_ne hpodd hv hρ v hv2 hvℓ
          exact isUnramifiedAt_conj (ρ.baseChange (AlgebraicClosure ℚ_[ℓ])) r' v
        · -- charpoly of the anchor: the bridge plus the eigensystem
          calc ((anchorRep.toLocal v
                (Field.AbsoluteGaloisGroup.adicArithFrob v)).charpoly)
              = anchorRep.charFrob v := rfl
            _ = (ρ.charFrob v).map (algebraMap R (AlgebraicClosure ℚ_[ℓ])) :=
                charFrob_baseChange_conj ρ r' v
            _ = (Pv v).map ψ := heigS v hvS'
      · rw [hσ_p_ne hfp φ hφ]
        exact (hm ℓ hfp φ).1 v hvT hvℓ
    · show (σ hfp φ).IsUnramifiedAt v ∧
        ((σ hfp φ).toLocal v
          (Field.AbsoluteGaloisGroup.adicArithFrob v)).charpoly = (Pv v).map φ
      rw [hσ_ne ℓ hfp φ hℓp]
      exact (hm ℓ hfp φ).1 v hvT hvℓ
  · -- the odd-residue members are hardly ramified
    intro ℓ hℓ hℓodd φ
    by_cases hℓp : ℓ = p
    · subst hℓp
      -- (the ambient prime is now named `ℓ`)
      by_cases hφ : φ = ψ
      · refine ⟨R, inferInstance, inferInstance, inferInstance, inferInstance,
          inferInstance, inferInstance, hRfree, inferInstance, inferInstance,
          inferInstance, inferInstance, inferInstance, hRinj, V, inferInstance,
          inferInstance, inferInstance, inferInstance, hv, ρ, r', ?_, ?_⟩
        · exact hρ
        · show (ρ.baseChange (AlgebraicClosure ℚ_[ℓ])).conj r' = σ hℓ φ
          rw [hφ]
          exact (hσ_anchor hℓ).symm
      · obtain ⟨A, iA1, iA2, iA3, iA4, iA5, iA6, iA7, iA8, iA9, iA10, iA11, iA12,
          hAinj, W, iW1, iW2, iW3, iW4, hW, τ, r, hτ, hτeq⟩ := (hm ℓ hℓ φ).2 hℓodd
        refine ⟨A, iA1, iA2, iA3, iA4, iA5, iA6, iA7, iA8, iA9, iA10, iA11, iA12,
          hAinj, W, iW1, iW2, iW3, iW4, hW, τ, r, hτ, ?_⟩
        show (τ.baseChange (AlgebraicClosure ℚ_[ℓ])).conj r = σ hℓ φ
        rw [hσ_p_ne hℓ φ hφ]
        exact hτeq
    · obtain ⟨A, iA1, iA2, iA3, iA4, iA5, iA6, iA7, iA8, iA9, iA10, iA11, iA12,
        hAinj, W, iW1, iW2, iW3, iW4, hW, τ, r, hτ, hτeq⟩ := (hm ℓ hℓ φ).2 hℓodd
      refine ⟨A, iA1, iA2, iA3, iA4, iA5, iA6, iA7, iA8, iA9, iA10, iA11, iA12,
        hAinj, W, iW1, iW2, iW3, iW4, hW, τ, r, hτ, ?_⟩
      show (τ.baseChange (AlgebraicClosure ℚ_[ℓ])).conj r = σ hℓ φ
      rw [hσ_ne ℓ hℓ φ hℓp]
      exact hτeq

/-- **B6b**: a hardly ramified `p`-adic representation over a
coefficient ring of characteristic zero (`hZinj`: `ℤ_[p]` embeds — the
audit hypothesis added 2026-07-22, without which the statement is false;
see the module docstring) lives in a compatible family of Galois
representations, all of whose odd-residue-characteristic members are
themselves hardly ramified.

DECOMPOSED (2026-07-22) into a compiling skeleton with one sorried step
(a second sorried step, the false-as-stated injectivity of
`algebraMap ℤ_[p] R`, was the quarantine of the audit defect and is
superseded by the hypothesis `hZinj`):

1. `hembed` — from `hZinj`, the coefficient embedding `R ↪ ℚ̄_p`
   (injective, `ℤ_[p]`-compatible, continuous) is PROVEN.
2. the automorphy core — given the fixed continuous embedding
   `R ↪ ℚ̄_p` (as the `Algebra R ℚ̄_p` instance `ia` in context), the
   hardly ramified `ρ` extends to a compatible family `σ` over a number
   field `E` with hardly ramified odd members, and `ρ ⊗ ℚ̄_p` is the
   member at some `ψ : E →+* ℚ̄_p`. FURTHER DECOMPOSED (2026-07-22)
   into the two strata above: the eigensystem stratum
   (`exists_numberField_eigensystem` — the Frobenius data descend to a
   number field, i.e. the Hecke-field/eigenform-congruence content) and
   the spreading stratum (`exists_family_of_eigensystem` — the
   compatible family attached to the eigensystem, i.e.
   Eichler–Shimura/Deligne plus local-global compatibility). AS OF
   2026-07-23 both strata are PROVEN assemblies, and the Hecke-field
   node `exists_finiteDimensional_coeff_field` is itself a PROVEN
   assembly (see its DECOMPOSED note); the surviving sorried leaves
   (2026-07-23, after the further decompositions recorded at each
   node) are `exists_rat_trace_coeff_of_not_isIrreducible`,
   `exists_isAlgebraic_trace_coeff_of_isIrreducible` and
   `exists_linearIndependent_trace_card_le_of_isIrreducible` (the
   reducible/irreducible dichotomy under the two shadows of the
   Hecke-field finiteness core for the TRACE coefficient),
   `exists_hardlyRamified_integral_realizations_core` (the `λ`-adic
   realizations at odd `ℓ`, minimal telescope) and
   `exists_realization_at_two_of_embedding_core` (the per-embedding
   member at `ℓ = 2`, confined to a finite-dimensional subfield of
   `ℚ̄_₂`).

NOTE (elaboration): the final repackaging must be `refine` +
a deferred `exact` — an anonymous-constructor `exact ⟨…, ψ, r', hψ⟩`
against the `∃ (_ : Algebra R ℚ̄_p) …` telescope sends `isDefEq` into
a heartbeat timeout. -/
theorem mem_isCompatible (hZinj : Function.Injective (algebraMap ℤ_[p] R))
    (hρ : IsHardlyRamified hpodd hv ρ) :
    IsInHardlyRamifiedFamily (p := p) ρ := by
  -- Step 1: the coefficient ring embeds into `ℚ̄_p` over `ℤ_[p]`,
  -- injectively and continuously.
  have hembed : ∃ i : R →+* AlgebraicClosure ℚ_[p], Function.Injective i ∧
      i.comp (algebraMap ℤ_[p] R) = algebraMap ℤ_[p] (AlgebraicClosure ℚ_[p]) ∧
      Continuous i := by
    haveI : Module.IsTorsionFree ℤ_[p] R :=
      Module.isTorsionFree_iff_algebraMap_injective.mpr hZinj
    have hZbarinj : Function.Injective (algebraMap ℤ_[p] (AlgebraicClosure ℚ_[p])) := by
      rw [IsScalarTower.algebraMap_eq ℤ_[p] ℚ_[p] (AlgebraicClosure ℚ_[p])]
      exact (algebraMap ℚ_[p] (AlgebraicClosure ℚ_[p])).injective.comp
        (FaithfulSMul.algebraMap_injective ℤ_[p] ℚ_[p])
    haveI : Module.IsTorsionFree ℤ_[p] (AlgebraicClosure ℚ_[p]) :=
      Module.isTorsionFree_iff_algebraMap_injective.mpr hZbarinj
    haveI : Algebra.IsIntegral ℤ_[p] R := Algebra.IsIntegral.of_finite ℤ_[p] R
    haveI : Algebra.IsAlgebraic ℤ_[p] R := inferInstance
    haveI : ContinuousSMul ℤ_[p] (AlgebraicClosure ℚ_[p]) :=
      continuousSMul_of_algebraMap _ _
        ((continuous_algebraMap ℚ_[p] _).comp continuous_subtype_val)
    let j : R →ₐ[ℤ_[p]] AlgebraicClosure ℚ_[p] := IsAlgClosed.lift
    have hj_inj : Function.Injective (j : R →+* AlgebraicClosure ℚ_[p]) := by
      rw [RingHom.injective_iff_ker_eq_bot]
      -- the kernel is an ideal of the integral extension `R/ℤ_[p]`
      -- contracting to `⊥` (as `j` restricts to the injective
      -- `algebraMap ℤ_[p] ℚ̄_p`), hence is `⊥`
      apply Ideal.eq_bot_of_comap_eq_bot (R := ℤ_[p])
      rw [RingHom.comap_ker, AlgHom.comp_algebraMap]
      exact (RingHom.injective_iff_ker_eq_bot _).mp hZbarinj
    have hj_cont : Continuous j := IsModuleTopology.continuous_of_linearMap j.toLinearMap
    exact ⟨j, hj_inj, AlgHom.comp_algebraMap j, hj_cont⟩
  obtain ⟨i, hinj, hcompat, hconti⟩ := hembed
  letI ia : Algebra R (AlgebraicClosure ℚ_[p]) := i.toAlgebra
  haveI ics : ContinuousSMul R (AlgebraicClosure ℚ_[p]) :=
    continuousSMul_of_algebraMap _ _ hconti
  haveI itower : IsScalarTower ℤ_[p] R (AlgebraicClosure ℚ_[p]) :=
    IsScalarTower.of_algebraMap_eq' hcompat.symm
  have hinj' : Function.Injective (algebraMap R (AlgebraicClosure ℚ_[p])) := hinj
  -- Step 2 (the automorphy core, decomposed 2026-07-22): the eigensystem
  -- stratum descends the Frobenius data to a number field; the spreading
  -- stratum builds the compatible family attached to that eigensystem.
  obtain ⟨E, iE, iNE, σ, hσcompat, hσodd, ψ, r', hψ⟩ :=
    exists_family_of_eigensystem hpodd hv hZinj hinj' hρ
      (exists_numberField_eigensystem hpodd hv hZinj hinj' hρ)
  unfold IsInHardlyRamifiedFamily
  refine ⟨E, iE, iNE, σ, hσcompat, hσodd, ia, ics, hinj', ψ, r', ?_⟩
  exact hψ

end GaloisRepresentation.IsHardlyRamified
