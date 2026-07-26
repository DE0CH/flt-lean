/-
Copyright (c) 2025 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard
-/
module

public import Fermat.FLT.GaloisRepresentation.HardlyRamified.Defs
public import Fermat.FLT.Deformations.RepresentationTheory.GaloisRepFamily
-- the modularity interface: the weight-2 eigenform carrier and the
-- sorried modularity/attachment nodes consumed by the automorphy atoms
public import Fermat.FLT.Modularity.Interface
-- `localInertia_two_eq_map_padic` (the PROVEN inertia bridge at `2`
-- between the place-spelled `localInertiaGroup` and the
-- `ℚ_[2]`/`Z2bar`-spelled inertia of the tame-at-two clause), consumed
-- by the at-2 stage of the Eisenstein character dichotomy. Non-public:
-- used in proofs only.
import Fermat.FLT.GaloisRepresentation.HardlyRamified.ModThree
-- the generic connected–étale idempotent package
-- (`Bialgebra.exists_connected_counit_idempotent`,
-- `mul_eq_zero_or_mul_eq_of_minimal`) and the generic `IsAdicComplete`
-- instance for `adicCompletionIntegers`, consumed by the
-- connected–étale cyclotomic assembly at `p`. Non-public: proofs only.
import Fermat.FLT.GroupScheme.ConnectedEtale
-- the generic convolution/points transport toolkit (`WithConv`
-- bridges, `liftEquiv_symm_convMul`, `vendored_mul_eq_convMul`),
-- consumed by the same assembly. Non-public: proofs only.
import Fermat.FLT.Deformations.RepresentationTheory.FlatProlongation
-- mathlib's convolution monoid on Hopf/bialgebra points (`WithConv`,
-- its `Mul`/`Pow`/`Monoid` instances and the antipode as an algebra
-- hom): `WithConv.toConv`/`ofConv` and the convolution POWER appear in
-- the STATEMENT of the shared brick `convPow_apply_of_comul_absorbs`
-- below, hence public.
public import Mathlib.RingTheory.HopfAlgebra.Convolution
-- the CONSTANT group scheme `Spec (G → R)` — the Hopf algebra of functions
-- on a finite group, dual to its group law. Absent from mathlib on this pin
-- (`Pi.instCoalgebraStruct` is the componentwise structure, not this one), so
-- built there; it is the witness for `hasFlatProlongationAt_trivialQuotChar`
-- below, whose STATEMENT does not mention it — but the general-`K` helper
-- `hasFlatProlongationAt_trivialQuotChar_of_base` is proved in this module and
-- consumes it, so the import is public.
public import Fermat.FLT.Mathlib.RingTheory.HopfAlgebra.GroupFunctions
-- `isIntegral_padicInt_of_spectralNorm_le_one`, consumed by the
-- `ValuationRing` instance of the concrete coefficient ring below. It used to
-- be declared in this file; it moved upstream (2026-07-25) so that the
-- Ribet-cut hull leaf `exists_padicIntegers_dvr_hull` in
-- `Modularity/Interface.lean` — which this file imports, hence cannot be
-- imported BY — can share it. Imported directly rather than relied on
-- transitively through `Modularity/Interface`.
public import Fermat.FLT.Mathlib.RingTheory.PadicIntegralClosure
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
-- `Polynomial.eval_one_cyclotomic_prime_pow` + the primitive-root product
-- factorization: distinct `p`-power roots of unity differ by a `2`-adic unit,
-- the arithmetic core of `cyclotomicCharacter_eq_one_of_mem_inertia_two`
import Mathlib.RingTheory.Polynomial.Cyclotomic.Eval
-- `IsLocalRing.isOpen_maximalIdeal_pow`: openness of the maximal-ideal powers
-- of a compact Hausdorff Noetherian topological ring, the level filtration of
-- the flat trace identity at `p` (same import as in Threeadic)
import Mathlib.Topology.Algebra.Ring.Compact

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

omit [IsDomain R] [Module.Finite ℤ_[p] R] [IsModuleTopology ℤ_[p] R] in
set_option backward.isDefEq.respectTransparency false in
/-- **Diagonal characters die on inertia away from `{2, p}`** (PROVEN):
first route stage of `char_add_char_eq_one_add_cyclotomicCharacter`.
At a prime `q ∉ {2, p}` a hardly ramified `ρ` is unramified, so on the
(image in `G_ℚ` of the) local inertia at `q` every `ρ g` is the
identity, whose characteristic polynomial is `(X - 1)²`; a pair of
characters splitting the mapped characteristic polynomials therefore
satisfies `(X - χ₁ g)(X - χ₂ g) = (X - 1)²`, and evaluating at `χᵢ g`
forces `χᵢ g = 1` (`ℚ̄_p` has no nilpotents). -/
theorem char_eq_one_of_mem_localInertiaGroup_of_ne
    [Algebra R (AlgebraicClosure ℚ_[p])]
    (hρ : IsHardlyRamified hpodd hv ρ)
    (χ₁ χ₂ : Field.absoluteGaloisGroup ℚ → AlgebraicClosure ℚ_[p])
    (hchar : ∀ g, ((ρ g).charpoly).map (algebraMap R (AlgebraicClosure ℚ_[p])) =
      (Polynomial.X - Polynomial.C (χ₁ g)) * (Polynomial.X - Polynomial.C (χ₂ g)))
    {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) (hqp : q ≠ p)
    (σ : Field.absoluteGaloisGroup (HeightOneSpectrum.adicCompletion ℚ
      hq.toHeightOneSpectrumRingOfIntegersRat))
    (hσ : σ ∈ localInertiaGroup hq.toHeightOneSpectrumRingOfIntegersRat) :
    χ₁ (Field.absoluteGaloisGroup.map (algebraMap ℚ (HeightOneSpectrum.adicCompletion ℚ
      hq.toHeightOneSpectrumRingOfIntegersRat)) σ) = 1 ∧
    χ₂ (Field.absoluteGaloisGroup.map (algebraMap ℚ (HeightOneSpectrum.adicCompletion ℚ
      hq.toHeightOneSpectrumRingOfIntegersRat)) σ) = 1 := by
  classical
  set g₀ := Field.absoluteGaloisGroup.map (algebraMap ℚ (HeightOneSpectrum.adicCompletion ℚ
    hq.toHeightOneSpectrumRingOfIntegersRat)) σ with hg₀def
  have hUn : ρ.IsUnramifiedAt hq.toHeightOneSpectrumRingOfIntegersRat :=
    hρ.isUnramified q hq ⟨hq2, hqp⟩
  have hker : ρ g₀ = 1 := by
    have h1 : (ρ.toLocal hq.toHeightOneSpectrumRingOfIntegersRat) σ = 1 :=
      hUn.localInertiaGroup_le hσ
    rw [GaloisRep.toLocal_apply] at h1
    rw [hg₀def]
    convert h1 using 4
    exact Subsingleton.elim _ _
  have hfr : Module.finrank R V = 2 := Module.finrank_eq_of_rank_eq hv
  have hpoly := hchar g₀
  rw [hker, LinearMap.charpoly_one, hfr, Polynomial.map_pow, Polynomial.map_sub,
    Polynomial.map_X, Polynomial.map_one] at hpoly
  constructor
  · have h := congrArg (Polynomial.eval (χ₁ g₀)) hpoly
    simp only [Polynomial.eval_pow, Polynomial.eval_mul, Polynomial.eval_sub,
      Polynomial.eval_X, Polynomial.eval_C, Polynomial.eval_one, sub_self, zero_mul] at h
    rwa [sq_eq_zero_iff, sub_eq_zero] at h
  · have h := congrArg (Polynomial.eval (χ₂ g₀)) hpoly
    simp only [Polynomial.eval_pow, Polynomial.eval_mul, Polynomial.eval_sub,
      Polynomial.eval_X, Polynomial.eval_C, Polynomial.eval_one, sub_self, mul_zero] at h
    rwa [sq_eq_zero_iff, sub_eq_zero] at h

include hpodd in
set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1000000 in
/-- **The cyclotomic character dies on inertia at `2`** (PROVEN
2026-07-24): for an odd prime `p`, the `p`-adic cyclotomic character is
trivial on the (image in `G_ℚ` of the) inertia at `2` — the extensions
`ℚ_2(μ_{p^n})/ℚ_2` are unramified, i.e. inertia at `2` acts trivially
on `p`-power roots of unity. Proof (the Frobenius-free core of
`adicArithFrob_rootsOfUnity_pow`, generalizing the `p = 3` case
`cyclotomicCharacter_algebraMap_eq_one_of_inertia_two` of ModThree):
a `p^n`-th root of unity `z` has spectral valuation `1`, so lies in
`Z2bar`, and an inertia element `τ` moves it by `v (τ z - z) < 1`; but
a NONtrivial `p`-power root of unity `u` has `v (u - 1) = 1` — by
`Polynomial.eval_one_cyclotomic_prime_pow` the product of `1 - μ` over
the primitive `p^m`-th roots is `p`, a `2`-adic unit since `p` is odd,
while every factor has `v ≤ 1`, forcing `v = 1` on each factor — so
`τ z = z` exactly. Hence every finite level of the cyclotomic
character is trivial (`modularCyclotomicCharacter.unique`) and
`p`-adic continuity (`PadicInt.ext_of_toZModPow`) concludes. -/
theorem cyclotomicCharacter_eq_one_of_mem_inertia_two
    (τ : Field.absoluteGaloisGroup ℚ_[2])
    (hτ : τ ∈ AddSubgroup.inertia
      ((IsLocalRing.maximalIdeal Z2bar).toAddSubgroup : AddSubgroup Z2bar)
      (Field.absoluteGaloisGroup ℚ_[2])) :
    cyclotomicCharacter (AlgebraicClosure ℚ) p
      ((Field.absoluteGaloisGroup.map (algebraMap ℚ ℚ_[2]) τ).toRingEquiv) = 1 := by
  classical
  -- roots of unity have spectral valuation `1`
  have hval_of_root : ∀ (m : ℕ), m ≠ 0 → ∀ w : AlgebraicClosure ℚ_[2],
      w ^ m = 1 → Valued.v w = 1 := by
    intro m hm w hw
    have h := congrArg Valued.v hw
    rw [map_pow, map_one] at h
    rcases lt_trichotomy (Valued.v w) 1 with hlt | heq | hgt
    · exfalso
      have hcon : Valued.v w ^ m < 1 := by
        calc Valued.v w ^ m ≤ Valued.v w ^ 1 :=
              pow_le_pow_right_of_le_one' (le_of_lt hlt) (Nat.one_le_iff_ne_zero.mpr hm)
          _ = Valued.v w := pow_one _
          _ < 1 := hlt
      rw [h] at hcon
      exact lt_irrefl _ hcon
    · exact heq
    · exfalso
      have hcon : 1 < Valued.v w ^ m := by
        calc 1 < Valued.v w := hgt
          _ = Valued.v w ^ 1 := (pow_one _).symm
          _ ≤ Valued.v w ^ m :=
              pow_le_pow_right' (le_of_lt hgt) (Nat.one_le_iff_ne_zero.mpr hm)
      rw [h] at hcon
      exact lt_irrefl _ hcon
  -- the odd prime `p` is a `2`-adic unit in the spectral valuation
  have hvp : Valued.v (((p : ℕ) : AlgebraicClosure ℚ_[2])) = 1 := by
    have hpnorm : ‖((p : ℕ) : ℚ_[2])‖ = 1 := by
      rw [Padic.norm_natCast_eq_one_iff]
      exact Nat.coprime_two_left.mpr hpodd
    have halg : ((p : ℕ) : AlgebraicClosure ℚ_[2]) =
        algebraMap ℚ_[2] (AlgebraicClosure ℚ_[2]) ((p : ℕ) : ℚ_[2]) := by
      rw [map_natCast]
    have hkey : ((Valued.v (algebraMap ℚ_[2] (AlgebraicClosure ℚ_[2])
        ((p : ℕ) : ℚ_[2])) : NNReal) : ℝ) = ‖((p : ℕ) : ℚ_[2])‖ := by
      rw [← spectralNorm_extends (K := ℚ_[2]) (L := AlgebraicClosure ℚ_[2]) _]
      rfl
    rw [halg]
    apply NNReal.coe_injective
    rw [hkey, hpnorm, NNReal.coe_one]
  -- a nontrivial `p`-power root of unity keeps valuation `1` away from `1`:
  -- the factors of `Φ_{p^m}(1) = p` all have `v ≤ 1` with product a unit
  have hsub_val : ∀ (N : ℕ) (u : AlgebraicClosure ℚ_[2]), u ^ (p ^ N) = 1 →
      u ≠ 1 → Valued.v (u - 1) = 1 := by
    intro N u hu hune
    obtain ⟨m, -, hordeq⟩ :=
      (Nat.dvd_prime_pow hp.out).mp (orderOf_dvd_of_pow_eq_one hu)
    have hm0 : m ≠ 0 := by
      rintro rfl
      rw [pow_zero] at hordeq
      exact hune (orderOf_eq_one_iff.mp hordeq)
    have hprim : IsPrimitiveRoot u (p ^ m) := hordeq ▸ IsPrimitiveRoot.orderOf u
    obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 :=
      ⟨m - 1, (Nat.succ_pred_eq_of_pos (Nat.pos_of_ne_zero hm0)).symm⟩
    have hppos : 0 < p ^ (m' + 1) := pow_pos hp.out.pos _
    have heval : (∏ μ ∈ primitiveRoots (p ^ (m' + 1)) (AlgebraicClosure ℚ_[2]),
        ((1 : AlgebraicClosure ℚ_[2]) - μ)) =
        ((p : ℕ) : AlgebraicClosure ℚ_[2]) := by
      have h1 := Polynomial.eval_one_cyclotomic_prime_pow
        (R := AlgebraicClosure ℚ_[2]) (p := p) m'
      rw [Polynomial.cyclotomic_eq_prod_X_sub_primitiveRoots hprim,
        Polynomial.eval_prod] at h1
      simpa using h1
    have hle : ∀ μ ∈ primitiveRoots (p ^ (m' + 1)) (AlgebraicClosure ℚ_[2]),
        Valued.v ((1 : AlgebraicClosure ℚ_[2]) - μ) ≤ 1 := by
      intro μ hμ
      have hμval : Valued.v μ = 1 :=
        hval_of_root _ hppos.ne' μ ((mem_primitiveRoots hppos).mp hμ).pow_eq_one
      refine le_trans (Valued.v.map_sub _ _) ?_
      rw [map_one, hμval]
      exact le_of_eq (max_self 1)
    have hprod : (∏ μ ∈ primitiveRoots (p ^ (m' + 1)) (AlgebraicClosure ℚ_[2]),
        Valued.v ((1 : AlgebraicClosure ℚ_[2]) - μ)) = 1 := by
      rw [← map_prod, heval, hvp]
    have h1u := (Finset.prod_eq_one_iff_of_le_one' hle).mp hprod u
      ((mem_primitiveRoots hppos).mpr hprim)
    rw [show u - 1 = -((1 : AlgebraicClosure ℚ_[2]) - u) by ring, Valuation.map_neg]
    exact h1u
  -- inertia at `2` fixes every `p`-power root of unity of `ℚ_[2]ᵃˡᵍ`
  have hfix2 : ∀ (n : ℕ) (z : AlgebraicClosure ℚ_[2]), z ^ (p ^ n) = 1 →
      τ z = z := by
    intro n z hz
    have hpn : (p : ℕ) ^ n ≠ 0 := pow_ne_zero n hp.out.ne_zero
    have hzval : Valued.v z = 1 := hval_of_root _ hpn z hz
    have hz0 : z ≠ 0 := by
      intro h0
      rw [h0, map_zero] at hzval
      exact zero_ne_one hzval
    have hzmem : z ∈ Z2bar := by
      rw [Valuation.mem_valuationSubring_iff, hzval]
    have hτzpow : (τ z) ^ (p ^ n) = 1 := by rw [← map_pow, hz, map_one]
    by_contra hne
    -- the inertia condition: `v (τ z − z) < 1`
    have hdiffval : Valued.v (τ z - z) < 1 := by
      have hin := (AddSubgroup.mem_inertia.mp hτ) ⟨z, hzmem⟩
      set y : Z2bar := τ • (⟨z, hzmem⟩ : Z2bar) - ⟨z, hzmem⟩ with hydef
      have hy1 : (y : AlgebraicClosure ℚ_[2]) = τ z - z := rfl
      have hnu : ¬IsUnit y := by
        have hmem : y ∈ IsLocalRing.maximalIdeal Z2bar := hin
        rwa [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hmem
      have hyval : Valued.v (τ z - z) ≤ 1 := by
        refine le_trans (Valued.v.map_sub _ _) ?_
        rw [show Valued.v (τ z) = 1 from hval_of_root _ hpn _ hτzpow, hzval]
        exact le_of_eq (max_self 1)
      rcases lt_or_eq_of_le hyval with hlt | heq
      · exact hlt
      · exfalso
        apply hnu
        have hne0 : (τ z - z : AlgebraicClosure ℚ_[2]) ≠ 0 := by
          intro h0
          rw [h0, map_zero] at heq
          exact zero_ne_one heq
        have hinvmem : (τ z - z : AlgebraicClosure ℚ_[2])⁻¹ ∈ Z2bar := by
          rw [Valuation.mem_valuationSubring_iff, map_inv₀, heq, inv_one]
        refine isUnit_iff_exists.mpr
          ⟨(⟨(τ z - z)⁻¹, hinvmem⟩ : Z2bar), ?_, ?_⟩
        · apply Subtype.ext
          show (y : AlgebraicClosure ℚ_[2]) * (τ z - z)⁻¹ = 1
          rw [hy1]
          exact mul_inv_cancel₀ hne0
        · apply Subtype.ext
          show (τ z - z)⁻¹ * (y : AlgebraicClosure ℚ_[2]) = 1
          rw [hy1]
          exact inv_mul_cancel₀ hne0
    -- but `τ z / z` is a nontrivial `p`-power root of unity, so the
    -- difference is a `Z2bar`-unit: contradiction
    have hu : (τ z * z⁻¹) ^ (p ^ n) = 1 := by
      rw [mul_pow, hτzpow, one_mul, inv_pow, hz, inv_one]
    have hune : τ z * z⁻¹ ≠ 1 := fun h1 => hne ((mul_inv_eq_one₀ hz0).mp h1)
    have hfac : τ z - z = (τ z * z⁻¹ - 1) * z := by
      rw [sub_mul, one_mul, mul_assoc, inv_mul_cancel₀ hz0, mul_one]
    rw [hfac, map_mul, hzval, mul_one, hsub_val n _ hu hune] at hdiffval
    exact lt_irrefl _ hdiffval
  -- conclude level by level through `p`-adic continuity
  refine Units.ext ?_
  rw [Units.val_one]
  refine PadicInt.ext_of_toZModPow.mp fun n => ?_
  rcases Nat.eq_zero_or_pos n with rfl | hnpos
  · haveI : Subsingleton (ZMod (p ^ 0)) := by rw [pow_zero]; infer_instance
    exact Subsingleton.elim _ _
  haveI : NeZero (p ^ n) := ⟨pow_ne_zero n hp.out.ne_zero⟩
  rw [map_one, cyclotomicCharacter.toZModPow]
  refine (modularCyclotomicCharacter.unique (AlgebraicClosure ℚ)
    (HasEnoughRootsOfUnity.natCard_rootsOfUnity (AlgebraicClosure ℚ) (p ^ n))
    _ ?_).symm
  intro t ht
  have hval1 : ((1 : ZMod (p ^ n))).val = 1 := by
    rw [ZMod.val_one_eq_one_mod,
      Nat.mod_eq_of_lt (Nat.one_lt_pow hnpos.ne' hp.out.one_lt)]
  rw [hval1, pow_one]
  have ht1 : ((t : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ) ^ (p ^ n) = 1 := by
    rw [← Units.val_pow_eq_pow_val, (mem_rootsOfUnity _ t).mp ht, Units.val_one]
  show (Field.absoluteGaloisGroup.map (algebraMap ℚ ℚ_[2]) τ)
      ((t : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ) =
    ((t : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ)
  apply (AlgebraicClosure.map (algebraMap ℚ ℚ_[2])).injective
  rw [Field.absoluteGaloisGroup.lift_map (algebraMap ℚ ℚ_[2]) τ]
  exact hfix2 n _ (by rw [← map_pow, ht1, map_one])

/-- **`1`-dimensional characteristic polynomial over a commutative
ring** (PROVEN): an endomorphism of a module with a basis indexed by
`Unit` has characteristic polynomial `X - C (trace)`. The general-ring
analogue of `LinearMap.charpoly_eq_X_sub_C_trace_of_finrank_eq_one`
above (which is stated over a field, where a basis can be chosen from
the finrank alone); used to evaluate the diagonal blocks of
`charpoly_eq_of_mem_inertia_two` over the local coefficient ring. -/
theorem _root_.LinearMap.charpoly_eq_X_sub_C_trace_of_basis
    {R₀ M₀ : Type*} [CommRing R₀] [AddCommGroup M₀] [Module R₀ M₀]
    [Module.Finite R₀ M₀] [Module.Free R₀ M₀]
    (b : Module.Basis Unit R₀ M₀) (f : M₀ →ₗ[R₀] M₀) :
    f.charpoly = Polynomial.X - Polynomial.C (LinearMap.trace R₀ M₀ f) := by
  classical
  rw [← f.charpoly_toMatrix b, LinearMap.trace_eq_matrix_trace R₀ b f,
    Matrix.charpoly, Matrix.det_unique, Matrix.charmatrix_apply_eq, Matrix.trace]
  simp

omit [IsDomain R] [Module.Finite ℤ_[p] R] [IsModuleTopology ℤ_[p] R] in
set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1000000 in
/-- **The tame-at-two triangular characteristic polynomial on inertia**
(PROVEN 2026-07-24): for a hardly ramified `ρ` and an inertia element
`τ` at `2` (spelled over `ℚ_[2]`, matching the `isTameAtTwo` clause),
the characteristic polynomial of `ρ` at the image of `τ` is
`(X - χ_cyc(τ))(X - 1)` over `R`. Pure linear algebra over the local
ring `R` plus the `IsHardlyRamified` clauses: the tame-at-two datum
`(π, δ)` exhibits `W := ker π` as a `ρ(G_2)`-stable direct summand of
`V` (finite and flat as a retract of `V` along the splitting through
any `π`-preimage of `1`, hence free of rank `1` over the local ring
`R` by `Module.free_of_flat_of_isLocalRing` and basis counting); on
`V ⧸ W ≅ R` the map `ρ τ` descends to `δ τ = 1` (inertia lies in
`δ.ker`), so the block-triangular factorization
`LinearMap.charpoly_eq_charpoly_restrict_mul_charpoly_mapQ` reads
`charpoly (ρ τ) = (X - C s)(X - C 1)` with `s` the trace of the
restriction to the line `W`; finally `s = det (ρ τ) = χ_cyc(τ)` by
reading the determinant off the constant coefficient
(`LinearMap.det_eq_sign_charpoly_coeff`) against the
cyclotomic-determinant clause. -/
theorem charpoly_eq_of_mem_inertia_two
    (hρ : IsHardlyRamified hpodd hv ρ)
    (τ : Field.absoluteGaloisGroup ℚ_[2])
    (hτ : τ ∈ AddSubgroup.inertia
      ((IsLocalRing.maximalIdeal Z2bar).toAddSubgroup : AddSubgroup Z2bar)
      (Field.absoluteGaloisGroup ℚ_[2])) :
    (ρ (Field.absoluteGaloisGroup.map (algebraMap ℚ ℚ_[2]) τ)).charpoly =
      (Polynomial.X - Polynomial.C (algebraMap ℤ_[p] R
        ((cyclotomicCharacter (AlgebraicClosure ℚ) p
          ((Field.absoluteGaloisGroup.map (algebraMap ℚ ℚ_[2])
            τ).toRingEquiv) : ℤ_[p]ˣ) : ℤ_[p]))) *
      (Polynomial.X - Polynomial.C 1) := by
  classical
  obtain ⟨π, hπsurj, δ, hδ⟩ := hρ.isTameAtTwo
  have hδτ : δ τ = 1 := (hδ τ 0).2.1 hτ
  set e : Module.End R V := ρ (Field.absoluteGaloisGroup.map (algebraMap ℚ ℚ_[2]) τ)
    with hedef
  -- `π` intertwines `e` with `δ τ = 1`
  have hcomm : ∀ v : V, π (e v) = π v := by
    intro v
    have h1 := (hδ τ v).1
    rw [GaloisRep.map_apply, hδτ] at h1
    simpa using h1
  -- a `π`-preimage of `1` and the induced projection of `V` onto `ker π`
  obtain ⟨v₀, hv₀⟩ := hπsurj 1
  set s : R →ₗ[R] V := LinearMap.toSpanSingleton R V v₀ with hsdef
  have hπs : ∀ r : R, π (s r) = r := by
    intro r
    rw [hsdef, LinearMap.toSpanSingleton_apply, map_smul, hv₀, smul_eq_mul, mul_one]
  set Q : V →ₗ[R] V := LinearMap.id - s ∘ₗ π with hQdef
  set W : Submodule R V := LinearMap.ker π with hWdef
  have hQmem : ∀ v : V, Q v ∈ W := by
    intro v
    rw [hWdef, LinearMap.mem_ker, hQdef]
    simp only [LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply]
    rw [map_sub, hπs, sub_self]
  have hQr_id : ∀ w : W, LinearMap.codRestrict W Q hQmem (w : V) = w := by
    intro w
    apply Subtype.ext
    rw [LinearMap.codRestrict_apply, hQdef]
    simp only [LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply]
    rw [show π (w : V) = 0 from LinearMap.mem_ker.mp (hWdef ▸ w.2), map_zero,
      sub_zero]
  -- `W` is a retract of the free module `V`: finite, flat, hence free
  haveI : Module.Finite R W :=
    Module.Finite.of_surjective (LinearMap.codRestrict W Q hQmem)
      (fun w => ⟨(w : V), hQr_id w⟩)
  haveI : Module.Flat R W :=
    Module.Flat.of_retract W.subtype (LinearMap.codRestrict W Q hQmem)
      (LinearMap.ext fun w => hQr_id w)
  haveI : Module.Free R W := Module.free_of_flat_of_isLocalRing
  -- the quotient line `V ⧸ W ≅ R` and its `Unit`-indexed basis
  have bQ : Module.Basis Unit R (V ⧸ W) :=
    (Module.Basis.singleton Unit R).map (π.quotKerEquivOfSurjective hπsurj).symm
  haveI : Module.Free R (V ⧸ W) := Module.Free.of_basis bQ
  haveI : Module.Finite R (V ⧸ W) := Module.Finite.of_basis bQ
  -- `W` is a line: `2 = finrank V = card (basis of W) + 1`
  have bW0 := Module.Free.chooseBasis R W
  have hcard : Fintype.card (Module.Free.ChooseBasisIndex R W) = 1 := by
    have hb := Module.finrank_eq_card_basis (Module.Basis.sumQuot bW0 bQ)
    rw [Module.finrank_eq_of_rank_eq hv, Fintype.card_sum, Fintype.card_unit] at hb
    exact Nat.succ_injective hb.symm
  have bW : Module.Basis Unit R W := bW0.reindex
    (Fintype.equivOfCardEq (by rw [hcard, Fintype.card_unit]))
  -- `e` preserves `W`
  have he : W ≤ W.comap e := by
    intro w hw
    rw [hWdef, LinearMap.mem_ker] at hw
    rw [Submodule.mem_comap, hWdef, LinearMap.mem_ker, hcomm w]
    exact hw
  -- the quotient block is the identity: `π ∘ e = π`
  have hmapQ : W.mapQ W e he = LinearMap.id := by
    refine Submodule.linearMap_qext _ ?_
    refine LinearMap.ext fun v => ?_
    simp only [LinearMap.comp_apply, Submodule.mkQ_apply, Submodule.mapQ_apply,
      LinearMap.id_apply]
    rw [Submodule.Quotient.eq, hWdef, LinearMap.mem_ker, map_sub, hcomm v, sub_self]
  have hQblock : (W.mapQ W e he).charpoly = Polynomial.X - Polynomial.C 1 := by
    have hfq : Module.finrank R (V ⧸ W) = 1 := by
      rw [Module.finrank_eq_card_basis bQ, Fintype.card_unit]
    rw [hmapQ, show (LinearMap.id : Module.End R (V ⧸ W)) = 1 from rfl,
      LinearMap.charpoly_one, hfq, pow_one, Polynomial.C_1]
  -- the block-triangular factorization along the line `W`
  have hchar : e.charpoly =
      (Polynomial.X - Polynomial.C (LinearMap.trace R W (e.restrict he))) *
      (Polynomial.X - Polynomial.C 1) := by
    rw [LinearMap.charpoly_eq_charpoly_restrict_mul_charpoly_mapQ W e he, hQblock,
      LinearMap.charpoly_eq_X_sub_C_trace_of_basis bW (e.restrict he)]
  -- identify the line scalar with the cyclotomic determinant
  have hdet1 := LinearMap.det_eq_sign_charpoly_coeff e
  rw [Module.finrank_eq_of_rank_eq hv, neg_one_sq, one_mul, hchar] at hdet1
  have hcoeff : ((Polynomial.X -
      Polynomial.C (LinearMap.trace R W (e.restrict he))) *
      (Polynomial.X - Polynomial.C 1) : Polynomial R).coeff 0 =
      LinearMap.trace R W (e.restrict he) := by
    rw [Polynomial.mul_coeff_zero]
    simp only [Polynomial.coeff_sub, Polynomial.coeff_X_zero, Polynomial.coeff_C_zero,
      zero_sub, neg_mul_neg, mul_one]
  rw [hcoeff] at hdet1
  have hcyc := hρ.det (Field.absoluteGaloisGroup.map (algebraMap ℚ ℚ_[2]) τ)
  rw [GaloisRep.det_apply, ← hedef] at hcyc
  rw [hcyc] at hdet1
  rw [hchar, ← hdet1]

omit [IsDomain R] [Module.Finite ℤ_[p] R] [IsModuleTopology ℤ_[p] R] in
/-- **Diagonal characters die on inertia at `2`** (FULLY PROVEN
2026-07-24, both sub-leaves discharged): second route stage
of `char_add_char_eq_one_add_cyclotomicCharacter`, per Serre (Duke
1987, §4.1). Assembly: the PROVEN inertia bridge
`localInertia_two_eq_map_padic` (ModThree) rewrites the place-spelled
inertia element as a `G_ℚ`-conjugate of a `ℚ_[2]`-spelled one, and
multiplicative characters into a commutative field are
conjugation-invariant; at the `ℚ_[2]`-spelled element the
characteristic polynomial is `(X - χ_cyc)(X - 1)` by the tame
triangularity (`charpoly_eq_of_mem_inertia_two`), and
`χ_cyc` is itself trivial there
(`cyclotomicCharacter_eq_one_of_mem_inertia_two`), so the split mapped
characteristic polynomial reads `(X - χ₁)(X - χ₂) = (X - 1)²` and
evaluation kills both characters, as in
`char_eq_one_of_mem_localInertiaGroup_of_ne`. -/
theorem char_eq_one_of_mem_localInertiaGroup_two
    [Algebra R (AlgebraicClosure ℚ_[p])]
    (hρ : IsHardlyRamified hpodd hv ρ)
    (χ₁ χ₂ : Field.absoluteGaloisGroup ℚ → AlgebraicClosure ℚ_[p])
    (hone₁ : χ₁ 1 = 1) (hone₂ : χ₂ 1 = 1)
    (hmul₁ : ∀ g h, χ₁ (g * h) = χ₁ g * χ₁ h)
    (hmul₂ : ∀ g h, χ₂ (g * h) = χ₂ g * χ₂ h)
    (hchar : ∀ g, ((ρ g).charpoly).map (algebraMap R (AlgebraicClosure ℚ_[p])) =
      (Polynomial.X - Polynomial.C (χ₁ g)) * (Polynomial.X - Polynomial.C (χ₂ g)))
    (σ : Field.absoluteGaloisGroup (HeightOneSpectrum.adicCompletion ℚ
      Nat.prime_two.toHeightOneSpectrumRingOfIntegersRat))
    (hσ : σ ∈ localInertiaGroup Nat.prime_two.toHeightOneSpectrumRingOfIntegersRat) :
    χ₁ (Field.absoluteGaloisGroup.map (algebraMap ℚ (HeightOneSpectrum.adicCompletion ℚ
      Nat.prime_two.toHeightOneSpectrumRingOfIntegersRat)) σ) = 1 ∧
    χ₂ (Field.absoluteGaloisGroup.map (algebraMap ℚ (HeightOneSpectrum.adicCompletion ℚ
      Nat.prime_two.toHeightOneSpectrumRingOfIntegersRat)) σ) = 1 := by
  classical
  obtain ⟨τ, hτ, c, hconj⟩ := localInertia_two_eq_map_padic hσ
  -- conjugation-invariance of the characters: their value at the
  -- place-spelled element is their value at the `ℚ_[2]`-spelled one
  have hred : ∀ χ : Field.absoluteGaloisGroup ℚ → AlgebraicClosure ℚ_[p],
      χ 1 = 1 → (∀ g h, χ (g * h) = χ g * χ h) →
      χ (Field.absoluteGaloisGroup.map (algebraMap ℚ (HeightOneSpectrum.adicCompletion ℚ
        Nat.prime_two.toHeightOneSpectrumRingOfIntegersRat)) σ) =
      χ (Field.absoluteGaloisGroup.map (algebraMap ℚ ℚ_[2]) τ) := by
    intro χ hone hmul
    rw [hconj]
    calc χ (c * Field.absoluteGaloisGroup.map (algebraMap ℚ ℚ_[2]) τ * c⁻¹)
        = χ c * χ (Field.absoluteGaloisGroup.map (algebraMap ℚ ℚ_[2]) τ) * χ c⁻¹ := by
          rw [hmul, hmul]
      _ = χ (Field.absoluteGaloisGroup.map (algebraMap ℚ ℚ_[2]) τ) * (χ c * χ c⁻¹) := by
          ring
      _ = χ (Field.absoluteGaloisGroup.map (algebraMap ℚ ℚ_[2]) τ) := by
          rw [← hmul, mul_inv_cancel, hone, mul_one]
  -- the split characteristic polynomial at the `ℚ_[2]`-spelled element
  -- is `(X - 1)²`, by the two sub-leaves
  have hB := charpoly_eq_of_mem_inertia_two hpodd hv hρ τ hτ
  rw [cyclotomicCharacter_eq_one_of_mem_inertia_two hpodd τ hτ, Units.val_one,
    map_one] at hB
  have hpoly := hchar (Field.absoluteGaloisGroup.map (algebraMap ℚ ℚ_[2]) τ)
  rw [hB, Polynomial.map_mul, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C,
    map_one, Polynomial.C_1] at hpoly
  refine ⟨?_, ?_⟩
  · rw [hred χ₁ hone₁ hmul₁]
    have h := congrArg (Polynomial.eval
      (χ₁ (Field.absoluteGaloisGroup.map (algebraMap ℚ ℚ_[2]) τ))) hpoly
    simp only [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X,
      Polynomial.eval_C, Polynomial.eval_one, sub_self, zero_mul] at h
    rwa [mul_self_eq_zero, sub_eq_zero] at h
  · rw [hred χ₂ hone₂ hmul₂]
    have h := congrArg (Polynomial.eval
      (χ₂ (Field.absoluteGaloisGroup.map (algebraMap ℚ ℚ_[2]) τ))) hpoly
    simp only [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X,
      Polynomial.eval_C, Polynomial.eval_one, sub_self, mul_zero] at h
    rwa [mul_self_eq_zero, sub_eq_zero] at h

-- Local abbreviations for the `p`-adic completion vocabulary of the
-- connected–étale skeleton at `p` (same pattern as the ModThree
-- block: the notations elaborate to exactly the spelled-out terms
-- used by the statements below).
local notation "𝒪ᵖᵥ" => IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ hp.out.toHeightOneSpectrumRingOfIntegersRat
local notation "ℚᵖᵥ" => IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ hp.out.toHeightOneSpectrumRingOfIntegersRat
local notation "ℚᵖᵥᵃˡᵍ" => AlgebraicClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ hp.out.toHeightOneSpectrumRingOfIntegersRat)

open WithConv

set_option backward.isDefEq.respectTransparency false in
set_option synthInstance.maxHeartbeats 1000000 in
set_option maxHeartbeats 2000000 in
/-- **Inertia congruence for convolution values at `p`** (PROVEN —
the general-`p` restatement of the ModThree helper
`lift_sub_lift_mem_of_localInertiaGroup_three`, same proof): for `σ`
in the local inertia group at `p` and two `𝒪ᵖᵥ`-points `χ, ψ` of a
module-finite Hopf order `G` (whose values are automatically integral
over `𝒪ᵖᵥ`), the paired lift values of `(σ ∘ χ, ψ)` and of `(χ, ψ)`
agree on every tensor modulo the maximal ideal of the integral
closure of `𝒪ᵖᵥ` in `ℚᵖᵥᵃˡᵍ`: inertia moves integral values only
within the maximal ideal (the DEFINING property of
`localInertiaGroup`), and the difference on a pure tensor is an
`𝔪`-multiple of an integral value. -/
theorem lift_sub_lift_mem_of_localInertiaGroup_p
    (G : Type) [CommRing G]
    [HopfAlgebra 𝒪ᵖᵥ G] [Module.Finite 𝒪ᵖᵥ G]
    (σ : Field.absoluteGaloisGroup ℚᵖᵥ)
    (hσ : σ ∈ localInertiaGroup hp.out.toHeightOneSpectrumRingOfIntegersRat)
    (χ ψ : G →ₐ[𝒪ᵖᵥ] ℚᵖᵥᵃˡᵍ) (t : G ⊗[𝒪ᵖᵥ] G) :
    Algebra.TensorProduct.lift ((σ.toAlgHom.restrictScalars 𝒪ᵖᵥ).comp χ) ψ
        (fun _ _ => Commute.all _ _) t -
      Algebra.TensorProduct.lift χ ψ (fun _ _ => Commute.all _ _) t ∈
      Submodule.map (Algebra.linearMap (IntegralClosure 𝒪ᵖᵥ ℚᵖᵥᵃˡᵍ) ℚᵖᵥᵃˡᵍ)
        (IsLocalRing.maximalIdeal (IntegralClosure 𝒪ᵖᵥ ℚᵖᵥᵃˡᵍ)) := by
  haveI : Algebra.IsIntegral 𝒪ᵖᵥ G := Algebra.IsIntegral.of_finite 𝒪ᵖᵥ G
  induction t using TensorProduct.induction_on with
  | zero =>
    simp only [map_zero, sub_self]
    exact Submodule.zero_mem _
  | add x y hx hy =>
    rw [map_add, map_add, add_sub_add_comm]
    exact Submodule.add_mem _ hx hy
  | tmul a b =>
    rw [Algebra.TensorProduct.lift_tmul, Algebra.TensorProduct.lift_tmul]
    have ha : IsIntegral 𝒪ᵖᵥ (χ a) :=
      (Algebra.IsIntegral.isIntegral (R := 𝒪ᵖᵥ) a).map χ
    have hb : IsIntegral 𝒪ᵖᵥ (ψ b) :=
      (Algebra.IsIntegral.isIntegral (R := 𝒪ᵖᵥ) b).map ψ
    set xa : IntegralClosure 𝒪ᵖᵥ ℚᵖᵥᵃˡᵍ := ⟨χ a, ha⟩
    set xb : IntegralClosure 𝒪ᵖᵥ ℚᵖᵥᵃˡᵍ := ⟨ψ b, hb⟩
    have hin := AddSubgroup.mem_inertia.mp hσ xa
    rw [Submodule.mem_toAddSubgroup] at hin
    have hval : algebraMap (IntegralClosure 𝒪ᵖᵥ ℚᵖᵥᵃˡᵍ) ℚᵖᵥᵃˡᵍ
        (σ • xa - xa) = σ (χ a) - χ a := by
      rw [map_sub]
      congr 1
    have hkey : ((σ.toAlgHom.restrictScalars 𝒪ᵖᵥ).comp χ) a * ψ b -
        χ a * ψ b =
        xb • (algebraMap (IntegralClosure 𝒪ᵖᵥ ℚᵖᵥᵃˡᵍ) ℚᵖᵥᵃˡᵍ
          (σ • xa - xa)) := by
      rw [hval, Algebra.smul_def]
      show σ (χ a) * ψ b - χ a * ψ b = ψ b * (σ (χ a) - χ a)
      ring
    rw [hkey]
    exact Submodule.smul_mem _ _ (Submodule.mem_map_of_mem hin)

set_option backward.isDefEq.respectTransparency false in
set_option synthInstance.maxHeartbeats 1000000 in
set_option maxHeartbeats 1000000 in
/-- **Group-like convolution powers evaluate by ordinary powers**
(PROVEN 2026-07-25 — brick (b) of the μ-type/Raynaud coordination
flagged in the docstring of
`connected_point_smul_eq_conv_pow_cyclotomicCharacter_of_hopf_package`
below, stated generically over any commutative base ring): let `e` be
a *connected counit idempotent* of a bialgebra `G₀` over `R₀` (counit
value `1`, comultiplication absorbing `e ⊗ e`), and let
`χ : G₀ →ₐ[R₀] C₀` be a point taking the value `1` on `e` — a
CONNECTED point. Then on any element `x` that is GROUP-LIKE relative
to the corner of `e` (`Δx · (e ⊗ e) = x ⊗ x` and `ε x = 1`) the `m`-th
convolution power of `χ` evaluates as the `m`-th ordinary power of the
value: `χ^{⋆ m}(x) = χ(x) ^ m`.

Proof: induction on `m`. The convolution unit is `algebraMap ∘ ε`
(`AlgHom.convOne_apply`), whose value at `x` is `1` by `ε x = 1`; and
`(χ^{⋆ i} ⋆ χ)(x) = lift (χ^{⋆ i}) χ (Δx)` (`AlgHom.convMul_apply`)
may be multiplied by
`lift (χ^{⋆ i}) χ (e ⊗ e) = χ^{⋆ i}(e) · χ(e) = 1` — the connectedness
of the convolution powers, which is this same statement at `x = e`,
proven separately by `convMul_apply_one_of_comul_absorbs` — so it
equals `lift (χ^{⋆ i}) χ (Δx · (e ⊗ e)) = lift (χ^{⋆ i}) χ (x ⊗ x) =
χ^{⋆ i}(x) · χ(x)`. -/
theorem convPow_apply_of_comul_absorbs {R₀ G₀ C₀ : Type*} [CommRing R₀]
    [CommRing G₀] [Bialgebra R₀ G₀] [CommRing C₀] [Algebra R₀ C₀]
    (e : G₀) (hεe : Coalgebra.counit (R := R₀) e = (1 : R₀))
    (habs : Coalgebra.comul (R := R₀) e * (e ⊗ₜ[R₀] e) = e ⊗ₜ[R₀] e)
    (χ : G₀ →ₐ[R₀] C₀) (hχe : χ e = 1)
    (x : G₀) (hεx : Coalgebra.counit (R := R₀) x = (1 : R₀))
    (hx : Coalgebra.comul (R := R₀) x * (e ⊗ₜ[R₀] e) = x ⊗ₜ[R₀] x)
    (m : ℕ) :
    ((toConv χ) ^ m).ofConv x = (χ x) ^ m := by
  -- the convolution powers of a connected point are connected
  have hpe : ∀ j : ℕ, ((toConv χ) ^ j).ofConv e = 1 := by
    intro j
    induction j with
    | zero =>
      rw [pow_zero]
      show algebraMap R₀ C₀ (Coalgebra.counit (R := R₀) e) = 1
      rw [hεe, map_one]
    | succ i ih =>
      rw [pow_succ]
      exact convMul_apply_one_of_comul_absorbs e habs _ _ ih hχe
  induction m with
  | zero =>
    rw [pow_zero, pow_zero]
    show algebraMap R₀ C₀ (Coalgebra.counit (R := R₀) x) = 1
    rw [hεx, map_one]
  | succ i ih =>
    have hone : Algebra.TensorProduct.lift (((toConv χ) ^ i).ofConv) χ
        (fun _ _ => Commute.all _ _) (e ⊗ₜ[R₀] e) = 1 := by
      rw [Algebra.TensorProduct.lift_tmul, hpe i, hχe, one_mul]
    have hval : ((toConv χ) ^ (i + 1)).ofConv x =
        Algebra.TensorProduct.lift (((toConv χ) ^ i).ofConv) χ
          (fun _ _ => Commute.all _ _) (Coalgebra.comul (R := R₀) x) := by
      rw [pow_succ]
      exact AlgHom.convMul_apply _ _ x
    rw [hval]
    calc Algebra.TensorProduct.lift (((toConv χ) ^ i).ofConv) χ
          (fun _ _ => Commute.all _ _) (Coalgebra.comul (R := R₀) x)
        = Algebra.TensorProduct.lift (((toConv χ) ^ i).ofConv) χ
            (fun _ _ => Commute.all _ _) (Coalgebra.comul (R := R₀) x) *
          Algebra.TensorProduct.lift (((toConv χ) ^ i).ofConv) χ
            (fun _ _ => Commute.all _ _) (e ⊗ₜ[R₀] e) := by rw [hone, mul_one]
      _ = Algebra.TensorProduct.lift (((toConv χ) ^ i).ofConv) χ
            (fun _ _ => Commute.all _ _)
            (Coalgebra.comul (R := R₀) x * (e ⊗ₜ[R₀] e)) := (map_mul _ _ _).symm
      _ = Algebra.TensorProduct.lift (((toConv χ) ^ i).ofConv) χ
            (fun _ _ => Commute.all _ _) (x ⊗ₜ[R₀] x) := by rw [hx]
      _ = ((toConv χ) ^ i).ofConv x * χ x :=
          Algebra.TensorProduct.lift_tmul _ _ _ _ _
      _ = (χ x) ^ i * χ x := by rw [ih]
      _ = (χ x) ^ (i + 1) := (pow_succ _ _).symm

set_option backward.isDefEq.respectTransparency false in
set_option synthInstance.maxHeartbeats 1000000 in
set_option maxHeartbeats 2000000 in
/-- **Convolution powers of a connected point of the generic fibre are
connected** (PROVEN 2026-07-25): if the geometric point `φ` of the
generic fibre `ℚᵖᵥ ⊗[𝒪ᵖᵥ] G` takes the value `1` on the base-changed
connected counit idempotent `1 ⊗ e₀`, then so does every convolution
power `φ ^ m` (the convolution monoid being the vendored bare-hom one
of `Deformations/RepresentationTheory/Etale.lean`). Proof: transport
along the tensor–hom adjunction `AlgHom.liftEquiv` to the `𝒪ᵖᵥ`-points
(`liftEquiv_symm_convOne`/`liftEquiv_symm_convMul` turn the vendored
powers into `WithConv` powers of `χ := φ ∘ includeRight`, whose value
at `e₀` is `φ (1 ⊗ e₀)`), then apply
`convPow_apply_of_comul_absorbs` at `x = e₀`. -/
theorem convPow_apply_one_of_comul_absorbs_p
    (G : Type) [CommRing G] [Bialgebra 𝒪ᵖᵥ G]
    (e₀ : G) (hε₀ : Coalgebra.counit (R := 𝒪ᵖᵥ) e₀ = (1 : 𝒪ᵖᵥ))
    (hcomul₀ : Coalgebra.comul (R := 𝒪ᵖᵥ) e₀ * (e₀ ⊗ₜ[𝒪ᵖᵥ] e₀) =
      e₀ ⊗ₜ[𝒪ᵖᵥ] e₀)
    (φ : ℚᵖᵥ ⊗[𝒪ᵖᵥ] G →ₐ[ℚᵖᵥ] ℚᵖᵥᵃˡᵍ)
    (hφe : φ ((1 : ℚᵖᵥ) ⊗ₜ[𝒪ᵖᵥ] e₀) = 1) (m : ℕ) :
    (φ ^ m) ((1 : ℚᵖᵥ) ⊗ₜ[𝒪ᵖᵥ] e₀) = 1 := by
  have hχe : (AlgHom.liftEquiv 𝒪ᵖᵥ ℚᵖᵥ G ℚᵖᵥᵃˡᵍ).symm φ e₀ = 1 := hφe
  have htrans : ∀ j : ℕ, (AlgHom.liftEquiv 𝒪ᵖᵥ ℚᵖᵥ G ℚᵖᵥᵃˡᵍ).symm (φ ^ j) =
      ((toConv ((AlgHom.liftEquiv 𝒪ᵖᵥ ℚᵖᵥ G ℚᵖᵥᵃˡᵍ).symm φ)) ^ j).ofConv := by
    intro j
    induction j with
    | zero =>
      rw [pow_zero, pow_zero, vendored_one_eq_convOne, liftEquiv_symm_convOne]
    | succ i ih =>
      rw [pow_succ, vendored_mul_eq_convMul, liftEquiv_symm_convMul,
        WithConv.ofConv_toConv, WithConv.ofConv_toConv, ih, pow_succ,
        WithConv.toConv_ofConv]
  have hval : (φ ^ m) ((1 : ℚᵖᵥ) ⊗ₜ[𝒪ᵖᵥ] e₀) =
      (AlgHom.liftEquiv 𝒪ᵖᵥ ℚᵖᵥ G ℚᵖᵥᵃˡᵍ).symm (φ ^ m) e₀ := rfl
  rw [hval, htrans m, convPow_apply_of_comul_absorbs e₀ hε₀ hcomul₀ _ hχe e₀
    hε₀ hcomul₀ m, hχe, one_pow]

set_option backward.isDefEq.respectTransparency false in
set_option synthInstance.maxHeartbeats 1000000 in
set_option maxHeartbeats 2000000 in
/-- **The cyclotomic root-of-unity bridge at `p`** (PROVEN 2026-07-25 —
brick (a) of the μ-type/Raynaud coordination flagged in the docstring
of `connected_point_smul_eq_conv_pow_cyclotomicCharacter_of_hopf_package`
below): EVERY element `τ` of the absolute Galois group of `ℚᵖᵥ` moves
a `p ^ k`-th root of unity `z` of `ℚᵖᵥᵃˡᵍ` to `z ^ n`, for any natural
`n` congruent to `χ_cyc(τ̃)` modulo `p ^ k` (`τ̃` the image of `τ` in
`Γ ℚ`). No inertia hypothesis is needed: this is the defining property
of the cyclotomic character, transported along the chosen embedding of
algebraic closures.

Proof (mimicking the endgame of the PROVEN 2-adic
`cyclotomicCharacter_eq_one_of_mem_inertia_two` above): the `p ^ k`-th
roots of unity of `ℚᵖᵥᵃˡᵍ` all come from `AlgebraicClosure ℚ` — a
primitive `p ^ k`-th root of unity `ζ` exists downstairs
(`HasEnoughRootsOfUnity.exists_primitiveRoot`), its image stays
primitive (`IsPrimitiveRoot.map_of_injective`), and in a domain every
`p ^ k`-th root of unity is a power of a primitive one
(`IsPrimitiveRoot.eq_pow_of_pow_eq_one`), so `z = ι (ζ ^ j)`.
Downstairs `cyclotomicCharacter.spec` evaluates the action of `τ̃` as
the `p ^ k`-truncation `PadicInt.toZModPow k` of `χ_cyc(τ̃)`, whose
kernel is exactly `p ^ k ℤ_p` (`PadicInt.ker_toZModPow`), so the
exponent may be replaced by `n`; and the commuting square
`Field.absoluteGaloisGroup.lift_map` transports the identity along
`ι = AlgebraicClosure.map (algebraMap ℚ ℚᵖᵥ)`. -/
theorem absoluteGalois_apply_eq_pow_of_cyclotomicCharacter_sub_mem
    (τ : Field.absoluteGaloisGroup ℚᵖᵥ) (k n : ℕ) (c : ℤ_[p])
    (hc : c = ((cyclotomicCharacter (AlgebraicClosure ℚ) p
      ((Field.absoluteGaloisGroup.map (algebraMap ℚ ℚᵖᵥ)
        τ).toRingEquiv) : ℤ_[p]ˣ) : ℤ_[p]))
    (hn : c - (n : ℤ_[p]) ∈ Ideal.span {(p : ℤ_[p]) ^ k})
    (z : ℚᵖᵥᵃˡᵍ) (hz : z ^ (p ^ k) = 1) :
    τ z = z ^ n := by
  classical
  haveI : NeZero (p ^ k) := ⟨pow_ne_zero k hp.out.ne_zero⟩
  -- the `p ^ k`-th roots of unity of `ℚᵖᵥᵃˡᵍ` come from `AlgebraicClosure ℚ`
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot
    (AlgebraicClosure ℚ) (p ^ k)
  have hζ' : IsPrimitiveRoot
      (AlgebraicClosure.map (algebraMap ℚ ℚᵖᵥ) ζ) (p ^ k) :=
    hζ.map_of_injective (AlgebraicClosure.map (algebraMap ℚ ℚᵖᵥ)).injective
  obtain ⟨j, -, hjz⟩ := hζ'.eq_pow_of_pow_eq_one hz
  have hwz : AlgebraicClosure.map (algebraMap ℚ ℚᵖᵥ) (ζ ^ j) = z := by
    rw [map_pow, hjz]
  have hwpow : (ζ ^ j) ^ (p ^ k) = 1 := by
    rw [← pow_mul, mul_comm j (p ^ k), pow_mul, hζ.pow_eq_one, one_pow]
  -- the cyclotomic character reads the action downstairs
  have hspec : (Field.absoluteGaloisGroup.map (algebraMap ℚ ℚᵖᵥ)
      τ).toRingEquiv (ζ ^ j) = (ζ ^ j) ^ (PadicInt.toZModPow k c).val := by
    rw [hc]
    exact cyclotomicCharacter.spec p _ _ hwpow
  -- the truncation of `χ_cyc(τ̃)` agrees with `n` modulo `p ^ k`
  have hcv : (((PadicInt.toZModPow k c).val : ℕ) : ZMod (p ^ k)) =
      (n : ZMod (p ^ k)) := by
    rw [ZMod.natCast_val, ZMod.cast_id]
    have h1 := hn
    rw [← PadicInt.ker_toZModPow k, RingHom.mem_ker, map_sub, map_natCast,
      sub_eq_zero] at h1
    exact h1
  -- a `p ^ k`-th root of unity only sees its exponent modulo `p ^ k`
  have hexp : (ζ ^ j) ^ (PadicInt.toZModPow k c).val = (ζ ^ j) ^ n := by
    have hmn : (PadicInt.toZModPow k c).val ≡ n [MOD p ^ k] :=
      (ZMod.natCast_eq_natCast_iff _ _ _).mp hcv
    rcases Nat.le_total (PadicInt.toZModPow k c).val n with hle | hle
    · obtain ⟨d, hd⟩ := (Nat.modEq_iff_dvd' hle).mp hmn
      have hn' : n = (PadicInt.toZModPow k c).val + p ^ k * d := by
        rw [← hd]
        exact (Nat.add_sub_cancel' hle).symm
      rw [hn', pow_add, pow_mul, hwpow, one_pow, mul_one]
    · obtain ⟨d, hd⟩ := (Nat.modEq_iff_dvd' hle).mp hmn.symm
      have hq' : (PadicInt.toZModPow k c).val = n + p ^ k * d := by
        rw [← hd]
        exact (Nat.add_sub_cancel' hle).symm
      rw [hq', pow_add, pow_mul, hwpow, one_pow, mul_one]
  -- transport the downstairs identity along the embedding
  have hup := Field.absoluteGaloisGroup.lift_map (algebraMap ℚ ℚᵖᵥ) τ (ζ ^ j)
  rw [hwz, show (Field.absoluteGaloisGroup.map (algebraMap ℚ ℚᵖᵥ) τ) (ζ ^ j) =
      (Field.absoluteGaloisGroup.map (algebraMap ℚ ℚᵖᵥ) τ).toRingEquiv (ζ ^ j)
      from rfl, hspec, hexp, map_pow, hwz] at hup
  exact hup.symm

/-- **The `L₀`-linear extension of a geometric point of a base-changed
generic fibre** (PROVEN machinery, 2026-07-25): a `K₀`-point
`ψ : K₀ ⊗[R₀] H₀ →ₐ[K₀] L₀` of the generic fibre of an `R₀`-bialgebra
`H₀` restricts along `includeRight` to the `R₀`-point
`ψ ∘ (1 ⊗ ·) : H₀ →ₐ[R₀] L₀`, which extends uniquely to an
`L₀`-ALGEBRA map on the `L₀`-base change `L₀ ⊗[R₀] H₀` (both steps are
the tensor–hom adjunction `AlgHom.liftEquiv`). This is the map written
`ψ ↦ ψ̃` in the μ-type bookkeeping below: it is where the
`L₀`-rational group-like coordinates of the connected corner get
evaluated, and it is INJECTIVE (a composition of two equivalences),
which is what turns "the group-likes separate `ψ̃`" into "they separate
`ψ`". -/
noncomputable def extendPoint {R₀ : Type*} [CommRing R₀] {K₀ L₀ : Type u}
    [Field K₀] [Field L₀] [Algebra K₀ L₀] [Algebra R₀ K₀] [Algebra R₀ L₀]
    [IsScalarTower R₀ K₀ L₀] {H₀ : Type*} [CommRing H₀] [Bialgebra R₀ H₀]
    (ψ : K₀ ⊗[R₀] H₀ →ₐ[K₀] L₀) : L₀ ⊗[R₀] H₀ →ₐ[L₀] L₀ :=
  AlgHom.liftEquiv R₀ L₀ H₀ L₀ ((AlgHom.liftEquiv R₀ K₀ H₀ L₀).symm ψ)

set_option synthInstance.maxHeartbeats 1000000 in
set_option maxHeartbeats 1000000 in
/-- **A convolution product evaluates by the ordinary product on a
relative group-like** (PROVEN 2026-07-25 — the two-factor companion of
the shared brick `convPow_apply_of_comul_absorbs` above, stated
generically over any commutative base ring): if `χ₁, χ₂` are points of
a bialgebra `G₀` taking the value `1` on `e` — CONNECTED points for the
counit idempotent `e` — then on any `x` that is GROUP-LIKE relative to
the corner of `e` (`Δx · (e ⊗ e) = x ⊗ x`) the convolution product
evaluates as the ordinary product of the values:
`(χ₁ ⋆ χ₂)(x) = χ₁ x · χ₂ x`.

Proof: `(χ₁ ⋆ χ₂)(x) = lift χ₁ χ₂ (Δx)` (`AlgHom.convMul_apply`) may be
multiplied by `lift χ₁ χ₂ (e ⊗ e) = χ₁ e · χ₂ e = 1`, so it equals
`lift χ₁ χ₂ (Δx · (e ⊗ e)) = lift χ₁ χ₂ (x ⊗ x) = χ₁ x · χ₂ x`. Note
that no hypothesis on `Δe` is needed: the connectedness of `χ₁, χ₂`
alone supplies the value `1` of the pair on `e ⊗ e`. -/
theorem convMul_apply_of_comul_absorbs {R₀ G₀ C₀ : Type*} [CommRing R₀]
    [CommRing G₀] [Bialgebra R₀ G₀] [CommRing C₀] [Algebra R₀ C₀]
    (e : G₀) (χ₁ χ₂ : G₀ →ₐ[R₀] C₀) (h₁ : χ₁ e = 1) (h₂ : χ₂ e = 1)
    (x : G₀)
    (hx : Coalgebra.comul (R := R₀) x * (e ⊗ₜ[R₀] e) = x ⊗ₜ[R₀] x) :
    (toConv χ₁ * toConv χ₂).ofConv x = χ₁ x * χ₂ x := by
  have hone : Algebra.TensorProduct.lift χ₁ χ₂ (fun _ _ => Commute.all _ _)
      (e ⊗ₜ[R₀] e) = 1 := by
    rw [Algebra.TensorProduct.lift_tmul, h₁, h₂, one_mul]
  have hval : (toConv χ₁ * toConv χ₂).ofConv x =
      Algebra.TensorProduct.lift χ₁ χ₂ (fun _ _ => Commute.all _ _)
        (Coalgebra.comul (R := R₀) x) :=
    AlgHom.convMul_apply (toConv χ₁) (toConv χ₂) x
  rw [hval]
  calc Algebra.TensorProduct.lift χ₁ χ₂ (fun _ _ => Commute.all _ _)
        (Coalgebra.comul (R := R₀) x)
      = Algebra.TensorProduct.lift χ₁ χ₂ (fun _ _ => Commute.all _ _)
          (Coalgebra.comul (R := R₀) x) *
        Algebra.TensorProduct.lift χ₁ χ₂ (fun _ _ => Commute.all _ _)
          (e ⊗ₜ[R₀] e) := by rw [hone, mul_one]
    _ = Algebra.TensorProduct.lift χ₁ χ₂ (fun _ _ => Commute.all _ _)
          (Coalgebra.comul (R := R₀) x * (e ⊗ₜ[R₀] e)) := (map_mul _ _ _).symm
    _ = Algebra.TensorProduct.lift χ₁ χ₂ (fun _ _ => Commute.all _ _)
          (x ⊗ₜ[R₀] x) := by rw [hx]
    _ = χ₁ x * χ₂ x := Algebra.TensorProduct.lift_tmul _ _ _ _ _

set_option synthInstance.maxHeartbeats 1000000 in
set_option maxHeartbeats 1000000 in
/-- **Semilinearity of the base-changed lift** (PROVEN 2026-07-25): an
`R₀`-algebra endomorphism `s` of `L₀` moves the `L₀`-linear lift of an
`R₀`-point `χ` of `H₀` to the lift of `s ∘ χ`, at the `s`-twisted
argument: `s (χ̃ t) = (s ∘ χ)~ ((s ⊗ id) t)`. Proof: both sides are
additive in `t`, and on `c ⊗ y` both are `s c · s (χ y)`.

This is the transport that carries the Galois action on POINTS to the
semilinear action on the base-changed Hopf algebra, and hence the exact
reason why the unramifiedness clause of the μ-type package below is
stated as `σ`-INVARIANCE OF THE GROUP-LIKES `(σ ⊗ id) x = x` rather
than as `ℚᵖᵥ`-rationality: `σ ∘ ψ̃` is only semilinear, so `θ (σ • ψ)`
and `σ (θ ψ)` agree exactly when `σ` fixes the coordinate `x`. -/
theorem apply_liftEquiv_eq_liftEquiv_map {R₀ : Type*} [CommRing R₀]
    {L₀ : Type*} [CommRing L₀] [Algebra R₀ L₀]
    {H₀ : Type*} [CommRing H₀] [Algebra R₀ H₀]
    (s : L₀ →ₐ[R₀] L₀) (χ : H₀ →ₐ[R₀] L₀) (t : L₀ ⊗[R₀] H₀) :
    s (AlgHom.liftEquiv R₀ L₀ H₀ L₀ χ t) =
      AlgHom.liftEquiv R₀ L₀ H₀ L₀ (s.comp χ)
        (Algebra.TensorProduct.map s (AlgHom.id R₀ H₀) t) := by
  induction t using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero, map_zero, map_zero]
  | add a b ha hb => rw [map_add, map_add, ha, hb, map_add, map_add]
  | tmul c y =>
    rw [Algebra.TensorProduct.map_tmul, AlgHom.liftEquiv_tmul,
      AlgHom.liftEquiv_tmul, smul_eq_mul, smul_eq_mul, map_mul]
    rfl

set_option synthInstance.maxHeartbeats 1000000 in
set_option maxHeartbeats 1000000 in
/-- **The `μ`-coordinate system attached to a group-like family**
(PROVEN 2026-07-25, generically over any base — this is the FORMAL half
of the μ-type/Raynaud node, split off the citation): suppose the
connected corner of `e₀` in the base change `L₀ ⊗[R₀] H₀` to a big
field `L₀` is the GROUP ALGEBRA of a family `x : ι → L₀ ⊗[R₀] H₀` of
elements that are

* *counit-normalised*: `ε (x i) = 1`;
* *group-like relative to the corner*:
  `Δ (x i) · (ē₀ ⊗ ē₀) = x i ⊗ x i`, where `ē₀ = 1 ⊗ e₀`;
* *generating the corner*: `y · ē₀ ∈ L₀[x]` for every `y` (this is what
  "the corner is the group algebra of the character group" says: the
  group-likes span it, so they generate it as an algebra);
* *fixed by a given automorphism `s` of `L₀`*:
  `(s ⊗ id) (x i) = x i`.

Then the EVALUATION coordinates `θ ψ i := ψ̃ (x i)` (`extendPoint`) on
the `K₀`-points of the generic fibre satisfy the five clauses of the
μ-coordinate package: `θ 1 = 1`, root-of-unity values on points of
finite convolution order, convolution-multiplicativity, separation of
connected points, and `s`-equivariance.

Proof, clause by clause. (1) The convolution unit is `algebraMap ∘ ε`
(`AlgHom.convOne_apply`), and both `liftEquiv` transports preserve it
(`vendored_one_eq_convOne`, `liftEquiv_symm_convOne`,
`liftEquiv_convOne`), so `θ 1 i = ε (x i) = 1`. (3) Both transports
preserve the convolution product (`vendored_mul_eq_convMul`,
`liftEquiv_symm_convMul`, `liftEquiv_convMul`), and the extension of a
connected point is connected (`ψ̃ ē₀ = ψ (1 ⊗ e₀) = 1`), so
`convMul_apply_of_comul_absorbs` at the group-like `x i` gives
multiplicativity. (2) With (1) and (3), `θ (ψ ^ m) i = (θ ψ i) ^ m` by
induction on `m` — the induction needs the connectedness of the
convolution powers, which is the hypothesis `hcp` (supplied at `p` by
the PROVEN `convPow_apply_one_of_comul_absorbs_p`) — so `ψ ^ m = 1`
forces `(θ ψ i) ^ m = θ 1 i = 1`. (4) The set where `ψ̃₁` and `ψ̃₂`
agree is a subalgebra (`AlgHom.equalizer`) containing every `x i`,
hence contains `L₀[x]` (`Algebra.adjoin_le`) and so every `y · ē₀`; for
CONNECTED points that gives `ψ̃₁ y = ψ̃₂ y` for all `y`, and `ψ ↦ ψ̃` is
injective. (5) `apply_liftEquiv_eq_liftEquiv_map` plus the
`s`-invariance of `x i` and `liftEquiv_symm_comp`. -/
theorem exists_grouplike_coordinates_of_grouplike_family
    {R₀ : Type*} [CommRing R₀] {K₀ L₀ : Type u} [Field K₀] [Field L₀]
    [Algebra K₀ L₀] [Algebra R₀ K₀] [Algebra R₀ L₀] [IsScalarTower R₀ K₀ L₀]
    {H₀ : Type*} [CommRing H₀] [Bialgebra R₀ H₀]
    (e₀ : H₀)
    (hcp : ∀ (m : ℕ) (ψ : K₀ ⊗[R₀] H₀ →ₐ[K₀] L₀),
      ψ ((1 : K₀) ⊗ₜ[R₀] e₀) = 1 → (ψ ^ m) ((1 : K₀) ⊗ₜ[R₀] e₀) = 1)
    (s : L₀ ≃ₐ[K₀] L₀)
    {ι : Type*} (x : ι → L₀ ⊗[R₀] H₀)
    (hcount : ∀ i, Coalgebra.counit (R := L₀) (x i) = (1 : L₀))
    (hgl : ∀ i, Coalgebra.comul (R := L₀) (x i) *
        (((1 : L₀) ⊗ₜ[R₀] e₀) ⊗ₜ[L₀] ((1 : L₀) ⊗ₜ[R₀] e₀)) =
      x i ⊗ₜ[L₀] x i)
    (hgen : ∀ y : L₀ ⊗[R₀] H₀,
      y * ((1 : L₀) ⊗ₜ[R₀] e₀) ∈ Algebra.adjoin L₀ (Set.range x))
    (hinv : ∀ i, Algebra.TensorProduct.map (s.toAlgHom.restrictScalars R₀)
      (AlgHom.id R₀ H₀) (x i) = x i) :
    ∃ θ : (K₀ ⊗[R₀] H₀ →ₐ[K₀] L₀) → ι → L₀,
      (∀ i, θ (1 : K₀ ⊗[R₀] H₀ →ₐ[K₀] L₀) i = 1) ∧
      (∀ (m : ℕ) (ψ : K₀ ⊗[R₀] H₀ →ₐ[K₀] L₀),
        ψ ((1 : K₀) ⊗ₜ[R₀] e₀) = 1 → ψ ^ m = 1 → ∀ i, (θ ψ i) ^ m = 1) ∧
      (∀ ψ₁ ψ₂ : K₀ ⊗[R₀] H₀ →ₐ[K₀] L₀,
        ψ₁ ((1 : K₀) ⊗ₜ[R₀] e₀) = 1 → ψ₂ ((1 : K₀) ⊗ₜ[R₀] e₀) = 1 →
        ∀ i, θ (ψ₁ * ψ₂) i = θ ψ₁ i * θ ψ₂ i) ∧
      (∀ ψ₁ ψ₂ : K₀ ⊗[R₀] H₀ →ₐ[K₀] L₀,
        ψ₁ ((1 : K₀) ⊗ₜ[R₀] e₀) = 1 → ψ₂ ((1 : K₀) ⊗ₜ[R₀] e₀) = 1 →
        (∀ i, θ ψ₁ i = θ ψ₂ i) → ψ₁ = ψ₂) ∧
      (∀ ψ : K₀ ⊗[R₀] H₀ →ₐ[K₀] L₀, ψ ((1 : K₀) ⊗ₜ[R₀] e₀) = 1 →
        ∀ i, θ (s.toAlgHom.comp ψ) i = s (θ ψ i)) := by
  classical
  -- the extension of a CONNECTED point stays connected
  have hconn : ∀ ψ : K₀ ⊗[R₀] H₀ →ₐ[K₀] L₀, ψ ((1 : K₀) ⊗ₜ[R₀] e₀) = 1 →
      extendPoint ψ ((1 : L₀) ⊗ₜ[R₀] e₀) = 1 := by
    intro ψ hψ
    rw [extendPoint, AlgHom.liftEquiv_tmul, one_smul]
    exact hψ
  -- clause 1: the coordinates of the convolution unit are `1`
  have hone : ∀ i, extendPoint (1 : K₀ ⊗[R₀] H₀ →ₐ[K₀] L₀) (x i) = 1 := by
    intro i
    have h1 : (AlgHom.liftEquiv R₀ K₀ H₀ L₀).symm
        (1 : K₀ ⊗[R₀] H₀ →ₐ[K₀] L₀) = (1 : WithConv (H₀ →ₐ[R₀] L₀)).ofConv := by
      rw [vendored_one_eq_convOne, liftEquiv_symm_convOne]
    rw [extendPoint, h1, liftEquiv_convOne]
    show algebraMap L₀ L₀ (Coalgebra.counit (R := L₀) (x i)) = 1
    rw [hcount i, map_one]
  -- clause 3: the coordinates are convolution-multiplicative
  have hmul : ∀ ψ₁ ψ₂ : K₀ ⊗[R₀] H₀ →ₐ[K₀] L₀,
      ψ₁ ((1 : K₀) ⊗ₜ[R₀] e₀) = 1 → ψ₂ ((1 : K₀) ⊗ₜ[R₀] e₀) = 1 →
      ∀ i, extendPoint (ψ₁ * ψ₂) (x i) =
        extendPoint ψ₁ (x i) * extendPoint ψ₂ (x i) := by
    intro ψ₁ ψ₂ h₁ h₂ i
    have hSm : (AlgHom.liftEquiv R₀ K₀ H₀ L₀).symm (ψ₁ * ψ₂) =
        (toConv ((AlgHom.liftEquiv R₀ K₀ H₀ L₀).symm ψ₁) *
          toConv ((AlgHom.liftEquiv R₀ K₀ H₀ L₀).symm ψ₂)).ofConv := by
      rw [vendored_mul_eq_convMul, liftEquiv_symm_convMul,
        WithConv.ofConv_toConv, WithConv.ofConv_toConv]
    rw [extendPoint, hSm, liftEquiv_convMul]
    exact convMul_apply_of_comul_absorbs ((1 : L₀) ⊗ₜ[R₀] e₀) _ _
      (hconn ψ₁ h₁) (hconn ψ₂ h₂) (x i) (hgl i)
  refine ⟨fun ψ i => extendPoint ψ (x i), hone, ?_, hmul, ?_, ?_⟩
  · -- clause 2: the coordinates of a point of order `m` are `m`-th roots of `1`
    intro m ψ hψ hord i
    have hpow : ∀ j : ℕ, extendPoint (ψ ^ j) (x i) =
        (extendPoint ψ (x i)) ^ j := by
      intro j
      induction j with
      | zero => rw [pow_zero, pow_zero, hone i]
      | succ n ih => rw [pow_succ, hmul (ψ ^ n) ψ (hcp n ψ hψ) hψ i, ih, pow_succ]
    rw [← hpow m, hord, hone i]
  · -- clause 4: connected points are separated by the coordinates
    intro ψ₁ ψ₂ h₁ h₂ hagree
    have hle : Algebra.adjoin L₀ (Set.range x) ≤
        AlgHom.equalizer (extendPoint ψ₁) (extendPoint ψ₂) := by
      apply Algebra.adjoin_le
      rintro y ⟨i, rfl⟩
      exact (AlgHom.mem_equalizer _ _ _).mpr (hagree i)
    have hall : ∀ y : L₀ ⊗[R₀] H₀, extendPoint ψ₁ y = extendPoint ψ₂ y := by
      intro y
      have hy := (AlgHom.mem_equalizer _ _ _).mp (hle (hgen y))
      rw [map_mul, map_mul, hconn ψ₁ h₁, hconn ψ₂ h₂, mul_one, mul_one] at hy
      exact hy
    have hTeq : extendPoint ψ₁ = extendPoint ψ₂ := AlgHom.ext hall
    rw [extendPoint, extendPoint] at hTeq
    exact (AlgHom.liftEquiv R₀ K₀ H₀ L₀).symm.injective
      ((AlgHom.liftEquiv R₀ L₀ H₀ L₀).injective hTeq)
  · -- clause 5: the coordinates are equivariant for the fixed automorphism
    intro ψ _ i
    show extendPoint (s.toAlgHom.comp ψ) (x i) = s (extendPoint ψ (x i))
    have h1 := apply_liftEquiv_eq_liftEquiv_map (s.toAlgHom.restrictScalars R₀)
      ((AlgHom.liftEquiv R₀ K₀ H₀ L₀).symm ψ) (x i)
    rw [hinv i] at h1
    have h2 : (AlgHom.liftEquiv R₀ K₀ H₀ L₀).symm (s.toAlgHom.comp ψ) =
        (s.toAlgHom.restrictScalars R₀).comp
          ((AlgHom.liftEquiv R₀ K₀ H₀ L₀).symm ψ) :=
      liftEquiv_symm_comp _ _
    have h3 : extendPoint (s.toAlgHom.comp ψ) (x i) =
        AlgHom.liftEquiv R₀ L₀ H₀ L₀ ((s.toAlgHom.restrictScalars R₀).comp
          ((AlgHom.liftEquiv R₀ K₀ H₀ L₀).symm ψ)) (x i) := by
      rw [extendPoint, h2]
    rw [h3, ← h1]
    rfl

set_option backward.isDefEq.respectTransparency false in
set_option synthInstance.maxHeartbeats 1000000 in
set_option maxHeartbeats 2000000 in
/-- **The connected component of a hardly-ramified Hopf package is of
multiplicative type: over `ℚᵖᵥᵃˡᵍ` its corner is the group algebra of
an inertia-fixed character group** (SORRY NODE — the SHARPENED citation
of the μ-type/Raynaud classification, isolated 2026-07-25 from the
coordinate package `exists_grouplike_coordinates_of_connected_hopf_package`
below, whose five clauses are now PROVEN over this one).

Content. `G` is a finite flat Hopf order over `𝒪ᵖᵥ` with étale generic
fibre, arising through the `Γ`-equivariant bijection `fG` from a
hardly-ramified `ρ` whose local Jordan–Hölder factors are
ONE-dimensional (the `hchar` input), and `e₀` is a connected counit
idempotent, so that `Spec (G·e₀)` is the identity component `G°`. The
claim is that `G°` is of MULTIPLICATIVE TYPE, in the concrete form that
its base change to the algebraic closure is a group algebra: there is a
family `x : ι → ℚᵖᵥᵃˡᵍ ⊗[𝒪ᵖᵥ] G` of elements of the corner of
`ē₀ = 1 ⊗ e₀` which are

* counit-normalised, `ε (x i) = 1`;
* GROUP-LIKE relative to the corner,
  `Δ (x i) · (ē₀ ⊗ ē₀) = x i ⊗ x i`;
* GENERATING the corner, `y · ē₀ ∈ ℚᵖᵥᵃˡᵍ[x]` for every `y` — i.e. the
  group-likes span `ℚᵖᵥᵃˡᵍ ⊗ (G·e₀)`, which is exactly the statement
  that this corner is the group algebra `ℚᵖᵥᵃˡᵍ[X]` of the character
  group `X = Hom(G°, 𝔾ₘ)` (the intended witness is `ι = X` with `x` its
  inclusion, `x` at the identity of `X` being `ē₀` itself);
* FIXED by the given inertia element, `(σ ⊗ id) (x i) = x i` — the
  unramifiedness of `X`.

Intended proof (Raynaud, *Schémas en groupes de type `(p, …, p)`*,
Bull. SMF 102 (1974) 241–280; Oort–Tate, *Group schemes of prime
order*, Ann. Sci. ÉNS 3 (1970) 1–21; Tate, *Finite flat group
schemes*, in Cornell–Silverman–Stevens, §4; Serre, Duke 54 (1987)
§4.1):

1. `e = v(p) = 1 < p − 1` for `𝒪ᵖᵥ` at the odd prime `p` (`hpodd`), so
   Raynaud's rigidity applies: the finite flat prolongation of the
   étale generic fibre is UNIQUE (Raynaud Th. 3.3.3, Cor. 3.3.6) and,
   after passage to the strict henselisation, `G` has a composition
   series whose quotients are `F`-vector-space schemes for finite
   fields `F` (Raynaud Cor. 3.3.7, dévissage of a group of type
   `(p, …, p)`; Tate–CSS §4.3).
2. Each such quotient is classified by the equations
   `Xᵢ^p = δᵢ X_{i+1}` with `0 ≤ v(δᵢ) ≤ e` (Raynaud §1.4, Th. 1.4.1;
   Tate–CSS Th. 4.4.1), and inertia acts on its geometric points
   through the fundamental characters of level `r = [F : 𝔽ₚ]`
   (Raynaud Th. 3.4.1, Cor. 3.4.4). The `hchar`/`fG` input forces every
   local Jordan–Hölder factor to be ONE-dimensional, i.e. `r = 1`, so
   only the level-one branch occurs: with `e = 1` each factor has
   `v(δ) ∈ {0, 1}`, hence is étale (`v(δ) = 0`) or of `μ`-type
   (`v(δ) = 1 = e`; Oort–Tate at order `p`).
3. The connected factors are therefore all of `μ`-type, and `G°` — an
   iterated extension of `μ`-type groups over the henselian `𝒪ᵖᵥ` — is
   itself of multiplicative type (dually: its Cartier dual is an
   extension of étale by étale, hence étale; Raynaud Prop. 3.3.2 2°
   and its dual, Tate–CSS §2 on Cartier duality).
4. A multiplicative-type `G° = D(X)` has coordinate ring the group
   algebra of its character group `X`, and `X` is ÉTALE over `𝒪ᵖᵥ` —
   constant over the strict henselisation — so its Galois action is
   UNRAMIFIED and the inertia element `σ` fixes every element of `X`,
   i.e. every group-like of the corner.

SOUNDNESS (do NOT weaken; two deliberate features).

(i) The one-dimensionality input `hchar`/`fG` is not redundant: for the
`p`-torsion of a SUPERSINGULAR elliptic curve over `ℤ_p` (connected,
killed by `p`, `e = 1`) the generic fibre is a simple `F`-vector-space
scheme with `F = 𝔽_{p²}` and tame inertia acts through `𝔽_{p²}^×`
(Raynaud Th. 3.4.1 at `r = 2`, and the worked example in Raynaud
§3.4.7), which is not a power map — the corner is then NOT a group
algebra of an inertia-fixed group, and the consumer's power-conclusion
is FALSE. Step 2 is exactly where the input is spent.

(ii) The unramifiedness clause is `σ`-INVARIANCE of the group-likes
inside `ℚᵖᵥᵃˡᵍ ⊗[𝒪ᵖᵥ] G`, and deliberately NOT `ℚᵖᵥ`-rationality of
the group-likes: the character group `X` may be a nonconstant
UNRAMIFIED TWIST, in which case no nontrivial group-like of the corner
is `ℚᵖᵥ`-rational and the rational-generators formulation would be a
FALSE leaf. Semilinearity (`apply_liftEquiv_eq_liftEquiv_map` above) is
what makes the invariance clause the RIGHT one: it is exactly what
`θ (σ • ψ) = σ (θ ψ)` needs. -/
theorem exists_grouplike_family_of_connected_hopf_package
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
      (Polynomial.X - Polynomial.C (χ₁ g)) * (Polynomial.X - Polynomial.C (χ₂ g)))
    (I : Ideal R) (hI : IsOpen (I : Set R))
    (G : Type) [CommRing G]
    [HopfAlgebra 𝒪ᵖᵥ G] [Module.Flat 𝒪ᵖᵥ G] [Module.Finite 𝒪ᵖᵥ G]
    [Algebra.Etale ℚᵖᵥ (ℚᵖᵥ ⊗[𝒪ᵖᵥ] G)]
    (fG : Additive (ℚᵖᵥ ⊗[𝒪ᵖᵥ] G →ₐ[ℚᵖᵥ] ℚᵖᵥᵃˡᵍ) →+[Field.absoluteGaloisGroup ℚᵖᵥ]
      (((ρ.baseChange (R ⧸ I)).toLocal
        hp.out.toHeightOneSpectrumRingOfIntegersRat).Space))
    (hfG : Function.Bijective fG)
    (e₀ : G) (he₀ : IsIdempotentElem e₀)
    (hε₀ : Coalgebra.counit (R := 𝒪ᵖᵥ) e₀ = (1 : 𝒪ᵖᵥ))
    (hprim₀ : ∀ x : G, IsIdempotentElem x → x * e₀ = 0 ∨ x * e₀ = e₀)
    (hcomul₀ : Coalgebra.comul (R := 𝒪ᵖᵥ) e₀ * (e₀ ⊗ₜ[𝒪ᵖᵥ] e₀) =
      e₀ ⊗ₜ[𝒪ᵖᵥ] e₀)
    (σ : Field.absoluteGaloisGroup ℚᵖᵥ)
    (hσ : σ ∈ localInertiaGroup hp.out.toHeightOneSpectrumRingOfIntegersRat) :
    ∃ (ι : Type) (x : ι → ℚᵖᵥᵃˡᵍ ⊗[𝒪ᵖᵥ] G),
      (∀ i, Coalgebra.counit (R := ℚᵖᵥᵃˡᵍ) (x i) = (1 : ℚᵖᵥᵃˡᵍ)) ∧
      (∀ i, Coalgebra.comul (R := ℚᵖᵥᵃˡᵍ) (x i) *
          (((1 : ℚᵖᵥᵃˡᵍ) ⊗ₜ[𝒪ᵖᵥ] e₀) ⊗ₜ[ℚᵖᵥᵃˡᵍ] ((1 : ℚᵖᵥᵃˡᵍ) ⊗ₜ[𝒪ᵖᵥ] e₀)) =
        x i ⊗ₜ[ℚᵖᵥᵃˡᵍ] x i) ∧
      (∀ y : ℚᵖᵥᵃˡᵍ ⊗[𝒪ᵖᵥ] G, y * ((1 : ℚᵖᵥᵃˡᵍ) ⊗ₜ[𝒪ᵖᵥ] e₀) ∈
        Algebra.adjoin ℚᵖᵥᵃˡᵍ (Set.range x)) ∧
      (∀ i, Algebra.TensorProduct.map (σ.toAlgHom.restrictScalars 𝒪ᵖᵥ)
        (AlgHom.id 𝒪ᵖᵥ G) (x i) = x i) :=
  sorry

set_option backward.isDefEq.respectTransparency false in
set_option synthInstance.maxHeartbeats 1000000 in
set_option maxHeartbeats 2000000 in
/-- **The connected component of a hardly-ramified Hopf package is of
multiplicative type: its points have unramified `μ`-coordinates**
(PROVEN 2026-07-25 over the SHARPENED citation
`exists_grouplike_family_of_connected_hopf_package` above — brick (c) of
the μ-type/Raynaud coordination; the classification input is Raynaud
1974, *Schémas en groupes de type `(p, …, p)`*, Bull. SMF 102, §1.4 +
Prop. 3.3.2 + Th. 3.4.1/Cor. 3.4.4 + Cor. 3.3.7, with Oort–Tate 1970 at
order `p`, Tate's chapter in Cornell–Silverman–Stevens §4 and Serre,
Duke 1987, §4.1): the
connected component `Spec (G·e₀)` of the finite flat Hopf order `G` at
`p`, for a hardly-ramified `ρ` whose local Jordan–Hölder factors are
ONE-dimensional (the `hchar`/`fG` input), is of multiplicative type
and killed by `p ^ k`; equivalently, its geometric points admit a
system of `μ_{p ^ k}`-valued COORDINATES `θ` on which the local
inertia at `p` acts through the cyclotomic character alone.

PROOF (2026-07-25): the coordinates are EVALUATION at the group-like
generators of the corner, `θ ψ i = ψ̃ (x i)` for the `ℚᵖᵥᵃˡᵍ`-linear
extension `ψ̃ = extendPoint ψ`, and all five clauses are formal
consequences of the four cited properties of the group-like family
supplied by `exists_grouplike_family_of_connected_hopf_package` — see
`exists_grouplike_coordinates_of_grouplike_family` above, which does
the whole derivation generically. In particular the root-of-unity
clause needs NO exponent hypothesis on the group-likes: it follows from
`θ (ψ ^ m) i = (θ ψ i) ^ m` (convolution-multiplicativity plus the
PROVEN connectedness of convolution powers,
`convPow_apply_one_of_comul_absorbs_p`) applied to the point's own
order `ψ ^ (p ^ k) = 1`; and the equivariance clause is where the
`σ`-invariance of the group-likes is spent, semilinearity of the
extension (`apply_liftEquiv_eq_liftEquiv_map`) being what makes the
two sides differ by exactly `(σ ⊗ id) (x i)` vs `x i`.

SOUNDNESS (inherited from the consumer, do NOT weaken): the
one-dimensionality input `hchar`/`fG` is not redundant — for the
`p`-torsion of a SUPERSINGULAR elliptic curve over `ℤ_p` (connected,
killed by `p`, `e = 1`) tame inertia acts through `𝔽_{p²}^×`, which is
not a power map, so no such coordinate system exists there and the
consumer's power-conclusion is FALSE without the exclusion. That is
also why the unramifiedness clause is stated for the SPECIFIC inertia
element `σ` rather than as `ℚᵖᵥ`-rationality of the `x i`: the
character group `X` may be a nonconstant unramified twist, in which
case NO nontrivial group-like of the corner is `ℚᵖᵥ`-rational, while
inertia still fixes all of them.

FAITHFULNESS AUDIT (2026-07-25, `𝒪ᵥ`-rationality sweep — VERDICT
FAITHFUL; this note exists so the statement is not "simplified" into
the shape that was already found FALSE once). The leaf survives the
counterexample that killed the first form of
`OortTate.exists_muType_coordinate`: by Oort–Tate the connected
order-`p` group schemes over `ℤ_p` (`p` odd, `e = 1 < p − 1`) are the
`p − 1` UNRAMIFIED twists `μ_p ⊗ ψ`, `ψ : G_{ℚ_p} → (ℤ/p)^×` of order
dividing `p − 1`, and for `ψ ≠ 1` the `μ_p`-coordinate exists only
over `𝒪^nr`, not over `𝒪ᵥ`. Three features keep this statement on the
right side of that line, and NONE of them may be dropped:
* `θ` is a FUNCTION ON POINTS valued in the algebraically closed
  `ℚᵖᵥᵃˡᵍ`, not a tuple of elements of `G`; the group-likes `x i` of
  the intended proof live in `ℚᵖᵥᵃˡᵍ ⊗[𝒪ᵥ] (G·e₀)` and never appear
  in the statement, so no `𝒪ᵥ`- or `ℚᵖᵥ`-rational datum is demanded;
* `ι` and `θ` are EXISTENTIALLY quantified with no tie to `G` beyond
  clauses 1–5, so a proof is free to make the unramified base change,
  build the coordinates over `𝒪^nr`/`ℚᵖᵥᵃˡᵍ`, and descend only their
  VALUES — which is exactly what the twist permits;
* clause 5 is quantified over the ONE given inertia element `σ`, and
  is an equivariance of values (`θ (σ • ψ) i = σ (θ ψ i)`), which holds
  because inertia fixes `𝒪^nr` pointwise. Strengthening it to
  `ℚᵖᵥ`-rationality of the `x i`, or to all of `Γ ℚᵖᵥ`, makes it FALSE
  for every `ψ ≠ 1` (Frobenius moves the group-likes by `ψ`).
The general rule the sweep confirmed: over `𝒪ᵥ`, IDENTITIES and VALUES
descend from `𝒪^nr` (flatness/torsion-freeness, and inertia fixing
`𝒪^nr`), while EXISTENCE of a coordinate or a normal form does not.

Consumed by
`connected_point_smul_eq_conv_pow_cyclotomicCharacter_of_hopf_package`
below, together with the two PROVEN bricks
`absoluteGalois_apply_eq_pow_of_cyclotomicCharacter_sub_mem` (a) and
`convPow_apply_of_comul_absorbs` (b); proven here over the single
remaining sorried citation
`exists_grouplike_family_of_connected_hopf_package` (c). -/
theorem exists_grouplike_coordinates_of_connected_hopf_package
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
      (Polynomial.X - Polynomial.C (χ₁ g)) * (Polynomial.X - Polynomial.C (χ₂ g)))
    (I : Ideal R) (hI : IsOpen (I : Set R))
    (G : Type) [CommRing G]
    [HopfAlgebra 𝒪ᵖᵥ G] [Module.Flat 𝒪ᵖᵥ G] [Module.Finite 𝒪ᵖᵥ G]
    [Algebra.Etale ℚᵖᵥ (ℚᵖᵥ ⊗[𝒪ᵖᵥ] G)]
    (fG : Additive (ℚᵖᵥ ⊗[𝒪ᵖᵥ] G →ₐ[ℚᵖᵥ] ℚᵖᵥᵃˡᵍ) →+[Field.absoluteGaloisGroup ℚᵖᵥ]
      (((ρ.baseChange (R ⧸ I)).toLocal
        hp.out.toHeightOneSpectrumRingOfIntegersRat).Space))
    (hfG : Function.Bijective fG)
    (e₀ : G) (he₀ : IsIdempotentElem e₀)
    (hε₀ : Coalgebra.counit (R := 𝒪ᵖᵥ) e₀ = (1 : 𝒪ᵖᵥ))
    (hprim₀ : ∀ x : G, IsIdempotentElem x → x * e₀ = 0 ∨ x * e₀ = e₀)
    (hcomul₀ : Coalgebra.comul (R := 𝒪ᵖᵥ) e₀ * (e₀ ⊗ₜ[𝒪ᵖᵥ] e₀) =
      e₀ ⊗ₜ[𝒪ᵖᵥ] e₀)
    (k : ℕ)
    (σ : Field.absoluteGaloisGroup ℚᵖᵥ)
    (hσ : σ ∈ localInertiaGroup hp.out.toHeightOneSpectrumRingOfIntegersRat) :
    ∃ (ι : Type) (θ : (ℚᵖᵥ ⊗[𝒪ᵖᵥ] G →ₐ[ℚᵖᵥ] ℚᵖᵥᵃˡᵍ) → ι → ℚᵖᵥᵃˡᵍ),
      (∀ i, θ (1 : ℚᵖᵥ ⊗[𝒪ᵖᵥ] G →ₐ[ℚᵖᵥ] ℚᵖᵥᵃˡᵍ) i = 1) ∧
      (∀ ψ : ℚᵖᵥ ⊗[𝒪ᵖᵥ] G →ₐ[ℚᵖᵥ] ℚᵖᵥᵃˡᵍ,
        ψ ((1 : ℚᵖᵥ) ⊗ₜ[𝒪ᵖᵥ] e₀) = 1 → ψ ^ (p ^ k) = 1 →
        ∀ i, (θ ψ i) ^ (p ^ k) = 1) ∧
      (∀ ψ₁ ψ₂ : ℚᵖᵥ ⊗[𝒪ᵖᵥ] G →ₐ[ℚᵖᵥ] ℚᵖᵥᵃˡᵍ,
        ψ₁ ((1 : ℚᵖᵥ) ⊗ₜ[𝒪ᵖᵥ] e₀) = 1 → ψ₂ ((1 : ℚᵖᵥ) ⊗ₜ[𝒪ᵖᵥ] e₀) = 1 →
        ∀ i, θ (ψ₁ * ψ₂) i = θ ψ₁ i * θ ψ₂ i) ∧
      (∀ ψ₁ ψ₂ : ℚᵖᵥ ⊗[𝒪ᵖᵥ] G →ₐ[ℚᵖᵥ] ℚᵖᵥᵃˡᵍ,
        ψ₁ ((1 : ℚᵖᵥ) ⊗ₜ[𝒪ᵖᵥ] e₀) = 1 → ψ₂ ((1 : ℚᵖᵥ) ⊗ₜ[𝒪ᵖᵥ] e₀) = 1 →
        (∀ i, θ ψ₁ i = θ ψ₂ i) → ψ₁ = ψ₂) ∧
      (∀ ψ : ℚᵖᵥ ⊗[𝒪ᵖᵥ] G →ₐ[ℚᵖᵥ] ℚᵖᵥᵃˡᵍ, ψ ((1 : ℚᵖᵥ) ⊗ₜ[𝒪ᵖᵥ] e₀) = 1 →
        ∀ i, θ (σ • ψ) i = σ (θ ψ i)) := by
  classical
  -- the CITED input: over `ℚᵖᵥᵃˡᵍ` the connected corner is the group
  -- algebra of an inertia-fixed character group
  obtain ⟨ι, x, hcount, hgl, hgen, hinv⟩ :=
    exists_grouplike_family_of_connected_hopf_package hpodd hv hZinj hRinj hρ
      χ₁ χ₂ hcont₁ hcont₂ hone₁ hone₂ hmul₁ hmul₂ hchar I hI G fG hfG e₀ he₀
      hε₀ hprim₀ hcomul₀ σ hσ
  -- the FORMAL half: evaluation at the group-likes is a `μ`-coordinate system
  obtain ⟨θ, h1, h2, h3, h4, h5⟩ :=
    exists_grouplike_coordinates_of_grouplike_family (K₀ := ℚᵖᵥ)
      (L₀ := ℚᵖᵥᵃˡᵍ) e₀
      (fun m ψ hψ => convPow_apply_one_of_comul_absorbs_p G e₀ hε₀ hcomul₀ ψ hψ m)
      σ x hcount hgl hgen hinv
  refine ⟨ι, θ, h1, fun ψ hψe hord i => h2 (p ^ k) ψ hψe hord i, h3, h4,
    fun ψ hψe i => ?_⟩
  have hsmul : σ • ψ = σ.toAlgHom.comp ψ := AlgHom.ext fun _ => rfl
  rw [hsmul]
  exact h5 ψ hψe i

set_option backward.isDefEq.respectTransparency false in
set_option synthInstance.maxHeartbeats 1000000 in
set_option maxHeartbeats 2000000 in
/-- **Inertia raises connected points to the exact cyclotomic
convolution power at `p`** (PROVEN 2026-07-25 as an assembly over the
single sorried Raynaud-classification sub-leaf
`exists_grouplike_coordinates_of_connected_hopf_package` above, whose
`μ`-coordinate system is combined with the two PROVEN bricks
`absoluteGalois_apply_eq_pow_of_cyclotomicCharacter_sub_mem` (the
root-of-unity bridge, step 4) and `convPow_apply_of_comul_absorbs` (the
group-like convolution evaluation, step 5, applied through
`convPow_apply_one_of_comul_absorbs_p`); isolated 2026-07-24 — THE
μ-type/Raynaud core, split off the transport assembly
`connected_point_smul_eq_cyclotomicCharacter_smul_of_hopf_package`
below, stated INTRINSICALLY on the convolution point group: no `u`,
no scalar action, no ideal bookkeeping): a geometric point `φ` of
the generic fibre of the finite flat Hopf order `G`, lying in the
CONNECTED component (value `1` on the connected counit idempotent
`e₀`) and of convolution order dividing `p ^ k`, is moved by a local
inertia element `σ` at `p` to its `n`-th convolution power, for ANY
`n : ℕ` congruent to `χ_cyc(σ̃)` modulo `p ^ k`.

Intended proof (Raynaud 1974, *Schémas en groupes de type
`(p, …, p)`*, Bull. SMF 102, 3.3.6; Oort–Tate 1970 at order `p`;
Serre, Duke 1987, §4.1; Tate, "Finite flat group schemes", in
Cornell–Silverman–Stevens):

1. *level-two exclusion (uses `hchar`/`fG`)*: the trace of
   `ρ ⊗ ℚ̄_p` on the decomposition group at `p` is the sum of the
   two continuous multiplicative characters `χ₁ + χ₂`, and `fG`
   identifies the point group of `G` with the congruence module of
   `ρ`, so every Jordan–Hölder factor of the local Galois module of
   points is ONE-dimensional — the supersingular
   (fundamental-characters-of-level-2) branch of Raynaud's
   classification cannot occur. NB the exclusion input is NOT
   redundant: for the `p`-torsion of a supersingular elliptic curve
   over `ℤ_p` (connected, killed by `p`, `e = 1`) tame inertia acts
   through `𝔽_{p²}^×`, which is NOT a power map, so the bare
   statement without `hchar`-type input is FALSE — any consumer
   sharing this node must supply a one-dimensionality input;
2. *multiplicative type at `e = 1 < p − 1`*: each connected
   one-dimensional factor is of `μ`-type (Raynaud 3.3.6/Oort–Tate),
   and the connected component `Spec (G·e₀)` is itself of
   multiplicative type: its Cartier dual is filtered by étale
   factors, and an extension of étale by étale over the henselian
   `ℤ_p` is étale;
3. *character-group triviality on inertia*: the `ℚᵖᵥᵃˡᵍ`-Hopf
   algebra `ℚᵖᵥᵃˡᵍ ⊗[𝒪ᵖᵥ] (G·e₀)` is then the group algebra of the
   étale character group `X` — it is GENERATED by group-like
   elements `x` (`Δx = x ⊗ x`, `ε x = 1`) with RING power
   `x ^ (p ^ k) = 1` (the ring product of group-likes is the group
   law of `X`, and `G·e₀` is killed by `p ^ k` through `hord`) — and
   `X` carries the UNRAMIFIED Galois action of the étale dual, so
   the inertia element `σ` fixes every group-like;
4. *the cyclotomic root-of-unity bridge (shared, PROVABLE
   machinery)*: every value `φ(x)` on a group-like is a `p ^ k`-th
   root of unity (`φ(x) ^ (p ^ k) = φ(x ^ (p ^ k)) = 1`), and EVERY
   `τ ∈ Γ ℚᵖᵥ` moves every `z` with `z ^ (p ^ k) = 1` to
   `z ^ m`, `m ≡ χ_cyc(τ̃) mod p ^ k`: the `p ^ k`-th roots of unity
   of `ℚᵖᵥᵃˡᵍ` all come from `AlgebraicClosure ℚ` (root counting on
   `X ^ (p ^ k) − 1`), where `modularCyclotomicCharacter.unique`
   plus `Field.absoluteGaloisGroup.lift_map` read the action off
   `cyclotomicCharacter.toZModPow` — follow the PROVEN 2-adic
   pattern in `cyclotomicCharacter_eq_one_of_mem_inertia_two` above
   (its `hfix2`/`modularCyclotomicCharacter.unique` endgame);
5. *evaluation*: on a group-like `x` fixed by `σ`, using
   `AlgHom.convMul_apply` and `Δx = x ⊗ x`,
   `(σ • φ) x = σ (φ x) = (φ x) ^ n = (φ ^ n) x`; two points of the
   corner agreeing on the group-like generators and on `e₀` agree
   everywhere (`hφe` and `convMul_apply_one_of_comul_absorbs` handle
   the idempotent corner splitting), giving `σ • φ = φ ^ n`.

COORDINATION (2026-07-24): this is the Family avatar of the shared
Oort–Tate/μ-type node flagged in `Modularity/Interface.lean`'s E1b-i
(`residual_triangular_sub_character_inertia_dichotomy_of_flat`) and
sibling of ModThree's `inertiaFixed_connected_point_eq_one_at_three`.
The three consumers CANNOT share this exact statement (it carries the
`hchar` exclusion, which ModThree's statement lacks — and by the
step-1 counterexample some exclusion is unavoidable for the
power-conclusion; ModThree's fixed-point-triviality conclusion is
instead true unconditionally, via no-inertia-fixed-points in the
level-2 branch). What IS shared and should be built ONCE, generically
(a `GroupScheme`-level file importable by ModThree, Interface and
Family): (a) the step-4 root-of-unity bridge, (b) the step-5
group-like convolution evaluation, (c) the step-2/3 Raynaud
classification with the one-dimensionality input as an explicit
hypothesis.

STATUS (2026-07-25, second pass): (a) and (b) are PROVEN, generically,
as `absoluteGalois_apply_eq_pow_of_cyclotomicCharacter_sub_mem` and
`convPow_apply_of_comul_absorbs` above — both are stated over abstract
data and are ready to move verbatim into a shared `GroupScheme` file
when ModThree and Interface are cut over; so are the three further
generic bricks `convMul_apply_of_comul_absorbs`,
`apply_liftEquiv_eq_liftEquiv_map` and
`exists_grouplike_coordinates_of_grouplike_family` (with the definition
`extendPoint`), which together turn a group-like family into the whole
μ-coordinate package. (c) has been SHRUNK: the coordinate package
`exists_grouplike_coordinates_of_connected_hopf_package` is now PROVEN,
and the only sorried node left in this cluster is the purely structural
classification statement `exists_grouplike_family_of_connected_hopf_package`
— "over `ℚᵖᵥᵃˡᵍ` the connected corner is the group algebra of an
inertia-fixed character group" — which carries the one-dimensionality
input as explicit hypotheses exactly as coordinated. -/
theorem connected_point_smul_eq_conv_pow_cyclotomicCharacter_of_hopf_package
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
      (Polynomial.X - Polynomial.C (χ₁ g)) * (Polynomial.X - Polynomial.C (χ₂ g)))
    (I : Ideal R) (hI : IsOpen (I : Set R))
    (G : Type) [CommRing G]
    [HopfAlgebra 𝒪ᵖᵥ G] [Module.Flat 𝒪ᵖᵥ G] [Module.Finite 𝒪ᵖᵥ G]
    [Algebra.Etale ℚᵖᵥ (ℚᵖᵥ ⊗[𝒪ᵖᵥ] G)]
    (fG : Additive (ℚᵖᵥ ⊗[𝒪ᵖᵥ] G →ₐ[ℚᵖᵥ] ℚᵖᵥᵃˡᵍ) →+[Field.absoluteGaloisGroup ℚᵖᵥ]
      (((ρ.baseChange (R ⧸ I)).toLocal
        hp.out.toHeightOneSpectrumRingOfIntegersRat).Space))
    (hfG : Function.Bijective fG)
    (e₀ : G) (he₀ : IsIdempotentElem e₀)
    (hε₀ : Coalgebra.counit (R := 𝒪ᵖᵥ) e₀ = (1 : 𝒪ᵖᵥ))
    (hprim₀ : ∀ x : G, IsIdempotentElem x → x * e₀ = 0 ∨ x * e₀ = e₀)
    (hcomul₀ : Coalgebra.comul (R := 𝒪ᵖᵥ) e₀ * (e₀ ⊗ₜ[𝒪ᵖᵥ] e₀) =
      e₀ ⊗ₜ[𝒪ᵖᵥ] e₀)
    (φ : ℚᵖᵥ ⊗[𝒪ᵖᵥ] G →ₐ[ℚᵖᵥ] ℚᵖᵥᵃˡᵍ)
    (hφe : φ ((1 : ℚᵖᵥ) ⊗ₜ[𝒪ᵖᵥ] e₀) = 1)
    (k : ℕ) (hord : φ ^ (p ^ k) = 1)
    (σ : Field.absoluteGaloisGroup ℚᵖᵥ)
    (hσ : σ ∈ localInertiaGroup hp.out.toHeightOneSpectrumRingOfIntegersRat)
    (n : ℕ)
    (hn : ((cyclotomicCharacter (AlgebraicClosure ℚ) p
        ((Field.absoluteGaloisGroup.map (algebraMap ℚ ℚᵖᵥ)
          σ).toRingEquiv) : ℤ_[p]ˣ) : ℤ_[p]) - (n : ℤ_[p]) ∈
      Ideal.span {(p : ℤ_[p]) ^ k}) :
    σ • φ = φ ^ n := by
  classical
  -- brick (c): the μ-type coordinate system on the connected component
  obtain ⟨ι, θ, hθ1, hθroot, hθmul, hθsep, hθσ⟩ :=
    exists_grouplike_coordinates_of_connected_hopf_package hpodd hv hZinj hRinj
      hρ χ₁ χ₂ hcont₁ hcont₂ hone₁ hone₂ hmul₁ hmul₂ hchar I hI G fG hfG e₀ he₀
      hε₀ hprim₀ hcomul₀ k σ hσ
  -- brick (b): the convolution powers of a connected point stay connected
  have hconn : ∀ m : ℕ, (φ ^ m) ((1 : ℚᵖᵥ) ⊗ₜ[𝒪ᵖᵥ] e₀) = 1 := fun m =>
    convPow_apply_one_of_comul_absorbs_p G e₀ hε₀ hcomul₀ φ hφe m
  -- so is the inertia translate of `φ`: `σ` fixes the value `1`
  have hσconn : (σ • φ) ((1 : ℚᵖᵥ) ⊗ₜ[𝒪ᵖᵥ] e₀) = 1 := by
    have h1 : (σ • φ) ((1 : ℚᵖᵥ) ⊗ₜ[𝒪ᵖᵥ] e₀) =
        σ (φ ((1 : ℚᵖᵥ) ⊗ₜ[𝒪ᵖᵥ] e₀)) := rfl
    rw [h1, hφe, map_one]
  -- the coordinates of a convolution power are ordinary powers
  have hθpow : ∀ (m : ℕ) (i : ι), θ (φ ^ m) i = (θ φ i) ^ m := by
    intro m
    induction m with
    | zero =>
      intro i
      rw [pow_zero, pow_zero, hθ1 i]
    | succ j ih =>
      intro i
      rw [pow_succ, hθmul (φ ^ j) φ (hconn j) hφe i, ih i, pow_succ]
  -- the coordinates of `φ` are `p ^ k`-th roots of unity
  have hroot : ∀ i, (θ φ i) ^ (p ^ k) = 1 := hθroot φ hφe hord
  -- brick (a): on those, `σ` acts as the `n`-th power; conclude by separation
  refine hθsep (σ • φ) (φ ^ n) hσconn (hconn n) fun i => ?_
  rw [hθσ φ hφe i, hθpow n i]
  exact absoluteGalois_apply_eq_pow_of_cyclotomicCharacter_sub_mem σ k n _ rfl hn
    (θ φ i) (hroot i)

set_option backward.isDefEq.respectTransparency false in
set_option synthInstance.maxHeartbeats 1000000 in
set_option maxHeartbeats 2000000 in
/-- **Inertia moves connected points by the exact cyclotomic scalar
at `p`** (PROVEN 2026-07-24 as a transport assembly over the single
sorried μ-type/Raynaud leaf
`connected_point_smul_eq_conv_pow_cyclotomicCharacter_of_hopf_package`
above — the finite-exponent bookkeeping is proven here): a geometric
point `φ` of the generic fibre of the finite flat Hopf order `G` —
whose points are `Γ`-equivariantly identified by `fG` with the
congruence space of `ρ` at the open ideal `I` — lying in the
CONNECTED component (value `1` on a connected counit idempotent
`e₀`) is moved by a local inertia element `σ` at `p` to its
`χ_cyc(σ̃) mod I` scalar multiple.

Assembly: the open ideal `I` absorbs `p ^ k` for some `k`
(continuity of `algebraMap ℤ_[p] R` for the module topology), so the
congruence module — hence, through the additive bijection `fG`, the
convolution point group — is `p ^ k`-torsion, giving
`φ ^ (p ^ k) = 1`; `n` is chosen as the `ZMod (p ^ k)`-value of
`χ_cyc(σ̃)` (`PadicInt.toZModPow`, whose kernel is exactly
`p ^ k ℤ_p` — `PadicInt.ker_toZModPow`); the leaf gives
`σ • φ = φ ^ n`, and transporting along `fG`,
`ρ̄(σ̃)(fG φ) = fG (φ ^ n) = n • fG φ = (n : R ⧸ I) • fG φ =
(χ_cyc(σ̃) mod I) • fG φ` — the intrinsic `ℤ`-action agreeing with
the `R ⧸ I`-scalar action through `Nat.cast_smul_eq_nsmul`, and
`n − χ_cyc(σ̃) ∈ p ^ k ℤ_p` mapping into `I`. -/
theorem connected_point_smul_eq_cyclotomicCharacter_smul_of_hopf_package
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
      (Polynomial.X - Polynomial.C (χ₁ g)) * (Polynomial.X - Polynomial.C (χ₂ g)))
    (I : Ideal R) (hI : IsOpen (I : Set R))
    (G : Type) [CommRing G]
    [HopfAlgebra 𝒪ᵖᵥ G] [Module.Flat 𝒪ᵖᵥ G] [Module.Finite 𝒪ᵖᵥ G]
    [Algebra.Etale ℚᵖᵥ (ℚᵖᵥ ⊗[𝒪ᵖᵥ] G)]
    (fG : Additive (ℚᵖᵥ ⊗[𝒪ᵖᵥ] G →ₐ[ℚᵖᵥ] ℚᵖᵥᵃˡᵍ) →+[Field.absoluteGaloisGroup ℚᵖᵥ]
      (((ρ.baseChange (R ⧸ I)).toLocal
        hp.out.toHeightOneSpectrumRingOfIntegersRat).Space))
    (hfG : Function.Bijective fG)
    (e₀ : G) (he₀ : IsIdempotentElem e₀)
    (hε₀ : Coalgebra.counit (R := 𝒪ᵖᵥ) e₀ = (1 : 𝒪ᵖᵥ))
    (hprim₀ : ∀ x : G, IsIdempotentElem x → x * e₀ = 0 ∨ x * e₀ = e₀)
    (hcomul₀ : Coalgebra.comul (R := 𝒪ᵖᵥ) e₀ * (e₀ ⊗ₜ[𝒪ᵖᵥ] e₀) =
      e₀ ⊗ₜ[𝒪ᵖᵥ] e₀)
    (φ : ℚᵖᵥ ⊗[𝒪ᵖᵥ] G →ₐ[ℚᵖᵥ] ℚᵖᵥᵃˡᵍ)
    (hφe : φ ((1 : ℚᵖᵥ) ⊗ₜ[𝒪ᵖᵥ] e₀) = 1)
    (u : (R ⧸ I) ⊗[R] V)
    (hφu : fG (Additive.ofMul φ) = u)
    (σ : Field.absoluteGaloisGroup ℚᵖᵥ)
    (hσ : σ ∈ localInertiaGroup hp.out.toHeightOneSpectrumRingOfIntegersRat) :
    (ρ.baseChange (R ⧸ I)) (Field.absoluteGaloisGroup.map
        (algebraMap ℚ ℚᵖᵥ) σ) u =
      (algebraMap R (R ⧸ I) (algebraMap ℤ_[p] R
        ((cyclotomicCharacter (AlgebraicClosure ℚ) p
          ((Field.absoluteGaloisGroup.map (algebraMap ℚ ℚᵖᵥ)
            σ).toRingEquiv) : ℤ_[p]ˣ) : ℤ_[p]))) • u := by
  classical
  set c : ℤ_[p] := ((cyclotomicCharacter (AlgebraicClosure ℚ) p
    ((Field.absoluteGaloisGroup.map (algebraMap ℚ ℚᵖᵥ)
      σ).toRingEquiv) : ℤ_[p]ˣ) : ℤ_[p])
  -- the congruence level: the open ideal `I` absorbs a power of `p`
  obtain ⟨k, hk⟩ : ∃ k : ℕ, algebraMap ℤ_[p] R ((p : ℤ_[p]) ^ k) ∈ I := by
    have hcont : Continuous (algebraMap ℤ_[p] R) :=
      IsModuleTopology.continuous_of_linearMap (Algebra.linearMap ℤ_[p] R)
    have htend : Filter.Tendsto (fun n : ℕ => (p : ℤ_[p]) ^ n)
        Filter.atTop (nhds 0) := by
      apply tendsto_pow_atTop_nhds_zero_of_norm_lt_one
      rw [PadicInt.norm_p]
      exact inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.out.one_lt)
    have htend2 : Filter.Tendsto
        (fun n : ℕ => algebraMap ℤ_[p] R ((p : ℤ_[p]) ^ n))
        Filter.atTop (nhds (algebraMap ℤ_[p] R 0)) :=
      (hcont.tendsto 0).comp htend
    rw [map_zero] at htend2
    exact (htend2.eventually_mem (hI.mem_nhds I.zero_mem)).exists
  haveI : NeZero (p ^ k) := ⟨pow_ne_zero k hp.out.ne_zero⟩
  -- the natural representative of `χ_cyc(σ̃)` modulo `p ^ k`
  obtain ⟨n, hn⟩ : ∃ n : ℕ, c - (n : ℤ_[p]) ∈
      Ideal.span {(p : ℤ_[p]) ^ k} := by
    refine ⟨(PadicInt.toZModPow k c).val, ?_⟩
    rw [← PadicInt.ker_toZModPow k, RingHom.mem_ker, map_sub, map_natCast,
      ZMod.natCast_val, ZMod.cast_id, sub_self]
  -- the image of `p ^ k` dies in `R ⧸ I`
  have hpkq : algebraMap R (R ⧸ I)
      (algebraMap ℤ_[p] R ((p : ℤ_[p]) ^ k)) = 0 := by
    rw [Ideal.Quotient.algebraMap_eq]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hk
  -- the congruence module is `p ^ k`-torsion
  have hpkS : ((p ^ k : ℕ) : R ⧸ I) = 0 := by
    have h1 := hpkq
    rw [show ((p : ℤ_[p]) ^ k) = ((p ^ k : ℕ) : ℤ_[p]) by norm_cast] at h1
    rwa [map_natCast, map_natCast] at h1
  have hpku : (p ^ k) • u = 0 := by
    have h1 : ((p ^ k : ℕ) : R ⧸ I) • u = (p ^ k) • u :=
      Nat.cast_smul_eq_nsmul (R ⧸ I) (p ^ k) u
    rw [hpkS, zero_smul] at h1
    exact h1.symm
  -- hence, through `fG`, the point `φ` has convolution order
  -- dividing `p ^ k`
  have hord : φ ^ (p ^ k) = 1 := by
    have h0 : fG ((p ^ k) • Additive.ofMul φ) =
        fG (0 : Additive (ℚᵖᵥ ⊗[𝒪ᵖᵥ] G →ₐ[ℚᵖᵥ] ℚᵖᵥᵃˡᵍ)) := by
      rw [map_nsmul fG (p ^ k) (Additive.ofMul φ), map_zero, hφu, hpku]
    have h1 := hfG.injective h0
    have h2 := congrArg Additive.toMul h1
    rwa [toMul_nsmul, toMul_ofMul, toMul_zero] at h2
  -- the μ-type/Raynaud leaf: inertia raises `φ` to the `n`-th
  -- convolution power
  have hsmul : σ • φ = φ ^ n :=
    connected_point_smul_eq_conv_pow_cyclotomicCharacter_of_hopf_package
      hpodd hv hZinj hRinj hρ χ₁ χ₂ hcont₁ hcont₂ hone₁ hone₂ hmul₁ hmul₂
      hchar I hI G fG hfG e₀ he₀ hε₀ hprim₀ hcomul₀ φ hφe k hord σ hσ n hn
  -- the two spellings of the local action agree: ring homs out of `ℚ`
  -- are unique
  have hbridge : ((ρ.baseChange (R ⧸ I)).toLocal
      hp.out.toHeightOneSpectrumRingOfIntegersRat) σ u =
      (ρ.baseChange (R ⧸ I)) (Field.absoluteGaloisGroup.map
        (algebraMap ℚ ℚᵖᵥ) σ) u := by
    rw [GaloisRep.toLocal_apply]
    exact congrArg (fun (h : ℚ →+* ℚᵖᵥ) =>
      (ρ.baseChange (R ⧸ I)) (Field.absoluteGaloisGroup.map h σ) u)
      (Subsingleton.elim _ _)
  -- transport `σ • φ = φ ^ n` along the equivariant bijection `fG`
  have htrans : (ρ.baseChange (R ⧸ I)) (Field.absoluteGaloisGroup.map
      (algebraMap ℚ ℚᵖᵥ) σ) u = n • u := by
    have h3 : fG (σ • Additive.ofMul φ) = fG (n • Additive.ofMul φ) := by
      rw [show σ • Additive.ofMul φ = Additive.ofMul (σ • φ) from rfl, hsmul,
        ← ofMul_pow]
    rw [map_smul fG σ (Additive.ofMul φ),
      map_nsmul fG n (Additive.ofMul φ), hφu] at h3
    rw [← hbridge]
    exact h3
  -- the finite-exponent congruence: `n ≡ χ_cyc(σ̃) mod I`
  have hscal : ((n : ℕ) : R ⧸ I) =
      algebraMap R (R ⧸ I) (algebraMap ℤ_[p] R c) := by
    obtain ⟨d, hd⟩ := Ideal.mem_span_singleton.mp hn
    have h1 : algebraMap R (R ⧸ I)
        (algebraMap ℤ_[p] R (c - (n : ℤ_[p]))) = 0 := by
      rw [hd, map_mul, map_mul, hpkq, zero_mul]
    rw [map_sub, map_sub, map_natCast, map_natCast, sub_eq_zero] at h1
    exact h1.symm
  rw [htrans, ← Nat.cast_smul_eq_nsmul (R ⧸ I) n u, hscal]

set_option backward.isDefEq.respectTransparency false in
set_option synthInstance.maxHeartbeats 1000000 in
set_option maxHeartbeats 4000000 in
/-- **The connected–étale cyclotomic subgroup of a Hopf package at
`p`** (PROVEN assembly, DECOMPOSED 2026-07-24 along the (i)/(ii)
split over the single sorried μ-type/Raynaud leaf
`connected_point_smul_eq_cyclotomicCharacter_smul_of_hopf_package`
above — the subgroup construction, part (i), and all
convolution/points plumbing are proven here, mirroring the PROVEN
ModThree assembly `exists_connectedEtale_subgroup_of_hopf_package`
with the char-3 negation step replaced by a finite-exponent
argument): given the explicit finite flat Hopf package for the
congruence quotient `ρ.baseChange (R ⧸ I)` at `p`, the congruence
space carries an additive subgroup `U` — the image under `fG` of the
geometric points of the connected component `G⁰ ⊆ Spec G`, i.e. the
vectors whose point takes the value `1` on the connected counit
idempotent `e₀` of the PROVEN generic package
`Bialgebra.exists_connected_counit_idempotent` — such that for every
`σ` in the local inertia at `p`:

* (i) every inertia displacement `ρ̄(σ̃)m − m` lies in `U` (PROVEN
  here): the displacement point is the convolution quotient
  `(σ∘χ) ⋆ χ⁻¹` of the point `χ` of `m`, its value on `e₀` is an
  idempotent of the field `ℚᵖᵥᵃˡᵍ` congruent to `1` modulo the
  maximal ideal of the integral closure
  (`lift_sub_lift_mem_of_localInertiaGroup_p` — inertia moves
  integral values only within `𝔪`), hence exactly `1`;
* (ii) `σ̃` acts on `U` by the EXACT cyclotomic scalar
  `χ_cyc(σ̃) mod I` — the sorried μ-type/Raynaud leaf above, applied
  to the point of `u`.

`U` is closed under addition because the comultiplication of `e₀`
absorbs `e₀ ⊗ e₀` (`convMul_apply_one_of_comul_absorbs`), contains
`0` (the counit point), and is closed under negation because the
congruence module is `p ^ k`-torsion for any `k` with
`algebraMap ℤ_[p] R (p ^ k) ∈ I` — such `k` exists since `I` is OPEN
and `algebraMap ℤ_[p] R` is continuous for the module topology — so
`-u = (p ^ k − 1) • u` is a repeated sum. -/
theorem exists_connectedEtale_cyclotomic_subgroup_of_hopf_package
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
      (Polynomial.X - Polynomial.C (χ₁ g)) * (Polynomial.X - Polynomial.C (χ₂ g)))
    (I : Ideal R) (hI : IsOpen (I : Set R))
    (G : Type) [CommRing G]
    [HopfAlgebra (HeightOneSpectrum.adicCompletionIntegers ℚ
      hp.out.toHeightOneSpectrumRingOfIntegersRat) G]
    [Module.Flat (HeightOneSpectrum.adicCompletionIntegers ℚ
      hp.out.toHeightOneSpectrumRingOfIntegersRat) G]
    [Module.Finite (HeightOneSpectrum.adicCompletionIntegers ℚ
      hp.out.toHeightOneSpectrumRingOfIntegersRat) G]
    [Algebra.Etale (HeightOneSpectrum.adicCompletion ℚ
        hp.out.toHeightOneSpectrumRingOfIntegersRat)
      ((HeightOneSpectrum.adicCompletion ℚ
          hp.out.toHeightOneSpectrumRingOfIntegersRat) ⊗[
        HeightOneSpectrum.adicCompletionIntegers ℚ
          hp.out.toHeightOneSpectrumRingOfIntegersRat] G)]
    (fG : Additive ((HeightOneSpectrum.adicCompletion ℚ
          hp.out.toHeightOneSpectrumRingOfIntegersRat) ⊗[
        HeightOneSpectrum.adicCompletionIntegers ℚ
          hp.out.toHeightOneSpectrumRingOfIntegersRat] G →ₐ[
        HeightOneSpectrum.adicCompletion ℚ
          hp.out.toHeightOneSpectrumRingOfIntegersRat]
        AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
          hp.out.toHeightOneSpectrumRingOfIntegersRat)) →+[
        Field.absoluteGaloisGroup (HeightOneSpectrum.adicCompletion ℚ
          hp.out.toHeightOneSpectrumRingOfIntegersRat)]
      (((ρ.baseChange (R ⧸ I)).toLocal
        hp.out.toHeightOneSpectrumRingOfIntegersRat).Space))
    (hfG : Function.Bijective fG) :
    ∃ U : AddSubgroup ((R ⧸ I) ⊗[R] V),
      ∀ σ ∈ localInertiaGroup hp.out.toHeightOneSpectrumRingOfIntegersRat,
        (∀ m : (R ⧸ I) ⊗[R] V,
          (ρ.baseChange (R ⧸ I)) (Field.absoluteGaloisGroup.map
            (algebraMap ℚ (HeightOneSpectrum.adicCompletion ℚ
              hp.out.toHeightOneSpectrumRingOfIntegersRat)) σ) m - m ∈ U) ∧
        (∀ u ∈ U, (ρ.baseChange (R ⧸ I)) (Field.absoluteGaloisGroup.map
            (algebraMap ℚ (HeightOneSpectrum.adicCompletion ℚ
              hp.out.toHeightOneSpectrumRingOfIntegersRat)) σ) u =
          (algebraMap R (R ⧸ I) (algebraMap ℤ_[p] R
            ((cyclotomicCharacter (AlgebraicClosure ℚ) p
              ((Field.absoluteGaloisGroup.map (algebraMap ℚ
                (HeightOneSpectrum.adicCompletion ℚ
                  hp.out.toHeightOneSpectrumRingOfIntegersRat)) σ).toRingEquiv) :
              ℤ_[p]ˣ) : ℤ_[p]))) • u) := by
  classical
  -- the congruence level: the open ideal `I` absorbs a power of `p`
  obtain ⟨k, hk⟩ : ∃ k : ℕ, algebraMap ℤ_[p] R ((p : ℤ_[p]) ^ k) ∈ I := by
    have hcont : Continuous (algebraMap ℤ_[p] R) :=
      IsModuleTopology.continuous_of_linearMap (Algebra.linearMap ℤ_[p] R)
    have htend : Filter.Tendsto (fun n : ℕ => (p : ℤ_[p]) ^ n)
        Filter.atTop (nhds 0) := by
      apply tendsto_pow_atTop_nhds_zero_of_norm_lt_one
      rw [PadicInt.norm_p]
      exact inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.out.one_lt)
    have htend2 : Filter.Tendsto
        (fun n : ℕ => algebraMap ℤ_[p] R ((p : ℤ_[p]) ^ n))
        Filter.atTop (nhds (algebraMap ℤ_[p] R 0)) :=
      (hcont.tendsto 0).comp htend
    rw [map_zero] at htend2
    exact (htend2.eventually_mem (hI.mem_nhds I.zero_mem)).exists
  -- the connected counit idempotent of the Hopf order
  obtain ⟨e₀, he₀, hε₀, hmin₀, habs₀⟩ :=
    Bialgebra.exists_connected_counit_idempotent (A := 𝒪ᵖᵥ) (G := G)
  have hprim₀ : ∀ x : G, IsIdempotentElem x → x * e₀ = 0 ∨ x * e₀ = e₀ :=
    fun x hx => mul_eq_zero_or_mul_eq_of_minimal he₀ hε₀ hmin₀ x hx
  have hcomul₀ : Coalgebra.comul (R := 𝒪ᵖᵥ) e₀ * (e₀ ⊗ₜ[𝒪ᵖᵥ] e₀) =
      e₀ ⊗ₜ[𝒪ᵖᵥ] e₀ := by
    rwa [Bialgebra.comulAlgHom_apply] at habs₀
  -- the points identification as an equivalence
  let g := Equiv.ofBijective fG hfG
  have hfs : ∀ x : (R ⧸ I) ⊗[R] V, fG (g.symm x) = x :=
    fun x => g.apply_symm_apply x
  have hgs_add : ∀ u w : (R ⧸ I) ⊗[R] V,
      g.symm (u + w) = g.symm u + g.symm w := by
    intro u w
    apply g.injective
    show fG (g.symm (u + w)) = fG (g.symm u + g.symm w)
    rw [map_add fG, hfs, hfs, hfs]
  have hgs_zero : g.symm (0 : (R ⧸ I) ⊗[R] V) = 0 := by
    apply g.injective
    show fG (g.symm (0 : (R ⧸ I) ⊗[R] V)) = fG 0
    rw [map_zero fG, hfs]
  -- the congruence module is `p ^ k`-torsion
  have hpkS : ((p ^ k : ℕ) : R ⧸ I) = 0 := by
    have h1 : algebraMap R (R ⧸ I)
        (algebraMap ℤ_[p] R ((p : ℤ_[p]) ^ k)) = 0 := by
      rw [Ideal.Quotient.algebraMap_eq]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr hk
    rw [show ((p : ℤ_[p]) ^ k) = ((p ^ k : ℕ) : ℤ_[p]) by norm_cast] at h1
    rwa [map_natCast, map_natCast] at h1
  have hpkV : ∀ m : (R ⧸ I) ⊗[R] V, (p ^ k) • m = 0 := by
    intro m
    have h1 : ((p ^ k : ℕ) : R ⧸ I) • m = (p ^ k) • m :=
      Nat.cast_smul_eq_nsmul (R ⧸ I) (p ^ k) m
    rw [hpkS, zero_smul] at h1
    exact h1.symm
  -- the two spellings of the local action agree: ring homs out of `ℚ`
  -- are unique, so the `algebraMap` baked into `toLocal` is the one of
  -- the statement
  have hbridge : ∀ (τ : Field.absoluteGaloisGroup ℚᵖᵥ)
      (w : (R ⧸ I) ⊗[R] V),
      ((ρ.baseChange (R ⧸ I)).toLocal
        hp.out.toHeightOneSpectrumRingOfIntegersRat) τ w =
      (ρ.baseChange (R ⧸ I)) (Field.absoluteGaloisGroup.map
        (algebraMap ℚ ℚᵖᵥ) τ) w := by
    intro τ w
    rw [GaloisRep.toLocal_apply]
    exact congrArg (fun (h : ℚ →+* ℚᵖᵥ) =>
      (ρ.baseChange (R ⧸ I)) (Field.absoluteGaloisGroup.map h τ) w)
      (Subsingleton.elim _ _)
  -- the zero point lies in the connected part (the counit point)
  have hP0 : (AlgHom.liftEquiv 𝒪ᵖᵥ ℚᵖᵥ G ℚᵖᵥᵃˡᵍ).symm
      (Additive.toMul (g.symm (0 : (R ⧸ I) ⊗[R] V))) e₀ = 1 := by
    rw [hgs_zero, toMul_zero, vendored_one_eq_convOne,
      liftEquiv_symm_convOne]
    show algebraMap 𝒪ᵖᵥ ℚᵖᵥᵃˡᵍ (Coalgebra.counit (R := 𝒪ᵖᵥ) e₀) = 1
    rw [hε₀, map_one]
  -- the connected-part subgroup: vectors whose point takes the value
  -- `1` on the connected counit idempotent
  refine ⟨{
      carrier := {u : (R ⧸ I) ⊗[R] V |
        (AlgHom.liftEquiv 𝒪ᵖᵥ ℚᵖᵥ G ℚᵖᵥᵃˡᵍ).symm
          (Additive.toMul (g.symm u)) e₀ = 1}
      zero_mem' := ?_
      add_mem' := ?_
      neg_mem' := ?_ }, fun σ hσ => ⟨?_, ?_⟩⟩
  · -- closure under addition: the comultiplication absorbs `e₀ ⊗ e₀`
    intro u w hu hw
    show (AlgHom.liftEquiv 𝒪ᵖᵥ ℚᵖᵥ G ℚᵖᵥᵃˡᵍ).symm
      (Additive.toMul (g.symm (u + w))) e₀ = 1
    rw [hgs_add, toMul_add, vendored_mul_eq_convMul, liftEquiv_symm_convMul]
    exact convMul_apply_one_of_comul_absorbs e₀ hcomul₀ _ _ hu hw
  · -- `0` is the counit point, whose value on `e₀` is `ε(e₀) = 1`
    exact hP0
  · -- closure under negation: the module is `p ^ k`-torsion, so
    -- `-u = (p ^ k - 1) • u`, a repeated sum
    intro u hu
    have hnsmul : ∀ n : ℕ,
        (AlgHom.liftEquiv 𝒪ᵖᵥ ℚᵖᵥ G ℚᵖᵥᵃˡᵍ).symm
          (Additive.toMul (g.symm ((n + 1) • u))) e₀ = 1 := by
      intro n
      induction n with
      | zero =>
        rw [zero_add, one_nsmul]
        exact hu
      | succ m ih =>
        rw [succ_nsmul u (m + 1), hgs_add, toMul_add,
          vendored_mul_eq_convMul, liftEquiv_symm_convMul]
        exact convMul_apply_one_of_comul_absorbs e₀ hcomul₀ _ _ ih hu
    have hneg : -u = (p ^ k - 1) • u := by
      have hsum : (p ^ k - 1) • u + u = 0 := by
        have h2 : (p ^ k - 1) • u + u = (p ^ k - 1 + 1) • u :=
          (succ_nsmul u (p ^ k - 1)).symm
        rw [h2, Nat.sub_add_cancel
          (Nat.one_le_iff_ne_zero.mpr (pow_ne_zero k hp.out.ne_zero))]
        exact hpkV u
      exact neg_eq_of_add_eq_zero_left hsum
    show (AlgHom.liftEquiv 𝒪ᵖᵥ ℚᵖᵥ G ℚᵖᵥᵃˡᵍ).symm
      (Additive.toMul (g.symm (-u))) e₀ = 1
    rcases hcase : p ^ k - 1 with - | m
    · rw [hneg, hcase, zero_nsmul]
      exact hP0
    · rw [hneg, hcase]
      exact hnsmul m
  · -- (i) every inertia displacement lies in the connected part: the
    -- displacement point is `(σ∘χ) ⋆ χ⁻¹`, congruent to `1` modulo the
    -- maximal ideal (inertia moves integral values within `𝔪`), and
    -- its idempotent value on `e₀` is `0` or `1` — so it is `1`
    intro m
    set d : (R ⧸ I) ⊗[R] V := (ρ.baseChange (R ⧸ I))
      (Field.absoluteGaloisGroup.map (algebraMap ℚ ℚᵖᵥ) σ) m - m with hd
    show (AlgHom.liftEquiv 𝒪ᵖᵥ ℚᵖᵥ G ℚᵖᵥᵃˡᵍ).symm
      (Additive.toMul (g.symm d)) e₀ = 1
    set χm : G →ₐ[𝒪ᵖᵥ] ℚᵖᵥᵃˡᵍ := (AlgHom.liftEquiv 𝒪ᵖᵥ ℚᵖᵥ G ℚᵖᵥᵃˡᵍ).symm
      (Additive.toMul (g.symm m)) with hχm
    set δd : G →ₐ[𝒪ᵖᵥ] ℚᵖᵥᵃˡᵍ := (AlgHom.liftEquiv 𝒪ᵖᵥ ℚᵖᵥ G ℚᵖᵥᵃˡᵍ).symm
      (Additive.toMul (g.symm d)) with hδd
    -- the displacement point multiplies the point of `m` into its
    -- inertia translate
    have hXd : g.symm d + g.symm m = σ • g.symm m := by
      apply g.injective
      show fG (g.symm d + g.symm m) = fG (σ • g.symm m)
      rw [map_add fG, map_smul fG, hfs, hfs]
      show d + m = ((ρ.baseChange (R ⧸ I)).toLocal
        hp.out.toHeightOneSpectrumRingOfIntegersRat) σ m
      rw [hbridge, hd, sub_add_cancel]
    have hDφ : Additive.toMul (g.symm d) * Additive.toMul (g.symm m) =
        σ • Additive.toMul (g.symm m) := by
      have h1 := congrArg Additive.toMul hXd
      have h2 : Additive.toMul (σ • g.symm m) =
          σ • Additive.toMul (g.symm m) := rfl
      rw [toMul_add, h2] at h1
      exact h1
    -- transport to the `𝒪ᵖᵥ`-points: `δ ⋆ χ = σ∘χ`
    have h3 := congrArg (AlgHom.liftEquiv 𝒪ᵖᵥ ℚᵖᵥ G ℚᵖᵥᵃˡᵍ).symm hDφ
    rw [vendored_mul_eq_convMul, liftEquiv_symm_convMul] at h3
    rw [show σ • Additive.toMul (g.symm m) =
        (σ.toAlgHom : ℚᵖᵥᵃˡᵍ →ₐ[ℚᵖᵥ] ℚᵖᵥᵃˡᵍ).comp (Additive.toMul (g.symm m))
        from AlgHom.ext fun _ => rfl, liftEquiv_symm_comp] at h3
    rw [← hχm, ← hδd] at h3
    have h4 : toConv δd * toConv χm =
        toConv ((σ.toAlgHom.restrictScalars 𝒪ᵖᵥ).comp χm) := by
      have h4a := congrArg WithConv.toConv h3
      rwa [WithConv.toConv_ofConv] at h4a
    -- cancel `χ` on the right through the antipode inverse
    have h5 : toConv δd =
        toConv ((σ.toAlgHom.restrictScalars 𝒪ᵖᵥ).comp χm) *
          toConv (χm.comp (HopfAlgebra.antipodeAlgHom 𝒪ᵖᵥ G)) := by
      rw [← h4, mul_assoc, toConv_mul_toConv_comp_antipodeAlgHom, mul_one]
    have h6 : δd e₀ =
        Algebra.TensorProduct.lift ((σ.toAlgHom.restrictScalars 𝒪ᵖᵥ).comp χm)
          (χm.comp (HopfAlgebra.antipodeAlgHom 𝒪ᵖᵥ G))
          (fun _ _ => Commute.all _ _) (Coalgebra.comul (R := 𝒪ᵖᵥ) e₀) := by
      have h7 := congrArg WithConv.ofConv h5
      rw [WithConv.ofConv_toConv] at h7
      rw [h7]
      exact AlgHom.convMul_apply _ _ e₀
    -- the corresponding value of `χ ⋆ χ⁻¹ = 1` is `ε(e₀) = 1`
    have h8 : Algebra.TensorProduct.lift χm
        (χm.comp (HopfAlgebra.antipodeAlgHom 𝒪ᵖᵥ G))
        (fun _ _ => Commute.all _ _) (Coalgebra.comul (R := 𝒪ᵖᵥ) e₀) = 1 := by
      have h9 := AlgHom.convMul_apply (toConv χm)
        (toConv (χm.comp (HopfAlgebra.antipodeAlgHom 𝒪ᵖᵥ G))) e₀
      rw [toConv_mul_toConv_comp_antipodeAlgHom] at h9
      rw [← h9]
      show algebraMap 𝒪ᵖᵥ ℚᵖᵥᵃˡᵍ (Coalgebra.counit (R := 𝒪ᵖᵥ) e₀) = 1
      rw [hε₀, map_one]
    -- the inertia congruence: `δ(e₀) ≡ 1` modulo the maximal ideal
    have h10 := lift_sub_lift_mem_of_localInertiaGroup_p G σ hσ χm
      (χm.comp (HopfAlgebra.antipodeAlgHom 𝒪ᵖᵥ G))
      (Coalgebra.comul (R := 𝒪ᵖᵥ) e₀)
    rw [h8, ← h6] at h10
    -- the value is an idempotent of a field, hence `0` or `1`; the
    -- congruence rules out `0`
    have h11 : δd e₀ * δd e₀ = δd e₀ := by
      rw [← map_mul, he₀.eq]
    have h12 : δd e₀ * (δd e₀ - 1) = 0 := by
      rw [mul_sub, h11, mul_one, sub_self]
    rcases mul_eq_zero.mp h12 with h13 | h13
    · exfalso
      rw [h13, zero_sub] at h10
      have h14 : (1 : ℚᵖᵥᵃˡᵍ) ∈
          Submodule.map (Algebra.linearMap (IntegralClosure 𝒪ᵖᵥ ℚᵖᵥᵃˡᵍ) ℚᵖᵥᵃˡᵍ)
            (IsLocalRing.maximalIdeal (IntegralClosure 𝒪ᵖᵥ ℚᵖᵥᵃˡᵍ)) := by
        have h15 := Submodule.neg_mem _ h10
        rwa [neg_neg] at h15
      obtain ⟨m', hm', hm1⟩ := h14
      have hm2 : m' = 1 := by
        apply Subtype.ext
        exact hm1
      rw [hm2] at hm'
      exact (IsLocalRing.maximalIdeal.isMaximal
        (IntegralClosure 𝒪ᵖᵥ ℚᵖᵥᵃˡᵍ)).ne_top
        (Ideal.eq_top_of_isUnit_mem _ hm' isUnit_one)
    · exact sub_eq_zero.mp h13
  · -- (ii) the connected part carries the exact cyclotomic scalar
    -- action: the sorried μ-type leaf, applied to the point of `u`
    intro u hu
    have hφe : Additive.toMul (g.symm u) ((1 : ℚᵖᵥ) ⊗ₜ[𝒪ᵖᵥ] e₀) = 1 := hu
    exact connected_point_smul_eq_cyclotomicCharacter_smul_of_hopf_package
      hpodd hv hZinj hRinj hρ χ₁ χ₂ hcont₁ hcont₂ hone₁ hone₂ hmul₁ hmul₂
      hchar I hI G fG hfG e₀ he₀ hε₀ hprim₀ hcomul₀
      (Additive.toMul (g.symm u)) hφe u (hfs u) σ hσ

/-- **The per-level Raynaud trace congruence at `p`** (PROVEN
assembly, DECOMPOSED 2026-07-24 over the single sorried
connected–étale leaf
`exists_connectedEtale_cyclotomic_subgroup_of_hopf_package` above —
the Raynaud/Fontaine group-scheme content; the Cayley–Hamilton trace
bookkeeping is proven here): given the explicit finite flat Hopf
package for the congruence quotient `ρ.baseChange (R ⧸ I)` at `p`
(the witness packaged by `GaloisRep.HasFlatProlongationAt`, extracted
by the consumer from `hρ.isFlat` at the open ideal `I`), the trace of
`ρ` at (the image in `G_ℚ` of) a local inertia element `σ` at `p` is
congruent to `1 + χ_cyc(σ̃)` modulo `I`. Assembly: write `Ā` for the
action of `σ̃` on the congruence quotient `(R ⧸ I) ⊗[R] V` and `c̄`
for `χ_cyc(σ̃) mod I`. The leaf provides the connected-part subgroup
`U` with (i) every displacement `Ā m − m` in `U` and (ii) `Ā` acting
on `U` by the scalar `c̄`; combining the two, `Ā` satisfies the
quadratic `Ā² = (1 + c̄) • Ā − c̄ • 1` pointwise. Cayley–Hamilton for
`Ā` (`LinearMap.aeval_self_charpoly`) with
`charpoly Ā = X² − t̄·X + d̄` — from rank `2` (`hv`),
`Matrix.charpoly_fin_two` along a reindexed `chooseBasis`, and
`LinearMap.charpoly_baseChange` — gives `Ā² = t̄ • Ā − d̄ • 1` with
`t̄, d̄` the mod-`I` images of the trace and determinant of `ρ(σ̃)`;
the cyclotomic determinant `hρ.det` pins `d̄ = c̄`, so subtracting the
two quadratics leaves `t̄ • Ā m = (1 + c̄) • Ā m` for every `m`. `Ā`
is invertible (`ρ̄` is a monoid hom into the endomorphism monoid), so
evaluating at the `Ā`-preimage of a base-changed basis vector
(`Module.Basis.baseChange`) and reading off its coordinate gives
`t̄ = 1 + c̄` in `R ⧸ I`, i.e. the stated congruence
(`Ideal.Quotient.eq_zero_iff_mem`). -/
theorem trace_sub_one_add_cyclotomicCharacter_mem_of_hopf_package
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
      (Polynomial.X - Polynomial.C (χ₁ g)) * (Polynomial.X - Polynomial.C (χ₂ g)))
    (I : Ideal R) (hI : IsOpen (I : Set R))
    (G : Type) [CommRing G]
    [HopfAlgebra (HeightOneSpectrum.adicCompletionIntegers ℚ
      hp.out.toHeightOneSpectrumRingOfIntegersRat) G]
    [Module.Flat (HeightOneSpectrum.adicCompletionIntegers ℚ
      hp.out.toHeightOneSpectrumRingOfIntegersRat) G]
    [Module.Finite (HeightOneSpectrum.adicCompletionIntegers ℚ
      hp.out.toHeightOneSpectrumRingOfIntegersRat) G]
    [Algebra.Etale (HeightOneSpectrum.adicCompletion ℚ
        hp.out.toHeightOneSpectrumRingOfIntegersRat)
      ((HeightOneSpectrum.adicCompletion ℚ
          hp.out.toHeightOneSpectrumRingOfIntegersRat) ⊗[
        HeightOneSpectrum.adicCompletionIntegers ℚ
          hp.out.toHeightOneSpectrumRingOfIntegersRat] G)]
    (fG : Additive ((HeightOneSpectrum.adicCompletion ℚ
          hp.out.toHeightOneSpectrumRingOfIntegersRat) ⊗[
        HeightOneSpectrum.adicCompletionIntegers ℚ
          hp.out.toHeightOneSpectrumRingOfIntegersRat] G →ₐ[
        HeightOneSpectrum.adicCompletion ℚ
          hp.out.toHeightOneSpectrumRingOfIntegersRat]
        AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
          hp.out.toHeightOneSpectrumRingOfIntegersRat)) →+[
        Field.absoluteGaloisGroup (HeightOneSpectrum.adicCompletion ℚ
          hp.out.toHeightOneSpectrumRingOfIntegersRat)]
      (((ρ.baseChange (R ⧸ I)).toLocal
        hp.out.toHeightOneSpectrumRingOfIntegersRat).Space))
    (hfG : Function.Bijective fG)
    (σ : Field.absoluteGaloisGroup (HeightOneSpectrum.adicCompletion ℚ
      hp.out.toHeightOneSpectrumRingOfIntegersRat))
    (hσ : σ ∈ localInertiaGroup hp.out.toHeightOneSpectrumRingOfIntegersRat) :
    LinearMap.trace R V (ρ (Field.absoluteGaloisGroup.map
        (algebraMap ℚ (HeightOneSpectrum.adicCompletion ℚ
          hp.out.toHeightOneSpectrumRingOfIntegersRat)) σ)) -
      (1 + algebraMap ℤ_[p] R
        ((cyclotomicCharacter (AlgebraicClosure ℚ) p
          ((Field.absoluteGaloisGroup.map (algebraMap ℚ (HeightOneSpectrum.adicCompletion ℚ
            hp.out.toHeightOneSpectrumRingOfIntegersRat)) σ).toRingEquiv) : ℤ_[p]ˣ) :
          ℤ_[p])) ∈ I := by
  classical
  -- the connected–étale leaf: displacement subgroup with exact
  -- cyclotomic scalar action, specialized at `σ`
  obtain ⟨U, hU⟩ := exists_connectedEtale_cyclotomic_subgroup_of_hopf_package
    hpodd hv hZinj hRinj hρ χ₁ χ₂ hcont₁ hcont₂ hone₁ hone₂ hmul₁ hmul₂ hchar
    I hI G fG hfG
  obtain ⟨hU1, hU2⟩ := hU σ hσ
  set g : Field.absoluteGaloisGroup ℚ := Field.absoluteGaloisGroup.map
    (algebraMap ℚ (HeightOneSpectrum.adicCompletion ℚ
      hp.out.toHeightOneSpectrumRingOfIntegersRat)) σ
  set c : ℤ_[p] := ((cyclotomicCharacter (AlgebraicClosure ℚ) p
    g.toRingEquiv : ℤ_[p]ˣ) : ℤ_[p]) with hc
  set cS : R ⧸ I := algebraMap R (R ⧸ I) (algebraMap ℤ_[p] R c) with hcS
  set A' : Module.End (R ⧸ I) ((R ⧸ I) ⊗[R] V) :=
    (ρ.baseChange (R ⧸ I)) g with hA'
  -- the cyclotomic determinant of `ρ(σ̃)` over `R`
  have hdet : LinearMap.det (ρ g) = algebraMap ℤ_[p] R c := by
    have h := hρ.det g
    rw [GaloisRep.det_apply] at h
    rw [h, hc]
  -- the rank-2 characteristic polynomial over `R`
  have hcard : Fintype.card (Module.Free.ChooseBasisIndex R V) = 2 := by
    rw [← Module.finrank_eq_card_chooseBasisIndex]
    exact Module.finrank_eq_of_rank_eq hv
  let b : Module.Basis (Fin 2) R V :=
    (Module.Free.chooseBasis R V).reindex (Fintype.equivFinOfCardEq hcard)
  have hcharR : (ρ g).charpoly =
      Polynomial.X ^ 2 -
        Polynomial.C (LinearMap.trace R V (ρ g)) * Polynomial.X +
        Polynomial.C (LinearMap.det (ρ g)) := by
    rw [← LinearMap.charpoly_toMatrix (ρ g) b, Matrix.charpoly_fin_two,
      ← LinearMap.trace_eq_matrix_trace R b, LinearMap.det_toMatrix]
  -- the congruence-quotient action is the base-changed endomorphism
  have hAeq : A' = (ρ g).baseChange (R ⧸ I) := by
    refine LinearMap.ext fun m => ?_
    induction m using TensorProduct.induction_on with
    | zero => simp
    | tmul r x =>
      rw [hA']
      simp only [GaloisRep.baseChange_tmul, LinearMap.baseChange_tmul]
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  -- the base-changed basis certifies freeness and finiteness mod `I`
  let bS : Module.Basis (Fin 2) (R ⧸ I) ((R ⧸ I) ⊗[R] V) :=
    b.baseChange (R ⧸ I)
  haveI : Module.Free (R ⧸ I) ((R ⧸ I) ⊗[R] V) := Module.Free.of_basis bS
  haveI : Module.Finite (R ⧸ I) ((R ⧸ I) ⊗[R] V) := Module.Finite.of_basis bS
  -- the mod-`I` characteristic polynomial, determinant pinned to `c̄`
  have hcharS : LinearMap.charpoly A' =
      Polynomial.X ^ 2 -
        Polynomial.C (algebraMap R (R ⧸ I) (LinearMap.trace R V (ρ g))) *
          Polynomial.X +
        Polynomial.C cS := by
    rw [hAeq, LinearMap.charpoly_baseChange, hcharR, hdet, hcS]
    simp only [Polynomial.map_add, Polynomial.map_sub, Polynomial.map_mul,
      Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C]
  -- Cayley–Hamilton for the mod-`I` action
  have hCH := LinearMap.aeval_self_charpoly A'
  rw [hcharS] at hCH
  simp only [map_sub, map_add, map_mul, map_pow, Polynomial.aeval_X,
    Polynomial.aeval_C] at hCH
  -- the leaf's quadratic and Cayley–Hamilton force the trace scalar
  -- to act as `1 + c̄` on the image of `Ā`
  have e7 : ∀ m : (R ⧸ I) ⊗[R] V,
      algebraMap R (R ⧸ I) (LinearMap.trace R V (ρ g)) • A' m =
        A' m + cS • A' m := by
    intro m
    have h1 := hU2 _ (hU1 m)
    rw [map_sub, smul_sub, sub_eq_iff_eq_add] at h1
    have e1 := LinearMap.congr_fun hCH m
    simp only [LinearMap.sub_apply, LinearMap.add_apply, Module.End.mul_apply,
      Module.algebraMap_end_apply, LinearMap.zero_apply, pow_two] at e1
    rw [sub_add, sub_eq_zero] at e1
    have e6 : algebraMap R (R ⧸ I) (LinearMap.trace R V (ρ g)) • A' m -
        cS • m = cS • A' m - cS • m + A' m := e1.symm.trans h1
    calc algebraMap R (R ⧸ I) (LinearMap.trace R V (ρ g)) • A' m
        = (algebraMap R (R ⧸ I) (LinearMap.trace R V (ρ g)) • A' m -
            cS • m) + cS • m := by abel
      _ = (cS • A' m - cS • m + A' m) + cS • m := by rw [e6]
      _ = A' m + cS • A' m := by abel
  -- `Ā` is invertible: evaluate at the preimage of a basis vector
  have hAB : A' * (ρ.baseChange (R ⧸ I)) g⁻¹ = 1 := by
    rw [hA', ← map_mul, mul_inv_cancel, map_one]
  have hAm : A' ((ρ.baseChange (R ⧸ I)) g⁻¹ (bS 0)) = bS 0 := by
    have h := LinearMap.congr_fun hAB (bS 0)
    rwa [Module.End.mul_apply, Module.End.one_apply] at h
  have e7' := e7 ((ρ.baseChange (R ⧸ I)) g⁻¹ (bS 0))
  rw [hAm] at e7'
  -- read off the coordinate: the mod-`I` trace is `1 + c̄`
  have e8 : algebraMap R (R ⧸ I) (LinearMap.trace R V (ρ g)) = 1 + cS := by
    have h := congrArg (fun y => bS.repr y 0) e7'
    simpa using h
  -- conclude the congruence over `R`
  have hfin : algebraMap R (R ⧸ I)
      (LinearMap.trace R V (ρ g) - (1 + algebraMap ℤ_[p] R c)) = 0 := by
    rw [map_sub, map_add, map_one, ← hcS, e8, sub_self]
  rw [Ideal.Quotient.algebraMap_eq] at hfin
  exact Ideal.Quotient.eq_zero_iff_mem.mp hfin

/-- **The flat trace identity on inertia at `p`** (PROVEN assembly,
DECOMPOSED 2026-07-24 over the single sorried Hopf-package core
`trace_sub_one_add_cyclotomicCharacter_mem_of_hopf_package` above —
the Raynaud/Fontaine content of the reducible branch; the
linear-algebra, topology and level-passage glue is proven here): for
a hardly ramified (flat-at-`p`, cyclotomic-determinant) `ρ` whose
mapped characteristic polynomials split through the continuous
multiplicative pair `χ₁, χ₂` (the reducibility input — needed:
without it a supersingular `ρ|_{G_p}` is flat with irreducible
inertia charpolys, and the conclusion is false), the two character
values at (the image in `G_ℚ` of) a local inertia element `σ` at `p`
sum to `1 + χ_cyc(σ̃)` in `ℚ̄_p`. Together with the determinant
identity `χ₁(σ̃)·χ₂(σ̃) = χ_cyc(σ̃)` (proven in the consumer from
`hρ.det`), this says the multiset `{χ₁(σ̃), χ₂(σ̃)}` is
`{1, χ_cyc(σ̃)}` — the Raynaud dichotomy, in the swap-symmetric
summed spelling that keeps the sub/quotient matching out of the
statement (same convention as the global
`char_add_char_eq_one_add_cyclotomicCharacter`). Assembly: the
character sum is the mapped trace (`coeff 1` of the split charpoly
against `Matrix.trace_eq_neg_charpoly_coeff` at rank `2`); `R` is
free over `ℤ_[p]` (torsion-free from `hZinj` over the PID), hence
compact Hausdorff and Noetherian in its module topology, so the
maximal-ideal powers `𝔪ᵏ` are OPEN
(`IsLocalRing.isOpen_maximalIdeal_pow`) and `hρ.isFlat.cond` hands
the finite flat Hopf package of `ρ.baseChange (R ⧸ 𝔪ᵏ)` to the core
at every level `k`; the Krull intersection
(`Ideal.iInf_pow_eq_bot_of_isLocalRing`, `R` local Noetherian)
assembles the level-wise congruences into the `R`-level trace
identity, which lands in the stated `ℚ̄_p` identity along
`algebraMap_comp_algebraMap_padicInt`. -/
theorem char_add_char_eq_one_add_cyclotomicCharacter_of_mem_localInertiaGroup_p
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
      (Polynomial.X - Polynomial.C (χ₁ g)) * (Polynomial.X - Polynomial.C (χ₂ g)))
    (σ : Field.absoluteGaloisGroup (HeightOneSpectrum.adicCompletion ℚ
      hp.out.toHeightOneSpectrumRingOfIntegersRat))
    (hσ : σ ∈ localInertiaGroup hp.out.toHeightOneSpectrumRingOfIntegersRat) :
    χ₁ (Field.absoluteGaloisGroup.map (algebraMap ℚ (HeightOneSpectrum.adicCompletion ℚ
      hp.out.toHeightOneSpectrumRingOfIntegersRat)) σ) +
    χ₂ (Field.absoluteGaloisGroup.map (algebraMap ℚ (HeightOneSpectrum.adicCompletion ℚ
      hp.out.toHeightOneSpectrumRingOfIntegersRat)) σ) =
      1 + algebraMap ℤ_[p] (AlgebraicClosure ℚ_[p])
        ((cyclotomicCharacter (AlgebraicClosure ℚ) p
          ((Field.absoluteGaloisGroup.map (algebraMap ℚ (HeightOneSpectrum.adicCompletion ℚ
            hp.out.toHeightOneSpectrumRingOfIntegersRat)) σ).toRingEquiv) : ℤ_[p]ˣ) :
          ℤ_[p]) := by
  classical
  set g : Field.absoluteGaloisGroup ℚ :=
    Field.absoluteGaloisGroup.map (algebraMap ℚ (HeightOneSpectrum.adicCompletion ℚ
      hp.out.toHeightOneSpectrumRingOfIntegersRat)) σ
  set c : ℤ_[p] := ((cyclotomicCharacter (AlgebraicClosure ℚ) p g.toRingEquiv :
    ℤ_[p]ˣ) : ℤ_[p])
  -- the trace is minus the linear coefficient of the (degree-2) charpoly
  have hfr : Module.finrank R V = 2 := Module.finrank_eq_of_rank_eq hv
  have hcard : Fintype.card (Module.Free.ChooseBasisIndex R V) = 2 := by
    rw [← Module.finrank_eq_card_chooseBasisIndex]
    exact hfr
  haveI : Nonempty (Module.Free.ChooseBasisIndex R V) :=
    Fintype.card_pos_iff.mp (by rw [hcard]; norm_num)
  have htrace : LinearMap.trace R V (ρ g) = -((ρ g).charpoly.coeff 1) := by
    rw [LinearMap.trace_eq_matrix_trace R (Module.Free.chooseBasis R V),
      Matrix.trace_eq_neg_charpoly_coeff, LinearMap.charpoly_toMatrix, hcard]
  -- the character sum is the mapped trace: `coeff 1` of the split charpoly
  have hsum_tr : χ₁ g + χ₂ g =
      algebraMap R (AlgebraicClosure ℚ_[p]) (LinearMap.trace R V (ρ g)) := by
    have h1 := congrArg
      (fun P : Polynomial (AlgebraicClosure ℚ_[p]) => P.coeff 1) (hchar g)
    simp only [Polynomial.coeff_map] at h1
    have hexp : ((Polynomial.X - Polynomial.C (χ₁ g)) *
        (Polynomial.X - Polynomial.C (χ₂ g))).coeff 1 = -(χ₁ g + χ₂ g) := by
      have hprod2 : (Polynomial.X - Polynomial.C (χ₁ g)) *
          (Polynomial.X - Polynomial.C (χ₂ g)) =
          Polynomial.X ^ 2 - Polynomial.C (χ₁ g + χ₂ g) * Polynomial.X +
          Polynomial.C (χ₁ g * χ₂ g) := by
        rw [Polynomial.C_add, Polynomial.C_mul]
        ring
      rw [hprod2]
      simp [Polynomial.coeff_X_pow]
    rw [hexp] at h1
    rw [htrace, map_neg, h1, neg_neg]
  -- the coefficient ring is free over `ℤ_[p]` (torsion-free from `hZinj`),
  -- Noetherian, compact Hausdorff — so the maximal-ideal powers are open
  haveI : Module.IsTorsionFree ℤ_[p] R :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr hZinj
  haveI : Module.Free ℤ_[p] R := Module.free_of_finite_type_torsion_free'
  haveI : IsNoetherianRing R := IsNoetherianRing.of_finite ℤ_[p] R
  let eR : R ≃ₗ[ℤ_[p]] (Module.Free.ChooseBasisIndex ℤ_[p] R → ℤ_[p]) :=
    (Module.Free.chooseBasis ℤ_[p] R).equivFun
  have hcontR₁ : Continuous eR :=
    IsModuleTopology.continuous_of_linearMap eR.toLinearMap
  have hcontR₂ : Continuous eR.symm :=
    IsModuleTopology.continuous_of_linearMap eR.symm.toLinearMap
  let homR : R ≃ₜ (Module.Free.ChooseBasisIndex ℤ_[p] R → ℤ_[p]) :=
    { toEquiv := eR.toEquiv
      continuous_toFun := hcontR₁
      continuous_invFun := hcontR₂ }
  haveI : CompactSpace R := homR.symm.compactSpace
  haveI : T2Space R := homR.isEmbedding.t2Space
  -- per-level Raynaud congruence through the flat prolongation
  have hlev : ∀ k : ℕ, LinearMap.trace R V (ρ g) - (1 + algebraMap ℤ_[p] R c) ∈
      IsLocalRing.maximalIdeal R ^ k := by
    intro k
    have hIopen : IsOpen ((IsLocalRing.maximalIdeal R ^ k : Ideal R) : Set R) :=
      IsLocalRing.isOpen_maximalIdeal_pow R k
    obtain ⟨G, i1, i2, i3, i4, i5, fG, hfG⟩ :=
      hρ.isFlat.cond (IsLocalRing.maximalIdeal R ^ k) hIopen
    letI := i1
    letI := i2
    letI := i3
    letI := i4
    letI := i5
    exact trace_sub_one_add_cyclotomicCharacter_mem_of_hopf_package hpodd hv
      hZinj hRinj hρ χ₁ χ₂ hcont₁ hcont₂ hone₁ hone₂ hmul₁ hmul₂ hchar
      (IsLocalRing.maximalIdeal R ^ k) hIopen G fG hfG σ hσ
  -- the Krull intersection assembles the levels over `R`
  have htr_eq : LinearMap.trace R V (ρ g) = 1 + algebraMap ℤ_[p] R c := by
    have hKrull : (⨅ i : ℕ, IsLocalRing.maximalIdeal R ^ i) = (⊥ : Ideal R) :=
      Ideal.iInf_pow_eq_bot_of_isLocalRing (I := IsLocalRing.maximalIdeal R)
        (Ideal.IsMaximal.ne_top inferInstance)
    have hx : LinearMap.trace R V (ρ g) - (1 + algebraMap ℤ_[p] R c) ∈
        (⨅ i : ℕ, IsLocalRing.maximalIdeal R ^ i) :=
      (Submodule.mem_iInf _).mpr hlev
    rw [hKrull, Submodule.mem_bot] at hx
    exact sub_eq_zero.mp hx
  -- conclude in `ℚ̄_p` along the (continuous) coefficient embedding
  have hcomp : algebraMap R (AlgebraicClosure ℚ_[p]) (algebraMap ℤ_[p] R c) =
      algebraMap ℤ_[p] (AlgebraicClosure ℚ_[p]) c :=
    RingHom.congr_fun algebraMap_comp_algebraMap_padicInt c
  rw [hsum_tr, htr_eq, map_add, map_one, hcomp]

/-- **The flat inertia charpoly at `p`** (PROVEN assembly, DECOMPOSED
2026-07-24 over the single sorried scalar leaf
`char_add_char_eq_one_add_cyclotomicCharacter_of_mem_localInertiaGroup_p`
above): for a hardly ramified (flat-at-`p`, cyclotomic-determinant)
`ρ` whose mapped characteristic polynomials split through the
continuous pair `χ₁, χ₂`, the characteristic polynomial of `ρ` at
(the image in `G_ℚ` of) a local inertia element `σ` at `p` is
`(X - χ_cyc(σ))(X - 1)` over `R` — the exact `p`-place analogue of
the tame-at-two leaf `charpoly_eq_of_mem_inertia_two`. Assembly (pure
linear algebra, all proven): the product `χ₁(g)·χ₂(g)` is the mapped
cyclotomic determinant at EVERY `g` (`coeff 0` of the split charpoly
against `hρ.det` — the same computation as `hprod` in the global
`char_add_char_eq_one_add_cyclotomicCharacter`); the leaf pins the
sum `χ₁(σ̃) + χ₂(σ̃)` to `1 + χ_cyc(σ̃)`; a monic quadratic is
determined by its trace/determinant coefficient pair, so the mapped
charpoly is `(X - χ_cyc(σ̃))(X - 1)` over `ℚ̄_p`; and the identity
descends to `R` along the injective coefficient embedding
(`Polynomial.map_injective` on `hRinj`, with
`algebraMap_comp_algebraMap_padicInt` matching the two spellings of
the cyclotomic constant). -/
theorem charpoly_eq_of_mem_localInertiaGroup_p
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
      (Polynomial.X - Polynomial.C (χ₁ g)) * (Polynomial.X - Polynomial.C (χ₂ g)))
    (σ : Field.absoluteGaloisGroup (HeightOneSpectrum.adicCompletion ℚ
      hp.out.toHeightOneSpectrumRingOfIntegersRat))
    (hσ : σ ∈ localInertiaGroup hp.out.toHeightOneSpectrumRingOfIntegersRat) :
    (ρ (Field.absoluteGaloisGroup.map (algebraMap ℚ (HeightOneSpectrum.adicCompletion ℚ
      hp.out.toHeightOneSpectrumRingOfIntegersRat)) σ)).charpoly =
      (Polynomial.X - Polynomial.C (algebraMap ℤ_[p] R
        ((cyclotomicCharacter (AlgebraicClosure ℚ) p
          ((Field.absoluteGaloisGroup.map (algebraMap ℚ (HeightOneSpectrum.adicCompletion ℚ
            hp.out.toHeightOneSpectrumRingOfIntegersRat)) σ).toRingEquiv) : ℤ_[p]ˣ) :
          ℤ_[p]))) *
      (Polynomial.X - Polynomial.C 1) := by
  classical
  set g : Field.absoluteGaloisGroup ℚ :=
    Field.absoluteGaloisGroup.map (algebraMap ℚ (HeightOneSpectrum.adicCompletion ℚ
      hp.out.toHeightOneSpectrumRingOfIntegersRat)) σ with hgdef
  set c : ℤ_[p] := ((cyclotomicCharacter (AlgebraicClosure ℚ) p g.toRingEquiv :
    ℤ_[p]ˣ) : ℤ_[p]) with hcdef
  have hfr : Module.finrank R V = 2 := Module.finrank_eq_of_rank_eq hv
  -- the product identity: `coeff 0` of the split mapped charpoly against
  -- the cyclotomic-determinant clause (valid at every `g`)
  have hprod : χ₁ g * χ₂ g = algebraMap ℤ_[p] (AlgebraicClosure ℚ_[p]) c := by
    have hdet0 : (ρ g).charpoly.coeff 0 = ρ.det g := by
      rw [GaloisRep.det_apply, LinearMap.det_eq_sign_charpoly_coeff, hfr]
      norm_num
    have h0 : (((ρ g).charpoly).map (algebraMap R (AlgebraicClosure ℚ_[p]))).coeff 0 =
        ((Polynomial.X - Polynomial.C (χ₁ g)) *
          (Polynomial.X - Polynomial.C (χ₂ g))).coeff 0 :=
      congrArg (fun P : Polynomial (AlgebraicClosure ℚ_[p]) => P.coeff 0) (hchar g)
    rw [Polynomial.coeff_map, hdet0, hρ.det g, Polynomial.mul_coeff_zero] at h0
    simp only [Polynomial.coeff_sub, Polynomial.coeff_X_zero, Polynomial.coeff_C_zero,
      zero_sub, neg_mul_neg] at h0
    rw [← h0]
    exact RingHom.congr_fun algebraMap_comp_algebraMap_padicInt _
  -- the sum identity on inertia: the Raynaud sub-leaf
  have hsum := char_add_char_eq_one_add_cyclotomicCharacter_of_mem_localInertiaGroup_p
    hpodd hv hZinj hRinj hρ χ₁ χ₂ hcont₁ hcont₂ hone₁ hone₂ hmul₁ hmul₂ hchar σ hσ
  rw [← hgdef, ← hcdef] at hsum
  -- a monic quadratic is determined by its trace/determinant pair
  have hQQ : (Polynomial.X - Polynomial.C (χ₁ g)) * (Polynomial.X - Polynomial.C (χ₂ g)) =
      (Polynomial.X - Polynomial.C (algebraMap ℤ_[p] (AlgebraicClosure ℚ_[p]) c)) *
      (Polynomial.X - Polynomial.C 1) := by
    have hexp₁ : (Polynomial.X - Polynomial.C (χ₁ g)) *
        (Polynomial.X - Polynomial.C (χ₂ g)) =
        Polynomial.X ^ 2 - Polynomial.C (χ₁ g + χ₂ g) * Polynomial.X +
        Polynomial.C (χ₁ g * χ₂ g) := by
      rw [Polynomial.C_add, Polynomial.C_mul]
      ring
    have hexp₂ : (Polynomial.X -
        Polynomial.C (algebraMap ℤ_[p] (AlgebraicClosure ℚ_[p]) c)) *
        (Polynomial.X - Polynomial.C 1) =
        Polynomial.X ^ 2 -
        Polynomial.C (1 + algebraMap ℤ_[p] (AlgebraicClosure ℚ_[p]) c) * Polynomial.X +
        Polynomial.C (algebraMap ℤ_[p] (AlgebraicClosure ℚ_[p]) c) := by
      rw [Polynomial.C_add, Polynomial.C_1]
      ring
    rw [hexp₁, hexp₂, hsum, hprod]
  -- descend along the injective coefficient embedding
  have hcomp : algebraMap R (AlgebraicClosure ℚ_[p]) (algebraMap ℤ_[p] R c) =
      algebraMap ℤ_[p] (AlgebraicClosure ℚ_[p]) c :=
    RingHom.congr_fun algebraMap_comp_algebraMap_padicInt c
  refine Polynomial.map_injective _ hRinj ?_
  rw [hchar g, hQQ]
  simp only [Polynomial.map_mul, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C,
    Polynomial.map_one, map_one, hcomp]

/-- **The flat dichotomy on inertia at `p`** (PROVEN assembly,
DECOMPOSED 2026-07-23 over the single sorried leaf
`charpoly_eq_of_mem_localInertiaGroup_p`): the Raynaud/Fontaine route
stage of `char_add_char_eq_one_add_cyclotomicCharacter`: for a hardly
ramified (in particular flat-at-`p`, cyclotomic-determinant) `ρ` whose
mapped characteristic polynomials split through the pair `χ₁, χ₂`, ONE
of the two characters is trivial on the (image of the) local inertia
at `p` — a disjunction of universally-quantified trivialities, stated
so deliberately to keep pointwise matching out of the statement.
Assembly, two stages:

* *pointwise dichotomy* (`hdich` below): mapping the charpoly identity
  of the leaf along `R → ℚ̄_p` against `hchar` and evaluating at `1`
  (a root of the flat side) gives, at EACH inertia element `σ`,
  `χ₁(σ̃) = 1 ∨ χ₂(σ̃) = 1` — with the matching free to vary with `σ`;
* *swap rigidity*: the matching cannot in fact vary — if neither
  character were identically `1` on inertia, witnesses `σ₁` (where
  `χ₁ ≠ 1`, hence `χ₂ = 1`) and `σ₂` (where `χ₂ ≠ 1`, hence `χ₁ = 1`)
  would give, at the inertia element `σ₁ * σ₂` (inertia is a
  subgroup), `χ₁(σ̃₁σ̃₂) = χ₁(σ̃₁) ≠ 1` and `χ₂(σ̃₁σ̃₂) = χ₂(σ̃₂) ≠ 1`
  by multiplicativity, contradicting the pointwise dichotomy. This is
  the level-independence ("which of `χ₁, χ₂` is the sub-character")
  bookkeeping, done once on characters instead of once per level. -/
theorem char_eq_one_on_localInertiaGroup_p_or
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
    (∀ σ ∈ localInertiaGroup hp.out.toHeightOneSpectrumRingOfIntegersRat,
      χ₁ (Field.absoluteGaloisGroup.map (algebraMap ℚ (HeightOneSpectrum.adicCompletion ℚ
        hp.out.toHeightOneSpectrumRingOfIntegersRat)) σ) = 1) ∨
    (∀ σ ∈ localInertiaGroup hp.out.toHeightOneSpectrumRingOfIntegersRat,
      χ₂ (Field.absoluteGaloisGroup.map (algebraMap ℚ (HeightOneSpectrum.adicCompletion ℚ
        hp.out.toHeightOneSpectrumRingOfIntegersRat)) σ) = 1) := by
  classical
  -- pointwise dichotomy: at each inertia element one of the two
  -- characters is `1` — evaluate the mapped flat charpoly identity at `1`
  have hdich : ∀ σ ∈ localInertiaGroup hp.out.toHeightOneSpectrumRingOfIntegersRat,
      χ₁ (Field.absoluteGaloisGroup.map (algebraMap ℚ (HeightOneSpectrum.adicCompletion ℚ
        hp.out.toHeightOneSpectrumRingOfIntegersRat)) σ) = 1 ∨
      χ₂ (Field.absoluteGaloisGroup.map (algebraMap ℚ (HeightOneSpectrum.adicCompletion ℚ
        hp.out.toHeightOneSpectrumRingOfIntegersRat)) σ) = 1 := by
    intro σ hσ
    have hB := charpoly_eq_of_mem_localInertiaGroup_p hpodd hv hZinj hRinj hρ χ₁ χ₂
      hcont₁ hcont₂ hone₁ hone₂ hmul₁ hmul₂ hchar σ hσ
    have hpoly := hchar (Field.absoluteGaloisGroup.map (algebraMap ℚ
      (HeightOneSpectrum.adicCompletion ℚ hp.out.toHeightOneSpectrumRingOfIntegersRat)) σ)
    rw [hB] at hpoly
    simp only [Polynomial.map_mul, Polynomial.map_sub, Polynomial.map_X,
      Polynomial.map_C] at hpoly
    have h := congrArg (Polynomial.eval (1 : AlgebraicClosure ℚ_[p])) hpoly
    simp only [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X,
      Polynomial.eval_C, Polynomial.eval_one, map_one, sub_self, mul_zero] at h
    rcases mul_eq_zero.mp h.symm with h1 | h1
    · exact Or.inl (sub_eq_zero.mp h1).symm
    · exact Or.inr (sub_eq_zero.mp h1).symm
  -- swap rigidity: if neither character dies identically on inertia,
  -- the product of the two witnesses violates the pointwise dichotomy
  by_contra hcon
  push Not at hcon
  obtain ⟨⟨σ₁, hσ₁, hne₁⟩, σ₂, hσ₂, hne₂⟩ := hcon
  have h₂σ₁ : χ₂ (Field.absoluteGaloisGroup.map (algebraMap ℚ
      (HeightOneSpectrum.adicCompletion ℚ
        hp.out.toHeightOneSpectrumRingOfIntegersRat)) σ₁) = 1 :=
    (hdich σ₁ hσ₁).resolve_left hne₁
  have h₁σ₂ : χ₁ (Field.absoluteGaloisGroup.map (algebraMap ℚ
      (HeightOneSpectrum.adicCompletion ℚ
        hp.out.toHeightOneSpectrumRingOfIntegersRat)) σ₂) = 1 :=
    (hdich σ₂ hσ₂).resolve_right hne₂
  rcases hdich (σ₁ * σ₂) (mul_mem hσ₁ hσ₂) with hd | hd
  · rw [map_mul, hmul₁, h₁σ₂, mul_one] at hd
    exact hne₁ hd
  · rw [map_mul, hmul₂, h₂σ₁, one_mul] at hd
    exact hne₂ hd

set_option backward.isDefEq.respectTransparency false in
/-- **Minkowski, closed-subgroup form** (PROVEN 2026-07-24, reduction
to the open form `open_normal_subgroup_eq_top_of_inertia_le`): a
CLOSED normal subgroup of `G_ℚ` containing the image of the local
inertia group at every prime is everything. Reduction: the fixed
field `L` of `H` recovers `H` by the infinite Galois correspondence
(`H` is closed) and is Galois over `ℚ` (`H` is normal); every `x ∈ L`
generates a finite subextension `ℚ⟮x⟯ ≤ L` whose normal closure `M`
is a finite Galois subextension of `L`, so `M.fixingSubgroup` is an
OPEN normal subgroup containing `H` and hence every inertia image;
the open form (Minkowski's discriminant bound under the hood) makes
it everything, so `M = ⊥` and `x ∈ ⊥`. Thus `L = ⊥` and
`H = L.fixingSubgroup = ⊤`. -/
theorem closed_normal_subgroup_eq_top_of_inertia_le
    (H : Subgroup (Field.absoluteGaloisGroup ℚ)) [hnorm : H.Normal]
    (hclosed : IsClosed (H : Set (Field.absoluteGaloisGroup ℚ)))
    (hinertia : ∀ (q : ℕ) (hq : q.Prime),
      Subgroup.map (Field.absoluteGaloisGroup.map (algebraMap ℚ
        (HeightOneSpectrum.adicCompletion ℚ
          hq.toHeightOneSpectrumRingOfIntegersRat))).toMonoidHom
        (localInertiaGroup hq.toHeightOneSpectrumRingOfIntegersRat) ≤ H) :
    H = ⊤ := by
  haveI hgal : IsGalois ℚ (AlgebraicClosure ℚ) := ⟨⟩
  set L : IntermediateField ℚ (AlgebraicClosure ℚ) :=
    IntermediateField.fixedField (E := AlgebraicClosure ℚ) H
  have hfix : L.fixingSubgroup = H :=
    InfiniteGalois.fixingSubgroup_fixedField ⟨H, hclosed⟩
  haveI hgalL : IsGalois ℚ L := (InfiniteGalois.normal_iff_isGalois L).mp
    (by rw [hfix]; exact hnorm)
  have hLbot : L = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have hxint : IsIntegral ℚ x := (Algebra.IsAlgebraic.isAlgebraic x).isIntegral
    haveI : FiniteDimensional ℚ (IntermediateField.adjoin ℚ {x}) :=
      IntermediateField.adjoin.finiteDimensional hxint
    set M : IntermediateField ℚ (AlgebraicClosure ℚ) :=
      IntermediateField.normalClosure ℚ (IntermediateField.adjoin ℚ {x})
        (AlgebraicClosure ℚ)
    haveI hgalM : IsGalois ℚ M := ⟨⟩
    have hML : M ≤ L :=
      IntermediateField.normalClosure_le_iff_of_normal.mpr
        (IntermediateField.adjoin_simple_le_iff.mpr hx)
    have hopenM : IsOpen (M.fixingSubgroup : Set (Field.absoluteGaloisGroup ℚ)) :=
      (InfiniteGalois.isOpen_iff_finite M).mpr inferInstance
    haveI hnormM : M.fixingSubgroup.Normal :=
      (InfiniteGalois.normal_iff_isGalois M).mpr inferInstance
    have hHM : H ≤ M.fixingSubgroup := by
      rw [← hfix]
      exact IntermediateField.fixingSubgroup_antitone hML
    have htopM : M.fixingSubgroup = ⊤ :=
      open_normal_subgroup_eq_top_of_inertia_le M.fixingSubgroup hopenM
        fun q hq => le_trans (hinertia q hq) hHM
    have hMbot : M = ⊥ := by
      rw [← InfiniteGalois.fixedField_fixingSubgroup M, htopM,
        InfiniteGalois.fixedField_bot]
    have hxM : x ∈ M :=
      IntermediateField.le_normalClosure (IntermediateField.adjoin ℚ {x})
        (IntermediateField.mem_adjoin_simple_self ℚ x)
    rwa [hMbot] at hxM
  rw [← hfix, hLbot, IntermediateField.fixingSubgroup_bot]

/-- **Minkowski: a character unramified everywhere is trivial**
(PROVEN 2026-07-24): the final route stage of
`char_add_char_eq_one_add_cyclotomicCharacter`: a continuous
multiplicative unital `χ : G_ℚ → ℚ̄_p` that kills the image of every
local inertia subgroup is constantly `1`. Proof: `χ` never vanishes
(`χ g · χ g⁻¹ = χ 1 = 1`) and its target is commutative, so
`H := {g | χ g = 1}` is a normal subgroup; it is closed (`ℚ̄_p` is a
normed field, hence `T1`, and `χ` is continuous) and contains the
image of every local inertia group by hypothesis, hence is everything
by the closed-subgroup Minkowski discriminant theorem
`closed_normal_subgroup_eq_top_of_inertia_le` (mathlib's
`NumberField.exists_not_isUnramifiedAt_int_of_isGalois` under the
hood, through `open_normal_subgroup_eq_top_of_inertia_le`). -/
theorem char_eq_one_of_forall_mem_localInertiaGroup
    (χ : Field.absoluteGaloisGroup ℚ → AlgebraicClosure ℚ_[p])
    (hcont : Continuous χ) (hone : χ 1 = 1)
    (hmul : ∀ g h, χ (g * h) = χ g * χ h)
    (hunr : ∀ (v : HeightOneSpectrum (NumberField.RingOfIntegers ℚ))
      (σ : Field.absoluteGaloisGroup (HeightOneSpectrum.adicCompletion ℚ v)),
      σ ∈ localInertiaGroup v →
      χ (Field.absoluteGaloisGroup.map (algebraMap ℚ
        (HeightOneSpectrum.adicCompletion ℚ v)) σ) = 1) :
    ∀ g, χ g = 1 := by
  have hinv : ∀ g, χ g = 1 → χ g⁻¹ = 1 := by
    intro g hg
    have h1 : χ g * χ g⁻¹ = 1 := by rw [← hmul, mul_inv_cancel, hone]
    rwa [hg, one_mul] at h1
  let H : Subgroup (Field.absoluteGaloisGroup ℚ) :=
    { carrier := {g | χ g = 1}
      one_mem' := hone
      mul_mem' := fun {a b} ha hb => by
        have ha' : χ a = 1 := ha
        have hb' : χ b = 1 := hb
        show χ (a * b) = 1
        rw [hmul, ha', hb', one_mul]
      inv_mem' := fun {a} ha => hinv a ha }
  haveI hnorm : H.Normal := by
    refine ⟨fun n hn g => ?_⟩
    have hn' : χ n = 1 := hn
    show χ (g * n * g⁻¹) = 1
    rw [hmul, hmul, hn', mul_one, ← hmul, mul_inv_cancel, hone]
  have hclosed : IsClosed (H : Set (Field.absoluteGaloisGroup ℚ)) := by
    have hpre : (H : Set (Field.absoluteGaloisGroup ℚ)) = χ ⁻¹' {1} := rfl
    rw [hpre]
    exact isClosed_singleton.preimage hcont
  have htop : H = ⊤ :=
    closed_normal_subgroup_eq_top_of_inertia_le H hclosed fun q hq => by
      rw [Subgroup.map_le_iff_le_comap]
      intro σ hσ
      rw [Subgroup.mem_comap]
      exact hunr _ σ hσ
  intro g
  have hg : g ∈ H := by rw [htop]; exact Subgroup.mem_top g
  exact hg

/-- **The Eisenstein character dichotomy** (PROVEN assembly, DECOMPOSED
2026-07-23 over three sorried route-stage leaves): if a pair of
continuous multiplicative characters `χ₁, χ₂ : G_ℚ → ℚ̄_p` splits every
mapped characteristic polynomial of a hardly ramified `ρ` (i.e.
`charpoly (ρ g) ↦ (X - χ₁ g)(X - χ₂ g)` for every `g`), then
`{χ₁, χ₂} = {1, χ_cyc}` in the symmetric (summed) form
`χ₁ + χ₂ = 1 + χ_cyc` pointwise. This is the class-field-theoretic
core of the reducible branch, isolated from all linear algebra (the
character extraction is the PROVEN
`exists_char_charpoly_map_eq_of_not_isIrreducible`); the route, one
node per stage:

* comparing `coeff 0` against the cyclotomic-determinant condition of
  `IsHardlyRamified`, `χ₁ · χ₂ = χ_cyc` (mapped) — PROVEN inline
  (`hprod` below);
* at inertia away from `{2, p}`: `ρ` is unramified there, so the
  split characteristic polynomial is `(X - 1)²` and both characters
  die on inertia — PROVEN,
  `char_eq_one_of_mem_localInertiaGroup_of_ne`;
* at inertia at `2`: the tame-at-two condition makes `ρ|_{G_2}`
  triangular with both diagonal entries killed by inertia — PROVEN
  assembly `char_eq_one_of_mem_localInertiaGroup_two` over the sorry
  leaves `cyclotomicCharacter_eq_one_of_mem_inertia_two` (arithmetic:
  `μ_{p^∞}` is unramified at `2`) and `charpoly_eq_of_mem_inertia_two`
  (linear algebra: the tame triangular factorization);
* at `p`: flatness of `ρ` at `p` forces (Raynaud/Fontaine on the
  finite levels) one of `χ₁, χ₂` to die on inertia at `p` — PROVEN
  assembly `char_eq_one_on_localInertiaGroup_p_or` over the proven
  flat charpoly `charpoly_eq_of_mem_localInertiaGroup_p`, whose sole
  remaining sorried input is the Raynaud trace leaf
  `char_add_char_eq_one_add_cyclotomicCharacter_of_mem_localInertiaGroup_p`;
* Minkowski: `ℚ` has no nontrivial extension unramified everywhere,
  so the member of the pair with everywhere-dead inertia is trivial —
  sorry leaf `char_eq_one_of_forall_mem_localInertiaGroup` — and the
  other is exactly `χ_cyc` by the product identity.

The conclusion is stated in the swap-symmetric summed form so that no
choice of matching survives into the statement; the assembly below
symmetrizes through the helper `hswap`, which runs the
Minkowski finish for whichever character the flat dichotomy selects. -/
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
        ((cyclotomicCharacter (AlgebraicClosure ℚ) p g.toRingEquiv : ℤ_[p]ˣ) : ℤ_[p]) := by
  classical
  have hfr : Module.finrank R V = 2 := Module.finrank_eq_of_rank_eq hv
  -- the product of the two characters is the mapped cyclotomic character:
  -- `coeff 0` of the split characteristic polynomial against the
  -- cyclotomic-determinant condition
  have hprod : ∀ g, χ₁ g * χ₂ g =
      algebraMap ℤ_[p] (AlgebraicClosure ℚ_[p])
        ((cyclotomicCharacter (AlgebraicClosure ℚ) p g.toRingEquiv : ℤ_[p]ˣ) : ℤ_[p]) := by
    intro g
    have hdet0 : (ρ g).charpoly.coeff 0 = ρ.det g := by
      rw [GaloisRep.det_apply, LinearMap.det_eq_sign_charpoly_coeff, hfr]
      norm_num
    have h0 : (((ρ g).charpoly).map (algebraMap R (AlgebraicClosure ℚ_[p]))).coeff 0 =
        ((Polynomial.X - Polynomial.C (χ₁ g)) *
          (Polynomial.X - Polynomial.C (χ₂ g))).coeff 0 :=
      congrArg (fun P : Polynomial (AlgebraicClosure ℚ_[p]) => P.coeff 0) (hchar g)
    rw [Polynomial.coeff_map, hdet0, hρ.det g, Polynomial.mul_coeff_zero] at h0
    simp only [Polynomial.coeff_sub, Polynomial.coeff_X_zero, Polynomial.coeff_C_zero,
      zero_sub, neg_mul_neg] at h0
    rw [← h0]
    exact RingHom.congr_fun algebraMap_comp_algebraMap_padicInt _
  -- the Minkowski finish, symmetrized: whichever character the flat
  -- dichotomy kills on inertia at `p` is killed on ALL inertia by the
  -- two proven stages and the at-2 leaf, hence trivial
  have hswap : ∀ χ χ' : Field.absoluteGaloisGroup ℚ → AlgebraicClosure ℚ_[p],
      Continuous χ → χ 1 = 1 → (∀ g h, χ (g * h) = χ g * χ h) →
      χ' 1 = 1 → (∀ g h, χ' (g * h) = χ' g * χ' h) →
      (∀ g, ((ρ g).charpoly).map (algebraMap R (AlgebraicClosure ℚ_[p])) =
        (Polynomial.X - Polynomial.C (χ g)) * (Polynomial.X - Polynomial.C (χ' g))) →
      (∀ σ ∈ localInertiaGroup hp.out.toHeightOneSpectrumRingOfIntegersRat,
        χ (Field.absoluteGaloisGroup.map (algebraMap ℚ (HeightOneSpectrum.adicCompletion ℚ
          hp.out.toHeightOneSpectrumRingOfIntegersRat)) σ) = 1) →
      ∀ g, χ g = 1 := by
    intro χ χ' hcont hone hmul hone' hmul' hchar' hinertp
    refine char_eq_one_of_forall_mem_localInertiaGroup χ hcont hone hmul ?_
    intro v σ hσ
    obtain ⟨q, hq, rfl⟩ := exists_prime_toHeightOneSpectrumRingOfIntegersRat v
    by_cases hq2 : q = 2
    · subst hq2
      exact (char_eq_one_of_mem_localInertiaGroup_two hpodd hv hρ χ χ'
        hone hone' hmul hmul' hchar' σ hσ).1
    · by_cases hqp : q = p
      · subst hqp
        exact hinertp σ hσ
      · exact (char_eq_one_of_mem_localInertiaGroup_of_ne hpodd hv hρ χ χ' hchar'
          hq hq2 hqp σ hσ).1
  have hkey : (∀ g, χ₁ g = 1) ∨ (∀ g, χ₂ g = 1) := by
    rcases char_eq_one_on_localInertiaGroup_p_or hpodd hv hZinj hRinj hρ χ₁ χ₂
        hcont₁ hcont₂ hone₁ hone₂ hmul₁ hmul₂ hchar with hIp | hIp
    · exact Or.inl (hswap χ₁ χ₂ hcont₁ hone₁ hmul₁ hone₂ hmul₂ hchar hIp)
    · refine Or.inr (hswap χ₂ χ₁ hcont₂ hone₂ hmul₂ hone₁ hmul₁ (fun g => ?_) hIp)
      rw [hchar g]
      exact mul_comm _ _
  rcases hkey with h1 | h1
  · intro g
    have hpg := hprod g
    rw [h1 g, one_mul] at hpg
    rw [h1 g, hpg]
  · intro g
    have hpg := hprod g
    rw [h1 g, mul_one] at hpg
    rw [h1 g, hpg, add_comm]

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
2. `char_add_char_eq_one_add_cyclotomicCharacter` (PROVEN assembly,
   further DECOMPOSED 2026-07-23) — the Eisenstein core: for such a
   pair, `χ₁ + χ₂ = 1 + χ_cyc` pointwise, assembled over now-PROVEN
   route stages (inertia away from `{2, p}`; inertia at `2`;
   `char_eq_one_on_localInertiaGroup_p_or` at `p`; the Minkowski
   finish `char_eq_one_of_forall_mem_localInertiaGroup`), whose
   single surviving sorried input is the Raynaud trace leaf
   `char_add_char_eq_one_add_cyclotomicCharacter_of_mem_localInertiaGroup_p`
   (see its docstring for the full route).
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

/-- **The Hecke field on the irreducible branch** (PROVEN assembly,
see the DECOMPOSED note below): away
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
content of the irreducible branch is carried by exactly one sorry.

DECOMPOSED (2026-07-23, opening the modularity subtree) into a PROVEN
assembly over the modularity interface
(`Fermat/FLT/Modularity/Interface.lean`), where the eigenform now has
an actual carrier on the pin (`Modularity.IsWeightTwoEigenform`, the
Diamond–Shurman 5.8.5 coefficient characterization on the pin's
`CuspForm`):

1. `Modularity.exists_weightTwoEigenform_trace_eq_of_isIrreducible`
   (sorry node) — the modularity input: the Frobenius traces are, away
   from finitely many places, the `ι`-images of the coefficients of a
   normalized weight-2 eigenform `f` of some level `N ≥ 1`, for a
   single embedding `ι : K_f →+* ℚ̄_p` of its Hecke field.
2. `Modularity.heckeField_finiteDimensional` (sorry node) — the Hecke
   field `K_f = ℚ({aₙ(f)})` is a number field (Diamond–Shurman §6.5).
3. The assembly (below, PROVEN): `E` is `ℚ` with the `ι`-images of a
   finite `ℚ`-spanning set of `K_f` adjoined — finite-dimensional
   because each generator is integral over `ℚ` (image of an element of
   a number field under a ring hom commuting with `ℚ`, ring homs out
   of `ℚ` being unique); every trace is `−ι(a_q) ∈ E` by span
   induction (the `ℚ`-scalars fall into `E` through the base field). -/
theorem exists_finiteDimensional_trace_field_of_isIrreducible
    [Algebra R (AlgebraicClosure ℚ_[p])]
    [ContinuousSMul R (AlgebraicClosure ℚ_[p])]
    (hZinj : Function.Injective (algebraMap ℤ_[p] R))
    (hRinj : Function.Injective (algebraMap R (AlgebraicClosure ℚ_[p])))
    (hρ : IsHardlyRamified hpodd hv ρ)
    (_hint : ∀ (v : HeightOneSpectrum (NumberField.RingOfIntegers ℚ)) (n : ℕ),
      ((algebraMap R (AlgebraicClosure ℚ_[p])).comp (algebraMap ℤ_[p] R)).IsIntegralElem
        (((ρ.charFrob v).map (algebraMap R (AlgebraicClosure ℚ_[p]))).coeff n))
    (K : IntermediateField ℚ_[p] (AlgebraicClosure ℚ_[p]))
    (_hKfd : FiniteDimensional ℚ_[p] K)
    (_hK : ∀ (v : HeightOneSpectrum (NumberField.RingOfIntegers ℚ)) (n : ℕ),
      ((ρ.charFrob v).map (algebraMap R (AlgebraicClosure ℚ_[p]))).coeff n ∈ K)
    (hirr : (ρ.baseChange (AlgebraicClosure ℚ_[p])).IsIrreducible) :
    ∃ (E : IntermediateField ℚ (AlgebraicClosure ℚ_[p]))
      (_ : FiniteDimensional ℚ E)
      (S : Finset (HeightOneSpectrum (NumberField.RingOfIntegers ℚ))),
      ∀ v ∉ S,
        ((ρ.charFrob v).map (algebraMap R (AlgebraicClosure ℚ_[p]))).coeff 1 ∈ E := by
  classical
  obtain ⟨N, hN, f, hf, ι, S, hS⟩ :=
    Modularity.exists_weightTwoEigenform_trace_eq_of_isIrreducible hpodd hv
      hZinj hRinj hρ hirr
  haveI : FiniteDimensional ℚ (Modularity.heckeField N f) :=
    Modularity.heckeField_finiteDimensional hN hf
  -- a finite `ℚ`-spanning set of the Hecke field
  obtain ⟨s, hs⟩ : (⊤ : Submodule ℚ (Modularity.heckeField N f)).FG :=
    Module.finite_def.mp inferInstance
  -- ring homs out of `ℚ` are unique, so `ι` restricts to the canonical map
  have hQcomp : algebraMap ℚ (AlgebraicClosure ℚ_[p]) =
      ι.comp (algebraMap ℚ (Modularity.heckeField N f)) := Subsingleton.elim _ _
  -- the `ι`-image of the Hecke field is integral over `ℚ`
  have hint' : ∀ x : Modularity.heckeField N f, IsIntegral ℚ (ι x) := by
    intro x
    obtain ⟨P, hPmonic, hPeval⟩ := IsIntegral.of_finite ℚ x
    refine ⟨P, hPmonic, ?_⟩
    rw [hQcomp, ← Polynomial.hom_eval₂, hPeval, map_zero]
  -- every `ι`-image lies in the field the finite spanning set generates
  have hmem : ∀ x : Modularity.heckeField N f,
      ι x ∈ IntermediateField.adjoin ℚ (⇑ι '' ↑s) := by
    intro x
    have hx : x ∈ Submodule.span ℚ (↑s : Set (Modularity.heckeField N f)) := by
      rw [hs]; exact Submodule.mem_top
    induction hx using Submodule.span_induction with
    | mem y hy => exact IntermediateField.subset_adjoin _ _ ⟨y, hy, rfl⟩
    | zero => rw [map_zero]; exact zero_mem _
    | add y z _ _ hy hz => rw [map_add]; exact add_mem hy hz
    | smul c y _ hy =>
      rw [Algebra.smul_def, map_mul]
      refine mul_mem ?_ hy
      have hc := RingHom.congr_fun hQcomp c
      rw [RingHom.comp_apply] at hc
      rw [← hc]
      exact IntermediateField.algebraMap_mem _ _
  refine ⟨IntermediateField.adjoin ℚ (⇑ι '' ↑s), ?_, S, ?_⟩
  · haveI : Finite ↥(⇑ι '' ↑s) := (s.finite_toSet.image _).to_subtype
    exact IntermediateField.finiteDimensional_adjoin fun x hx => by
      obtain ⟨y, -, rfl⟩ := hx
      exact hint' y
  · intro v hv'
    obtain ⟨q, hq, rfl⟩ := exists_prime_toHeightOneSpectrumRingOfIntegersRat v
    rw [hS q hq hv']
    exact neg_mem (hmem _)

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

-- `isIntegral_padicInt_of_spectralNorm_le_one` (the `ℤ_ℓ`-avatar of
-- `isIntegral_of_spectralNorm_le_one`, consumed just below) used to live here;
-- it moved to `Fermat/FLT/Mathlib/RingTheory/PadicIntegralClosure.lean`
-- (2026-07-25) so that `Modularity/Interface.lean`'s Ribet-cut hull leaf
-- `exists_padicIntegers_dvr_hull`, which is UPSTREAM of this file, can share
-- it. It arrives here through the public import of `Modularity/Interface`.

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

/-! #### Universe transport along `ULift` (PROVEN layer)

Helper layer for the formal transport leaf
`exists_realization_package_of_concrete`: a coefficient ring `A₀ : Type`
is relabeled as `ULift.{u} A₀`, which acts on the UNCHANGED module `W`
through `ULift.down` (the instance `ULift.module`), so endomorphisms,
bases, determinants, characteristic polynomials and Galois
representations all transport by identity-on-elements relabelings. -/

/-- **Endomorphism relabeling along `ULift`** (PROVEN): an `A₀`-linear
endomorphism of `W` *is* an `ULift A₀`-linear endomorphism for the
`ULift.down`-action — the identity on underlying functions, packaged as
a ring isomorphism of endomorphism rings. -/
def endULiftRingEquiv (A₀ : Type) [CommRing A₀] (W : Type*) [AddCommGroup W]
    [Module A₀ W] : Module.End A₀ W ≃+* Module.End (ULift.{u} A₀) W where
  toFun f :=
    { toFun := f
      map_add' := f.map_add'
      map_smul' := fun a w => f.map_smul' a.down w }
  invFun g :=
    { toFun := g
      map_add' := g.map_add'
      map_smul' := fun a w => g.map_smul' (ULift.up a) w }
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl

/-- **Galois-representation relabeling along `ULift`** (PROVEN): a Galois
representation over `A₀` is one over `ULift A₀` on the same module — the
composite with the endomorphism relabeling, which is continuous for the
respective module topologies because it is additive and equivariant over
the (continuous) ring map `ULift.up`. -/
noncomputable def galoisRepULift {K : Type*} [Field K] {A₀ : Type} [CommRing A₀]
    [TopologicalSpace A₀] {W : Type*} [AddCommGroup W] [Module A₀ W]
    (ρ : GaloisRep K A₀ W) : GaloisRep K (ULift.{u} A₀) W :=
  letI := moduleTopology A₀ (Module.End A₀ W)
  letI := moduleTopology (ULift.{u} A₀) (Module.End (ULift.{u} A₀) W)
  haveI : IsModuleTopology A₀ (Module.End A₀ W) := ⟨rfl⟩
  haveI : ContinuousAdd (Module.End (ULift.{u} A₀) W) :=
    ModuleTopology.continuousAdd (ULift.{u} A₀) (Module.End (ULift.{u} A₀) W)
  haveI : ContinuousSMul (ULift.{u} A₀) (Module.End (ULift.{u} A₀) W) :=
    ModuleTopology.continuousSMul (ULift.{u} A₀) (Module.End (ULift.{u} A₀) W)
  ContinuousMonoidHom.comp
    ⟨(endULiftRingEquiv A₀ W).toRingHom.toMonoidHom,
      IsModuleTopology.continuous_of_distribMulActionHomₑ
        (σ := ((ULift.ringEquiv : ULift.{u} A₀ ≃+* A₀).symm.toRingHom.toMonoidHom))
        continuous_uliftUp
        { toFun := endULiftRingEquiv A₀ W
          map_smul' := fun _ _ => rfl
          map_zero' := rfl
          map_add' := fun _ _ => rfl }⟩ ρ

@[simp] lemma galoisRepULift_apply {K : Type*} [Field K] {A₀ : Type} [CommRing A₀]
    [TopologicalSpace A₀] {W : Type*} [AddCommGroup W] [Module A₀ W]
    (ρ : GaloisRep K A₀ W) (g : Field.absoluteGaloisGroup K) :
    galoisRepULift ρ g = endULiftRingEquiv A₀ W (ρ g) := rfl

/-- `ULift.up` as an `ULift A₀`-linear equivalence from `A₀` (with the
`ULift.down`-action) to `ULift A₀` (PROVEN, definitional). -/
def uliftUpLinearEquiv {A₀ : Type} [CommRing A₀] : A₀ ≃ₗ[ULift.{u} A₀] ULift.{u} A₀ where
  toFun := ULift.up
  invFun := ULift.down
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

/-- Coordinates of the `ULift`-relabeled basis (PROVEN, definitional):
`Basis.mapCoeffs` along `ULift.up` lifts each coordinate by `ULift.up`. -/
lemma mapCoeffs_uliftUp_repr {A₀ : Type} [CommRing A₀] {W : Type*} [AddCommGroup W]
    [Module A₀ W] {ι : Type*} (b : Module.Basis ι A₀ W) (x : W) (i : ι) :
    (b.mapCoeffs (ULift.ringEquiv : ULift.{u} A₀ ≃+* A₀).symm
        (fun _ _ => rfl)).repr x i = ULift.up (b.repr x i) :=
  rfl

/-- The matrix of a relabeled endomorphism in the relabeled basis is the
entrywise `ULift.up` of the original matrix (PROVEN). -/
lemma toMatrix_endULiftRingEquiv {A₀ : Type} [CommRing A₀] {W : Type*} [AddCommGroup W]
    [Module A₀ W] {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι A₀ W)
    (f : Module.End A₀ W) :
    LinearMap.toMatrix
        (b.mapCoeffs (ULift.ringEquiv : ULift.{u} A₀ ≃+* A₀).symm (fun _ _ => rfl))
        (b.mapCoeffs (ULift.ringEquiv : ULift.{u} A₀ ≃+* A₀).symm (fun _ _ => rfl))
        (endULiftRingEquiv A₀ W f)
      = (LinearMap.toMatrix b b f).map
          (ULift.ringEquiv : ULift.{u} A₀ ≃+* A₀).symm.toRingHom := by
  refine Matrix.ext fun i j => ?_
  rw [Matrix.map_apply, LinearMap.toMatrix_apply, LinearMap.toMatrix_apply,
    Module.Basis.mapCoeffs_apply]
  exact mapCoeffs_uliftUp_repr b (f (b j)) i

/-- The determinant of a relabeled endomorphism is the `ULift.up` of the
original determinant (PROVEN, via the relabeled basis). -/
lemma det_endULiftRingEquiv {A₀ : Type} [CommRing A₀] {W : Type*} [AddCommGroup W]
    [Module A₀ W] [Module.Finite A₀ W] [Module.Free A₀ W]
    (f : Module.End A₀ W) :
    LinearMap.det (endULiftRingEquiv A₀ W f)
      = (ULift.up (LinearMap.det f) : ULift.{u} A₀) := by
  classical
  show LinearMap.det (endULiftRingEquiv A₀ W f)
    = (ULift.ringEquiv : ULift.{u} A₀ ≃+* A₀).symm.toRingHom (LinearMap.det f)
  rw [← LinearMap.det_toMatrix (Module.Free.chooseBasis A₀ W) f, RingHom.map_det,
    RingHom.mapMatrix_apply,
    ← toMatrix_endULiftRingEquiv (Module.Free.chooseBasis A₀ W) f,
    LinearMap.det_toMatrix]

/-- The characteristic polynomial of a relabeled endomorphism is the
coefficientwise `ULift.up` of the original one (PROVEN, via the relabeled
basis and `Matrix.charpoly_map`). -/
lemma charpoly_endULiftRingEquiv {A₀ : Type} [CommRing A₀] {W : Type*} [AddCommGroup W]
    [Module A₀ W] [Module.Finite A₀ W] [Module.Free A₀ W]
    [Module.Finite (ULift.{u} A₀) W] [Module.Free (ULift.{u} A₀) W]
    (f : Module.End A₀ W) :
    (endULiftRingEquiv A₀ W f).charpoly
      = f.charpoly.map (ULift.ringEquiv : ULift.{u} A₀ ≃+* A₀).symm.toRingHom := by
  classical
  rw [← LinearMap.charpoly_toMatrix f (Module.Free.chooseBasis A₀ W),
    ← Matrix.charpoly_map,
    ← toMatrix_endULiftRingEquiv (Module.Free.chooseBasis A₀ W) f,
    LinearMap.charpoly_toMatrix]

/-- Unramifiedness transports along the `ULift` relabeling (PROVEN: the
kernels of the local representations coincide). -/
lemma isUnramifiedAt_galoisRepULift {A₀ : Type} [CommRing A₀] [TopologicalSpace A₀]
    {W : Type*} [AddCommGroup W] [Module A₀ W] (τ₀ : GaloisRep ℚ A₀ W)
    (v : HeightOneSpectrum (NumberField.RingOfIntegers ℚ)) [τ₀.IsUnramifiedAt v] :
    (galoisRepULift τ₀).IsUnramifiedAt v := by
  refine ⟨le_trans (GaloisRep.IsUnramifiedAt.localInertiaGroup_le (ρ := τ₀)) ?_⟩
  intro σ hσ
  have h1 : τ₀.toLocal v σ = 1 := hσ
  show (galoisRepULift τ₀).toLocal v σ = 1
  rw [GaloisRep.toLocal_apply, galoisRepULift_apply, ← GaloisRep.toLocal_apply, h1,
    map_one]

/-- Flatness transports along the `ULift` relabeling (PROVEN): open ideals
of `ULift A₀` pull back to open ideals of `A₀` along the (continuous)
`ULift.up`, the quotients are isomorphic via `Ideal.quotientEquiv`, and
the flat-prolongation witness transports through
`HasFlatProlongationAt.of_equiv` along the induced equivariant
identification of base-changed spaces (coefficient transport by
`TensorProduct.congr` plus base-ring relabeling by
`TensorProduct.equivOfCompatibleSMul`). -/
lemma isFlatAt_galoisRepULift {A₀ : Type} [CommRing A₀] [TopologicalSpace A₀]
    [IsTopologicalRing A₀] [IsLocalRing A₀] [IsLocalRing (ULift.{u} A₀)]
    {W : Type*} [AddCommGroup W] [Module A₀ W] [Module.Finite A₀ W] [Module.Free A₀ W]
    [Module.Finite (ULift.{u} A₀) W] [Module.Free (ULift.{u} A₀) W]
    (τ₀ : GaloisRep ℚ A₀ W)
    (v : HeightOneSpectrum (NumberField.RingOfIntegers ℚ))
    (h : τ₀.IsFlatAt v) : (galoisRepULift τ₀).IsFlatAt v := by
  constructor
  intro I hI
  -- pull the open ideal back to `A₀` along the (continuous) `ULift.up`
  have hI₀open : IsOpen ((I.comap ((ULift.ringEquiv : ULift.{u} A₀ ≃+* A₀).symm :
      A₀ ≃+* ULift.{u} A₀) : Ideal A₀) : Set A₀) := by
    rw [Ideal.coe_comap]
    exact hI.preimage continuous_uliftUp
  have h0 := h.cond (I.comap ((ULift.ringEquiv : ULift.{u} A₀ ≃+* A₀).symm :
    A₀ ≃+* ULift.{u} A₀)) hI₀open
  -- the induced isomorphism of quotient coefficient rings
  have hmapI : I = (I.comap ((ULift.ringEquiv : ULift.{u} A₀ ≃+* A₀).symm :
      A₀ ≃+* ULift.{u} A₀)).map (ULift.ringEquiv : ULift.{u} A₀ ≃+* A₀).symm :=
    (Ideal.map_comap_of_surjective _
      (ULift.ringEquiv : ULift.{u} A₀ ≃+* A₀).symm.surjective I).symm
  let q := Ideal.quotientEquiv _ I (ULift.ringEquiv : ULift.{u} A₀ ≃+* A₀).symm hmapI
  -- ... as an `A₀`-linear equivalence
  let qL : (A₀ ⧸ I.comap ((ULift.ringEquiv : ULift.{u} A₀ ≃+* A₀).symm :
        A₀ ≃+* ULift.{u} A₀)) ≃ₗ[A₀] (ULift.{u} A₀ ⧸ I) :=
    { q.toAddEquiv with
      map_smul' := fun c x => by
        show q (c • x) = c • q x
        rw [Algebra.smul_def, Algebra.smul_def, map_mul]
        congr 1 }
  -- scalar compatibility for the base-ring relabeling of the tensor product
  haveI : SMulCommClass A₀ (ULift.{u} A₀) (ULift.{u} A₀ ⧸ I) :=
    ⟨fun a x m => by simp only [Algebra.smul_def]; rw [mul_left_comm]⟩
  haveI : SMulCommClass A₀ A₀ (ULift.{u} A₀ ⧸ I) :=
    ⟨fun a b m => by simp only [Algebra.smul_def]; rw [mul_left_comm]⟩
  haveI : SMulCommClass (ULift.{u} A₀) A₀ (ULift.{u} A₀ ⧸ I) :=
    ⟨fun x a m => by simp only [Algebra.smul_def]; rw [mul_left_comm]⟩
  haveI : TensorProduct.CompatibleSMul A₀ (ULift.{u} A₀) (ULift.{u} A₀ ⧸ I) W :=
    ⟨fun x m w => by
      have hm : x • m = x.down • m := by
        rw [Algebra.smul_def, Algebra.smul_def]; rfl
      rw [hm, show x • w = x.down • w from rfl, TensorProduct.smul_tmul]⟩
  haveI : TensorProduct.CompatibleSMul (ULift.{u} A₀) A₀ (ULift.{u} A₀ ⧸ I) W :=
    ⟨fun a m w => by
      have hm : a • m = ULift.up a • m := by
        rw [Algebra.smul_def, Algebra.smul_def]; rfl
      rw [hm, show a • w = ULift.up a • w from rfl, TensorProduct.smul_tmul]⟩
  -- the equivariant identification of base-changed spaces
  refine h0.of_equiv _
    (((TensorProduct.congr qL (LinearEquiv.refl A₀ W)).toAddEquiv).trans
      (TensorProduct.equivOfCompatibleSMul A₀ (ULift.{u} A₀) A₀
        (ULift.{u} A₀ ⧸ I) W).symm.toAddEquiv) ?_
  intro g x
  show ((TensorProduct.equivOfCompatibleSMul A₀ (ULift.{u} A₀) A₀
      (ULift.{u} A₀ ⧸ I) W).symm
        ((TensorProduct.congr qL (LinearEquiv.refl A₀ W))
          (((τ₀.baseChange (A₀ ⧸ I.comap ((ULift.ringEquiv :
            ULift.{u} A₀ ≃+* A₀).symm : A₀ ≃+* ULift.{u} A₀))).toLocal v) g x)))
    = (((galoisRepULift τ₀).baseChange (ULift.{u} A₀ ⧸ I)).toLocal v) g
        ((TensorProduct.equivOfCompatibleSMul A₀ (ULift.{u} A₀) A₀
          (ULift.{u} A₀ ⧸ I) W).symm
            ((TensorProduct.congr qL (LinearEquiv.refl A₀ W)) x))
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => simp only [map_add, ha, hb]
  | tmul c w => rfl

/-- **Hardly-ramifiedness transports along the `ULift` relabeling**
(PROVEN, field by field): the determinant through
`det_endULiftRingEquiv` and the commuting triangle of structure maps,
unramifiedness through equality of local kernels, flatness through
`isFlatAt_galoisRepULift`, and tameness at `2` by lifting the projection
`π` and conjugating the quotient character by the `ULift.up` linear
equivalence. -/
lemma isHardlyRamified_galoisRepULift (hℓodd : Odd ℓ)
    {A₀ : Type} [CommRing A₀] [TopologicalSpace A₀] [IsTopologicalRing A₀]
    [IsLocalRing A₀] [Algebra ℤ_[ℓ] A₀] [IsLocalRing (ULift.{u} A₀)]
    {W : Type v} [AddCommGroup W] [Module A₀ W] [Module.Finite A₀ W]
    [Module.Free A₀ W]
    [Module.Finite (ULift.{u} A₀) W] [Module.Free (ULift.{u} A₀) W]
    {hW : Module.rank A₀ W = 2} (hW' : Module.rank (ULift.{u} A₀) W = 2)
    {τ₀ : GaloisRep ℚ A₀ W} (hτ₀ : IsHardlyRamified hℓodd hW τ₀) :
    IsHardlyRamified hℓodd hW' (galoisRepULift τ₀) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- cyclotomic determinant
    intro g
    rw [GaloisRep.det_apply, galoisRepULift_apply, det_endULiftRingEquiv,
      ← GaloisRep.det_apply, hτ₀.det g]
    rfl
  · -- unramified outside `2ℓ`
    intro q hq hq'
    haveI := hτ₀.isUnramified q hq hq'
    exact isUnramifiedAt_galoisRepULift τ₀ _
  · -- flat at `ℓ`
    exact isFlatAt_galoisRepULift τ₀ _ hτ₀.isFlat
  · -- tame at `2`
    obtain ⟨π₀, hπ₀, δ₀, hδ₀⟩ := hτ₀.isTameAtTwo
    refine ⟨{ toFun := fun w => ULift.up (π₀ w)
              map_add' := fun x y => by rw [map_add]; rfl
              map_smul' := fun c w => by
                show ULift.up (π₀ (c.down • w)) = c • ULift.up (π₀ w)
                rw [map_smul]
                rfl },
      fun a => (hπ₀ a.down).imp fun w hw => by
        show ULift.up (π₀ w) = a
        rw [hw],
      (galoisRepULift δ₀).conj uliftUpLinearEquiv, ?_⟩
    intro g w
    obtain ⟨h1, h2, h3⟩ := hδ₀ g w
    refine ⟨?_, ?_, ?_⟩
    · -- the projection intertwines the representations
      show ULift.up (π₀ (τ₀.map (algebraMap ℚ ℚ_[2]) g w))
        = ((galoisRepULift δ₀).conj uliftUpLinearEquiv) g (ULift.up (π₀ w))
      rw [h1]
      rfl
    · -- the quotient character is unramified
      intro σ hσ
      have hδσ : δ₀ σ = 1 := h2 hσ
      show ((galoisRepULift δ₀).conj uliftUpLinearEquiv) σ = 1
      rw [GaloisRep.conj_apply, galoisRepULift_apply, hδσ, map_one]
      refine LinearMap.ext fun x => ?_
      simp [LinearEquiv.conj_apply]
    · -- the quotient character squares to one
      intro g'
      have hsq := h3 g'
      calc ((galoisRepULift δ₀).conj uliftUpLinearEquiv) g'
            * ((galoisRepULift δ₀).conj uliftUpLinearEquiv) g'
          = ((galoisRepULift δ₀).conj uliftUpLinearEquiv) (g' * g') :=
            (map_mul _ _ _).symm
        _ = 1 := by
            rw [GaloisRep.conj_apply, galoisRepULift_apply, map_mul δ₀, hsq, map_one]
            refine LinearMap.ext fun x => ?_
            simp [LinearEquiv.conj_apply]

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
        (τ.charFrob v).map (algebraMap A (AlgebraicClosure ℚ_[ℓ])) = Q v := by
  classical
  -- the coefficient-ring package on `ULift.{u} A₀` (the algebra structure is
  -- mathlib's `ULift.algebra'`, whose scalar action is definitionally the
  -- `ULift.down`-action — no instance diamond against `ULift.module`)
  letI algU : Algebra (ULift.{u} A₀) (AlgebraicClosure ℚ_[ℓ]) :=
    ULift.algebra' A₀ (AlgebraicClosure ℚ_[ℓ])
  haveI locU : IsLocalRing (ULift.{u} A₀) :=
    IsLocalRing.of_surjective' (ULift.ringEquiv : ULift.{u} A₀ ≃+* A₀).symm.toRingHom
      (ULift.ringEquiv : ULift.{u} A₀ ≃+* A₀).symm.surjective
  haveI finU : Module.Finite ℤ_[ℓ] (ULift.{u} A₀) :=
    Module.Finite.equiv (ULift.moduleEquiv : ULift.{u} A₀ ≃ₗ[ℤ_[ℓ]] A₀).symm
  haveI towU : IsScalarTower ℤ_[ℓ] (ULift.{u} A₀) (AlgebraicClosure ℚ_[ℓ]) :=
    IsScalarTower.of_algebraMap_eq (S := ULift.{u} A₀) fun x =>
      IsScalarTower.algebraMap_apply ℤ_[ℓ] A₀ (AlgebraicClosure ℚ_[ℓ]) x
  haveI mtU : IsModuleTopology ℤ_[ℓ] (ULift.{u} A₀) :=
    IsModuleTopology.iso (R := ℤ_[ℓ])
      { toLinearEquiv := (ULift.moduleEquiv : ULift.{u} A₀ ≃ₗ[ℤ_[ℓ]] A₀).symm
        continuous_toFun := continuous_uliftUp
        continuous_invFun := continuous_uliftDown }
  have hinjU : Function.Injective
      (algebraMap (ULift.{u} A₀) (AlgebraicClosure ℚ_[ℓ])) := fun x y hxy =>
    ULift.down_injective (hA₀inj hxy)
  -- the module `W₀`, with the coefficients relabeled through `ULift.up`
  haveI finW : Module.Finite (ULift.{u} A₀) W₀ :=
    Module.Finite.of_basis ((Module.Free.chooseBasis A₀ W₀).mapCoeffs
      (ULift.ringEquiv : ULift.{u} A₀ ≃+* A₀).symm fun _ _ => rfl)
  haveI freeW : Module.Free (ULift.{u} A₀) W₀ :=
    Module.Free.of_basis ((Module.Free.chooseBasis A₀ W₀).mapCoeffs
      (ULift.ringEquiv : ULift.{u} A₀ ≃+* A₀).symm fun _ _ => rfl)
  have hWU : Module.rank (ULift.{u} A₀) W₀ = 2 := by
    rw [rank_eq_card_basis ((Module.Free.chooseBasis A₀ W₀).mapCoeffs
        (ULift.ringEquiv : ULift.{u} A₀ ≃+* A₀).symm fun _ _ => rfl),
      ← rank_eq_card_basis (Module.Free.chooseBasis A₀ W₀), hW₀]
  -- scalar compatibility for the base-ring relabeling of the framing (the
  -- `ULift A₀`-actions are definitionally the `ULift.down`-actions)
  haveI : SMulCommClass A₀ (ULift.{u} A₀) (AlgebraicClosure ℚ_[ℓ]) :=
    ⟨fun a x m => by
      change a • x.down • m = x.down • a • m
      rw [smul_smul, smul_smul, mul_comm]⟩
  haveI : TensorProduct.CompatibleSMul A₀ (ULift.{u} A₀)
      (AlgebraicClosure ℚ_[ℓ]) W₀ :=
    ⟨fun x m w => by
      change (x.down • m) ⊗ₜ[A₀] w = m ⊗ₜ[A₀] (x.down • w)
      rw [TensorProduct.smul_tmul]⟩
  haveI : TensorProduct.CompatibleSMul (ULift.{u} A₀) A₀
      (AlgebraicClosure ℚ_[ℓ]) W₀ :=
    ⟨fun a m w => by
      change ((ULift.up a) • m) ⊗ₜ[ULift.{u} A₀] w
        = m ⊗ₜ[ULift.{u} A₀] ((ULift.up a) • w)
      rw [TensorProduct.smul_tmul]⟩
  refine ⟨ULift.{u} A₀, inferInstance, inferInstance, inferInstance, locU,
    inferInstance, finU, algU, towU, mtU, hinjU, W₀, inferInstance, inferInstance,
    finW, freeW, hWU, galoisRepULift τ₀,
    (TensorProduct.equivOfCompatibleSMul A₀ (ULift.{u} A₀) (AlgebraicClosure ℚ_[ℓ])
        (AlgebraicClosure ℚ_[ℓ]) W₀) ≪≫ₗ r₀,
    isHardlyRamified_galoisRepULift hℓodd hWU hτ₀, ?_⟩
  intro w hwT hwℓ
  obtain ⟨hunr, hchar⟩ := hmatch w hwT hwℓ
  haveI := hunr
  refine ⟨isUnramifiedAt_galoisRepULift τ₀ w, ?_⟩
  have hcf : (galoisRepULift τ₀ : GaloisRep ℚ (ULift.{u} A₀) W₀).charFrob w
      = (τ₀.charFrob w).map
          (ULift.ringEquiv : ULift.{u} A₀ ≃+* A₀).symm.toRingHom := by
    show ((galoisRepULift τ₀).toLocal w
        (Field.AbsoluteGaloisGroup.adicArithFrob w)).charpoly = _
    rw [GaloisRep.toLocal_apply, galoisRepULift_apply, charpoly_endULiftRingEquiv]
    rfl
  rw [hcf, Polynomial.map_map,
    show ((algebraMap (ULift.{u} A₀) (AlgebraicClosure ℚ_[ℓ])).comp
        (ULift.ringEquiv : ULift.{u} A₀ ≃+* A₀).symm.toRingHom)
      = algebraMap A₀ (AlgebraicClosure ℚ_[ℓ]) from RingHom.ext fun x => rfl,
    hchar]

end ConcreteCoefficientRing

/-- **Attachment at odd residue characteristics, from a level-2
eigenform** (PROVEN via the dimension-formula route of the modularity
interface: `S₂(Γ₀(2)) = 0`, so the eigenform hypothesis `hf` is
contradictory — `Modularity.weightTwoEigenform_level_two_false`;
DECOMPOSITION PLAN item 3 of
`Fermat/FLT/Modularity/Interface.lean`. The non-vacuous reading,
Diamond–Shurman ch. 8–9, kept for the record): a normalized weight-2 eigenform of level `Γ₀(2)` matching the
eigensystem `(E, S, Pv)` yields, at every odd prime `ℓ` and embedding
`φ : E →+* ℚ̄_ℓ`, a HARDLY RAMIFIED representation over the ring of
integers `IntegralClosure ℤ_ℓ L` of a finite extension `L/ℚ_ℓ` whose
Frobenius characteristic polynomials map to `(Pv v).map φ` away from a
uniform finite `T` and the places over `ℓ`. This is Eichler–Shimura/
Deligne (the `λ`-adic representations of the newform of level dividing
2 underlying `f`, with the stabilized-lattice integral model over
`E_λ`'s ring of integers), plus Carayol–Saito local–global
compatibility, plus the level-2 weight-2 analysis giving the hardly
ramified shape — the LEVEL-2 hypothesis is what makes that last clause
sound for every inhabitant of the eigenform carrier (see the soundness
audit in `Fermat/FLT/Modularity/Interface.lean`): at a general level a
wildly-ramified-at-2 eigenform would falsify it. No `ρ` appears: the
statement is purely about the eigenform, which is what makes it an
interface node rather than a restatement of the consuming atom below.
Since `S₂(Γ₀(2)) = 0` (genus of `X₀(2)` is zero), this node is also
dischargeable through the dimension-formula route — DECOMPOSITION PLAN
item 3 of the interface file: no such `f` exists, `qCoeff_one`
refuting `f = 0`. -/
theorem exists_ringOfIntegers_realizations_of_weightTwoEigenform
    {E : Type v} [Field E] [NumberField E]
    (S : Finset (HeightOneSpectrum (NumberField.RingOfIntegers ℚ)))
    (Pv : HeightOneSpectrum (NumberField.RingOfIntegers ℚ) → Polynomial E)
    {f : CuspForm (Modularity.Gamma0GL 2) 2}
    (hf : Modularity.IsWeightTwoEigenform 2 f)
    (_hmatch : Modularity.MatchesEigensystem 2 f S Pv) :
    ∃ (T : Finset (HeightOneSpectrum (NumberField.RingOfIntegers ℚ))),
      ∀ (ℓ : ℕ) (_hℓ : Fact ℓ.Prime) (hℓodd : Odd ℓ)
        (φ : E →+* AlgebraicClosure ℚ_[ℓ]),
      ∃ (L : IntermediateField ℚ_[ℓ] (AlgebraicClosure ℚ_[ℓ]))
        (_ : FiniteDimensional ℚ_[ℓ] L)
        (W : Type v) (_ : AddCommGroup W)
        (_ : Module (IntegralClosure ℤ_[ℓ] L) W)
        (_ : Module.Finite (IntegralClosure ℤ_[ℓ] L) W)
        (_ : Module.Free (IntegralClosure ℤ_[ℓ] L) W)
        (hW : Module.rank (IntegralClosure ℤ_[ℓ] L) W = 2)
        (τ : GaloisRep ℚ (IntegralClosure ℤ_[ℓ] L) W)
        (_r : AlgebraicClosure ℚ_[ℓ] ⊗[IntegralClosure ℤ_[ℓ] L] W
          ≃ₗ[AlgebraicClosure ℚ_[ℓ]] Fin 2 → AlgebraicClosure ℚ_[ℓ]),
        IsHardlyRamified hℓodd hW τ ∧
        ∀ v ∉ T, (ℓ : NumberField.RingOfIntegers ℚ) ∉ v.asIdeal →
          τ.IsUnramifiedAt v ∧
          (τ.charFrob v).map
              (algebraMap (IntegralClosure ℤ_[ℓ] L) (AlgebraicClosure ℚ_[ℓ])) =
            (Pv v).map φ :=
  (Modularity.weightTwoEigenform_level_two_false f hf).elim

/-! ### The explicit Eisenstein member `1 ⊕ χ_cyc`

Infrastructure for the two REDUCIBLE-branch realization leaves
(`exists_hardlyRamified_ringOfIntegers_realizations_of_not_isIrreducible`
and `exists_realization_at_two_generated_of_not_isIrreducible` below):
by the PROVEN reducibility analysis
(`exists_char_charpoly_map_eq_of_not_isIrreducible`) and the Eisenstein
character dichotomy (`char_add_char_eq_one_add_cyclotomicCharacter`),
the eigensystem of a reducible hardly ramified member degenerates to
`Pv v = (X - 1)(X - q)` with coefficients in the PRIME FIELD away from
`S ∪ {p}` (`eisenstein_Pv_eq_of_not_isIrreducible` below), so it is
realized at every residue characteristic by the explicit DIAGONAL
member `1 ⊕ χ_cyc,ℓ` — built here over any topological `ℤ_ℓ`-algebra
with continuous structure map, on any rank-2 carrier with a chosen
basis. Its Frobenius characteristic polynomial at `q ≠ ℓ` is exactly
`(X - 1)(X - q)` (PROVEN via `cyclotomicCharacter_adicArithFrob_natCast`),
it is unramified at every `q ≠ ℓ` (PROVEN, via
`cyclotomicCharacter_eq_one_of_mem_localInertiaGroup_of_ne`:
`μ_{ℓ^∞}/ℚ` is unramified away from `ℓ`), and over the concrete rings
of integers it is hardly ramified (cyclotomic determinant and tameness
at `2` with TRIVIAL quotient character both PROVEN; flatness at `ℓ` as
the Tate module of `μ_{ℓ^∞} × ℚ_ℓ/ℤ_ℓ` is `isFlatAt_cycDiagRep`, PROVEN
2026-07-25 over three group-scheme leaves — see the section note
before it).

SOUNDNESS AUDIT (2026-07-24, the reducible-but-INDECOMPOSABLE
subtlety): a reducible hardly ramified member may itself be a
nontrivial extension of `χ_cyc` by `1` (or vice versa), NOT isomorphic
to this diagonal model. This threatens nothing: the realization leaves
only demand SOME hardly ramified representation whose Frobenius
characteristic polynomials match the eigensystem away from finitely
many places — no integral model of `ρ` itself, and no isomorphism with
`ρ`'s base change. The characteristic-polynomial data of an extension
agrees everywhere with that of its semisimplification, so the diagonal
member realizes exactly the same eigensystem and the statements are
TRUE as written for extension classes too. -/

section EisensteinDiagonal

/-- The `ℓ`-adic cyclotomic character of `G_ℚ`, pushed into a
`ℤ_ℓ`-algebra `A` (PROVEN layer): the scalar by which the second
diagonal entry of the explicit Eisenstein member `1 ⊕ χ_cyc,ℓ` acts. -/
noncomputable def cycUnitChar (ℓ : ℕ) [Fact ℓ.Prime] (A : Type*) [CommRing A]
    [Algebra ℤ_[ℓ] A] (g : Field.absoluteGaloisGroup ℚ) : A :=
  algebraMap ℤ_[ℓ] A
    ((cyclotomicCharacter (AlgebraicClosure ℚ) ℓ g.toRingEquiv : ℤ_[ℓ]ˣ) : ℤ_[ℓ])

/-- `cycUnitChar` is unital (PROVEN). -/
lemma cycUnitChar_one {ℓ : ℕ} [Fact ℓ.Prime] (A : Type*) [CommRing A]
    [Algebra ℤ_[ℓ] A] : cycUnitChar ℓ A 1 = 1 := by
  have h1 : (1 : Field.absoluteGaloisGroup ℚ).toRingEquiv = 1 := rfl
  simp [cycUnitChar, h1]

/-- `cycUnitChar` is multiplicative (PROVEN). -/
lemma cycUnitChar_mul {ℓ : ℕ} [Fact ℓ.Prime] (A : Type*) [CommRing A]
    [Algebra ℤ_[ℓ] A] (g h : Field.absoluteGaloisGroup ℚ) :
    cycUnitChar ℓ A (g * h) = cycUnitChar ℓ A g * cycUnitChar ℓ A h := by
  have h1 : (g * h).toRingEquiv = g.toRingEquiv * h.toRingEquiv := rfl
  simp [cycUnitChar, h1]

/-- `cycUnitChar` is continuous whenever the structure map is (PROVEN:
mathlib's `cyclotomicCharacter.continuous` against the Krull topology
on `G_ℚ`). -/
lemma continuous_cycUnitChar {ℓ : ℕ} [Fact ℓ.Prime] (A : Type*) [CommRing A]
    [TopologicalSpace A] [Algebra ℤ_[ℓ] A]
    (hcont : Continuous (algebraMap ℤ_[ℓ] A)) :
    Continuous (cycUnitChar ℓ A) := by
  have h1 := cyclotomicCharacter.continuous ℓ ℚ (AlgebraicClosure ℚ)
  exact (hcont.comp (Units.continuous_val.comp h1)).congr fun g => rfl

/-- The diagonal endomorphism `diag(1, a)` in a chosen basis (PROVEN
layer): the value of the explicit Eisenstein member at a group element
acting through the scalar `a`. -/
noncomputable def cycDiagEnd {A : Type*} [CommRing A] {W : Type*} [AddCommGroup W]
    [Module A W] (b : Module.Basis (Fin 2) A W) (a : A) : Module.End A W :=
  Matrix.toLin b b (Matrix.diagonal ![1, a])

/-- `diag(1, 1) = 1` (PROVEN). -/
lemma cycDiagEnd_one {A : Type*} [CommRing A] {W : Type*} [AddCommGroup W]
    [Module A W] (b : Module.Basis (Fin 2) A W) : cycDiagEnd b 1 = 1 := by
  rw [cycDiagEnd]
  have h : ![(1 : A), 1] = fun _ => 1 := by funext i; fin_cases i <;> simp
  rw [h, Matrix.diagonal_one, Matrix.toLin_one]
  rfl

/-- `diag(1, a) * diag(1, c) = diag(1, ac)` (PROVEN). -/
lemma cycDiagEnd_mul {A : Type*} [CommRing A] {W : Type*} [AddCommGroup W]
    [Module A W] (b : Module.Basis (Fin 2) A W) (a c : A) :
    cycDiagEnd b a * cycDiagEnd b c = cycDiagEnd b (a * c) := by
  show (Matrix.toLin b b _).comp (Matrix.toLin b b _) = _
  rw [cycDiagEnd, ← Matrix.toLin_mul, Matrix.diagonal_mul_diagonal]
  congr 2
  funext i
  fin_cases i <;> simp

/-- `diag(1, a)` is a constant plus `a` times a constant (PROVEN): the
decomposition giving continuity of the Eisenstein member in the module
topology on endomorphisms. -/
lemma cycDiagEnd_eq_add_smul {A : Type*} [CommRing A] {W : Type*} [AddCommGroup W]
    [Module A W] (b : Module.Basis (Fin 2) A W) (a : A) :
    cycDiagEnd b a = Matrix.toLin b b (Matrix.diagonal ![1, 0]) +
      a • Matrix.toLin b b (Matrix.diagonal ![0, 1]) := by
  rw [cycDiagEnd, ← map_smul, ← map_add]
  congr 1
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal]

/-- The characteristic polynomial of `diag(1, a)` is `(X - 1)(X - a)`
(PROVEN). -/
lemma charpoly_cycDiagEnd {A : Type*} [CommRing A] {W : Type*} [AddCommGroup W]
    [Module A W] [Module.Finite A W] [Module.Free A W]
    (b : Module.Basis (Fin 2) A W) (a : A) :
    (cycDiagEnd b a).charpoly =
      (Polynomial.X - Polynomial.C 1) * (Polynomial.X - Polynomial.C a) := by
  rw [cycDiagEnd, ← LinearMap.charpoly_toMatrix _ b, LinearMap.toMatrix_toLin,
    Matrix.charpoly_diagonal, Fin.prod_univ_two]
  simp

/-- The determinant of `diag(1, a)` is `a` (PROVEN). -/
lemma det_cycDiagEnd {A : Type*} [CommRing A] {W : Type*} [AddCommGroup W]
    [Module A W] (b : Module.Basis (Fin 2) A W) (a : A) :
    LinearMap.det (cycDiagEnd b a) = a := by
  rw [cycDiagEnd, LinearMap.det_toLin, Matrix.det_diagonal, Fin.prod_univ_two]
  simp

/-- `diag(1, a)` acts trivially on the first coordinate (PROVEN): the
tame-at-two quotient of the Eisenstein member is the TRIVIAL character. -/
lemma coord_zero_cycDiagEnd {A : Type*} [CommRing A] {W : Type*} [AddCommGroup W]
    [Module A W] (b : Module.Basis (Fin 2) A W) (a : A) (w : W) :
    b.coord 0 (cycDiagEnd b a w) = b.coord 0 w := by
  simp [cycDiagEnd, Matrix.toLin_apply, Matrix.mulVec, Matrix.diagonal, Fin.sum_univ_two,
    dotProduct]

/-- **The explicit Eisenstein member `1 ⊕ χ_cyc,ℓ`** (PROVEN
construction): the diagonal Galois representation acting by `1` on the
first basis vector and by the `ℓ`-adic cyclotomic character on the
second, over any topological `ℤ_ℓ`-algebra whose structure map is
continuous, on any carrier with a chosen rank-2 basis. Continuity is
the decomposition `cycDiagEnd_eq_add_smul` against the continuity of
the module topology's operations. -/
noncomputable def cycDiagRep {ℓ : ℕ} [Fact ℓ.Prime] {A : Type*} [CommRing A]
    [TopologicalSpace A] [IsTopologicalRing A] [Algebra ℤ_[ℓ] A]
    {W : Type*} [AddCommGroup W] [Module A W]
    (hcont : Continuous (algebraMap ℤ_[ℓ] A)) (b : Module.Basis (Fin 2) A W) :
    GaloisRep ℚ A W :=
  letI := moduleTopology A (Module.End A W)
  haveI : ContinuousAdd (Module.End A W) := ModuleTopology.continuousAdd A _
  haveI : ContinuousSMul A (Module.End A W) := ModuleTopology.continuousSMul A _
  { toFun := fun g => cycDiagEnd b (cycUnitChar ℓ A g)
    map_one' := by rw [cycUnitChar_one, cycDiagEnd_one]
    map_mul' := fun g h => by rw [cycUnitChar_mul, ← cycDiagEnd_mul]
    continuous_toFun := by
      simp only [cycDiagEnd_eq_add_smul]
      exact continuous_const.add ((continuous_cycUnitChar A hcont).smul continuous_const) }

/-- Evaluation of the Eisenstein member (PROVEN, definitional). -/
lemma cycDiagRep_apply {ℓ : ℕ} [Fact ℓ.Prime] {A : Type*} [CommRing A]
    [TopologicalSpace A] [IsTopologicalRing A] [Algebra ℤ_[ℓ] A]
    {W : Type*} [AddCommGroup W] [Module A W]
    (hcont : Continuous (algebraMap ℤ_[ℓ] A)) (b : Module.Basis (Fin 2) A W)
    (g : Field.absoluteGaloisGroup ℚ) :
    cycDiagRep hcont b g = cycDiagEnd b (cycUnitChar ℓ A g) := rfl

/-- **The `ℓ`-adic cyclotomic character dies on inertia away from `ℓ`**
(PROVEN 2026-07-25 by delegation to
`Modularity.cyclotomicCharacter_map_eq_one_of_mem_localInertiaGroup` of
`Fermat/FLT/Modularity/Interface.lean`, which is this statement in the
same place spelling with the section prime `p` playing the role of `ℓ`
and the inequality written `p ≠ q`): at
a rational prime `q ≠ ℓ` the `ℓ`-adic cyclotomic character kills the
image in `G_ℚ` of the local inertia at `q` — the extensions
`ℚ_q(μ_{ℓ^n})/ℚ_q` are unramified for `q ≠ ℓ`. Proof there (as
anticipated here): the
inertia analogue of the PROVEN Frobenius computation
`adicArithFrob_rootsOfUnity_pow_of_ne` above, sharing all its
infrastructure: an `ℓ^n`-th root of unity `ζ` is integral over the
completion integers at `q` (it kills `X^{ℓ^n} - 1`), distinct `ℓ^n`-th
roots of unity have UNIT difference in residue characteristic `q ≠ ℓ`
(their difference divides `ℓ^{ℓ^n}`, a `q`-adic unit, cf.
`valued_natCast_adicCompletionIntegers_eq_one_of_ne`), and an inertia
element fixes the residue field of the integral closure, so it fixes
`ζ` itself; then every level `toZModPow n` of the character is trivial
(`modularCyclotomicCharacter.unique` with the trivial action) and
`ℓ`-adic continuity (`PadicInt.ext_of_toZModPow`) concludes. This is
the general-`(q, ℓ)` place-spelled form of the at-`2` statement
`cyclotomicCharacter_eq_one_of_mem_inertia_two` above (which is
spelled over `ℚ_[2]`/`Z2bar` instead and is separately PROVEN). -/
theorem cyclotomicCharacter_eq_one_of_mem_localInertiaGroup_of_ne
    {ℓ q : ℕ} [Fact ℓ.Prime] (hq : q.Prime) (hqℓ : q ≠ ℓ)
    (σ : Field.absoluteGaloisGroup (HeightOneSpectrum.adicCompletion ℚ
      hq.toHeightOneSpectrumRingOfIntegersRat))
    (hσ : σ ∈ localInertiaGroup hq.toHeightOneSpectrumRingOfIntegersRat) :
    cyclotomicCharacter (AlgebraicClosure ℚ) ℓ
      ((Field.absoluteGaloisGroup.map (algebraMap ℚ (HeightOneSpectrum.adicCompletion ℚ
        hq.toHeightOneSpectrumRingOfIntegersRat)) σ).toRingEquiv) = 1 :=
  Modularity.cyclotomicCharacter_map_eq_one_of_mem_localInertiaGroup
    (p := ℓ) hq (Ne.symm hqℓ) hσ

/-- The Eisenstein member is unramified at every `q ≠ ℓ` (PROVEN over
the arithmetic leaf `cyclotomicCharacter_eq_one_of_mem_localInertiaGroup_of_ne`:
the diagonal value `diag(1, χ_cyc(σ))` at an inertia element is
`diag(1, 1) = 1`). -/
theorem isUnramifiedAt_cycDiagRep_of_ne {ℓ : ℕ} [Fact ℓ.Prime] {A : Type*}
    [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [Algebra ℤ_[ℓ] A]
    {W : Type*} [AddCommGroup W] [Module A W]
    (hcont : Continuous (algebraMap ℤ_[ℓ] A)) (b : Module.Basis (Fin 2) A W)
    {q : ℕ} (hq : q.Prime) (hqℓ : q ≠ ℓ) :
    (cycDiagRep hcont b).IsUnramifiedAt hq.toHeightOneSpectrumRingOfIntegersRat := by
  refine ⟨fun σ hσ => ?_⟩
  show (cycDiagRep hcont b).toLocal hq.toHeightOneSpectrumRingOfIntegersRat σ = 1
  rw [GaloisRep.toLocal_apply, cycDiagRep_apply]
  -- the value at the (freshly spelled) global image of `σ` is `1`
  have h2 : cycUnitChar ℓ A (Field.absoluteGaloisGroup.map (algebraMap ℚ
      (HeightOneSpectrum.adicCompletion ℚ hq.toHeightOneSpectrumRingOfIntegersRat)) σ) = 1 := by
    rw [cycUnitChar, cyclotomicCharacter_eq_one_of_mem_localInertiaGroup_of_ne hq hqℓ σ hσ,
      Units.val_one, map_one]
  have h3 : cycDiagEnd b (cycUnitChar ℓ A (Field.absoluteGaloisGroup.map (algebraMap ℚ
      (HeightOneSpectrum.adicCompletion ℚ hq.toHeightOneSpectrumRingOfIntegersRat)) σ)) =
      (1 : Module.End A W) := by
    rw [h2, cycDiagEnd_one]
  -- bridge the `toLocal` spelling of the coefficient embedding to the fresh
  -- one (they differ only in the subsingleton `Algebra ℚ _` instance)
  convert h3 using 5
  exact Subsingleton.elim _ _

/-- **Frobenius characteristic polynomials of the Eisenstein member**
(PROVEN): at every prime `q ≠ ℓ` the characteristic polynomial of the
Frobenius under `1 ⊕ χ_cyc,ℓ` is exactly `(X - 1)(X - q)`, by the
proven cyclotomic evaluation `cyclotomicCharacter_adicArithFrob_natCast`. -/
theorem charFrob_cycDiagRep_of_ne {ℓ : ℕ} [Fact ℓ.Prime] {A : Type*}
    [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [Algebra ℤ_[ℓ] A]
    {W : Type*} [AddCommGroup W] [Module A W] [Module.Finite A W] [Module.Free A W]
    (hcont : Continuous (algebraMap ℤ_[ℓ] A)) (b : Module.Basis (Fin 2) A W)
    {q : ℕ} (hq : q.Prime) (hqℓ : q ≠ ℓ) :
    (cycDiagRep hcont b).charFrob hq.toHeightOneSpectrumRingOfIntegersRat =
      (Polynomial.X - Polynomial.C 1) * (Polynomial.X - Polynomial.C (q : A)) := by
  rw [show (cycDiagRep hcont b).charFrob hq.toHeightOneSpectrumRingOfIntegersRat =
    ((cycDiagRep hcont b).toLocal hq.toHeightOneSpectrumRingOfIntegersRat
      (Field.AbsoluteGaloisGroup.adicArithFrob
        hq.toHeightOneSpectrumRingOfIntegersRat)).charpoly from rfl,
    GaloisRep.toLocal_apply, cycDiagRep_apply, charpoly_cycDiagEnd]
  -- the character value at the (freshly spelled) global Frobenius image is `q`
  have hval : cycUnitChar ℓ A (Field.absoluteGaloisGroup.map (algebraMap ℚ
      (HeightOneSpectrum.adicCompletion ℚ hq.toHeightOneSpectrumRingOfIntegersRat))
      (Field.AbsoluteGaloisGroup.adicArithFrob
        hq.toHeightOneSpectrumRingOfIntegersRat)) = (q : A) := by
    rw [cycUnitChar, cyclotomicCharacter_adicArithFrob_natCast hq hqℓ, map_natCast]
  have h3 : (Polynomial.X - Polynomial.C 1) * (Polynomial.X - Polynomial.C
      (cycUnitChar ℓ A (Field.absoluteGaloisGroup.map (algebraMap ℚ
        (HeightOneSpectrum.adicCompletion ℚ hq.toHeightOneSpectrumRingOfIntegersRat))
        (Field.AbsoluteGaloisGroup.adicArithFrob
          hq.toHeightOneSpectrumRingOfIntegersRat)))) =
      (Polynomial.X - Polynomial.C 1) * (Polynomial.X - Polynomial.C (q : A)) := by
    rw [hval]
  -- bridge the `toLocal` spelling of the coefficient embedding to the fresh
  -- one (subsingleton `Algebra ℚ _` instance)
  convert h3 using 7
  exact Subsingleton.elim _ _

/-- The trivial rank-one Galois representation over `A` (PROVEN layer):
the tame-at-two quotient character of the Eisenstein member — the
first diagonal entry of `diag(1, χ_cyc)` is `1`. Elaborated in this
generic context (instance synthesis at the `IntegralClosure` type
synonym is unreliable inside tactic blocks; binders sidestep it, the
pattern of `isModuleTopology_of_compactSpace_t2Space` above). -/
noncomputable def trivialQuotChar (K : Type*) [Field K] (A : Type*) [CommRing A]
    [TopologicalSpace A] : GaloisRep K A A :=
  letI := moduleTopology A (Module.End A A)
  { toMonoidHom := 1
    continuous_toFun := continuous_const }

/-! #### The two group-scheme factors of the Eisenstein member

`isFlatAt_cycDiagRep` below asks for a finite flat group scheme over
`ℤ_ℓ` prolonging every open reduction `(𝒪/I)²` of the diagonal member
`1 ⊕ χ_cyc,ℓ`. That group scheme is a PRODUCT of the two diagonal
factors,

  `(𝒪/I)_const  ×  μ_{𝒪/I}`,

the CONSTANT group scheme on the finite abelian group `𝒪/I` (which
carries the TRIVIAL Galois action — the first diagonal entry) and the
DIAGONALIZABLE group scheme `Spec 𝒪ᵥ[D]`, `D = Hom(𝒪/I, ℚ̄ˣ)`, whose
`ℚ̄`-points are `Hom(D, ℚ̄ˣ) ≅ 𝒪/I` by character BIDUALITY
(`CommGroup.monoidHomMonoidHomEquiv`) with the Galois action given by
raising roots of unity to the power `χ_cyc(σ)` — the second diagonal
entry.

The layer below cuts the leaf along exactly that decomposition, into
three group-scheme leaves — a PRODUCT transport
(`hasFlatProlongationAt_of_prod`), the CONSTANT factor
(`hasFlatProlongationAt_trivialQuotChar`) and the `μ`-FACTOR
(`hasFlatProlongationAt_cycScalarRep`). Everything else is PROVEN
here: finiteness of the open quotients
(`finite_quotient_of_isOpen_integralClosure`, over compactness of the
concrete ring of integers), the identification of the base change with
the diagonal member over `𝒪/I`, the splitting of the diagonal member
into its two entries (`hasFlatProlongationAt_cycDiagRep`) and the
assembly.

MISSING MACHINERY, in dependency order (2026-07-25 survey of this
mathlib pin). Mathlib HAS: the group-algebra Hopf structure
`MonoidAlgebra.instHopfAlgebra` (the diagonalizable group scheme) with
`MonoidAlgebra.lift` for its points; character biduality for finite
abelian groups, `CommGroup.monoidHomMonoidHomEquiv : ((G →* Mˣ) →* Mˣ)
≃* G` under `HasEnoughRootsOfUnity M (Monoid.exponent G)`, together
with the evaluation description `monoidHomMonoidHomEquiv_symm_apply_apply`;
étale-ness of finite products (the `Algebra.Etale R (Π i, A i)`
instance of `Mathlib/RingTheory/Etale/Pi.lean`), of base changes and of
composites; and the Hopf structure on a tensor product. Mathlib does
NOT have the Hopf algebra of FUNCTIONS on a finite group — the
constant group scheme. That is the one genuinely absent object: there
is a `Pi.instCoalgebra`, but it is the COMPONENTWISE structure, not
the one dual to the group law, so a type synonym carrying
`Bialgebra`/`HopfAlgebra` with `comul (e_g) = Σ_{ab = g} e_a ⊗ e_b`
has to be built (the needed algebra equivalence
`(G → R) ⊗[R] (G → R) ≃ₐ[R] (G × G → R)` for `G` finite is
`Algebra.TensorProduct.piScalarRight` plus currying).

BUILT 2026-07-26 as `GroupFunctions`, in
`Fermat/FLT/Mathlib/RingTheory/HopfAlgebra/GroupFunctions.lean`, together with
its points package (`GroupFunctions.pointsMulEquiv`,
`GroupFunctions.exists_eq_pointAlgHom`, `GroupFunctions.comp_pointAlgHom`) and
its generic fibre (`GroupFunctions.baseChangeAlgEquiv`); the CONSTANT factor
`hasFlatProlongationAt_trivialQuotChar` is PROVEN from it. The object is stated
for an arbitrary finite group `G` over an arbitrary commutative ring `R`, so it
is reusable — in particular by the `μ`-factor's Cartier-dual bookkeeping. -/

/-- **The rank-one cyclotomic member `χ_cyc,ℓ`** (PROVEN construction):
the second diagonal entry of `1 ⊕ χ_cyc,ℓ`, isolated as a
representation in its own right so that the flat-prolongation package
of the diagonal member splits as a product of the constant and the
`μ`-typed group scheme. Continuity is `continuous_cycUnitChar` against
the module topology on `Module.End B B`. -/
noncomputable def cycScalarRep {ℓ : ℕ} [Fact ℓ.Prime] {B : Type*} [CommRing B]
    [TopologicalSpace B] [IsTopologicalRing B] [Algebra ℤ_[ℓ] B]
    (hcont : Continuous (algebraMap ℤ_[ℓ] B)) : GaloisRep ℚ B B :=
  letI := moduleTopology B (Module.End B B)
  haveI : ContinuousAdd (Module.End B B) := ModuleTopology.continuousAdd B _
  haveI : ContinuousSMul B (Module.End B B) := ModuleTopology.continuousSMul B _
  { toFun := fun g => (cycUnitChar ℓ B g) • (LinearMap.id : Module.End B B)
    map_one' := by rw [cycUnitChar_one, one_smul]
    map_mul' := fun g h => by
      rw [cycUnitChar_mul]
      ext x
      simp [mul_smul, mul_comm]
    continuous_toFun := (continuous_cycUnitChar B hcont).smul continuous_const }

/-- Evaluation of the rank-one cyclotomic member (PROVEN,
definitional). -/
lemma cycScalarRep_apply {ℓ : ℕ} [Fact ℓ.Prime] {B : Type*} [CommRing B]
    [TopologicalSpace B] [IsTopologicalRing B] [Algebra ℤ_[ℓ] B]
    (hcont : Continuous (algebraMap ℤ_[ℓ] B)) (g : Field.absoluteGaloisGroup ℚ) (x : B) :
    cycScalarRep hcont g x = cycUnitChar ℓ B g • x := rfl

/-- `cycUnitChar` is compatible with a tower of `ℤ_ℓ`-algebras (PROVEN):
its value downstairs is the image of its value upstairs. -/
lemma cycUnitChar_algebraMap {ℓ : ℕ} [Fact ℓ.Prime] {A B : Type*} [CommRing A] [CommRing B]
    [Algebra ℤ_[ℓ] A] [Algebra A B] [Algebra ℤ_[ℓ] B] [IsScalarTower ℤ_[ℓ] A B]
    (g : Field.absoluteGaloisGroup ℚ) :
    cycUnitChar ℓ B g = algebraMap A B (cycUnitChar ℓ A g) := by
  rw [cycUnitChar, cycUnitChar, ← IsScalarTower.algebraMap_apply]

/-- `diag(1, a)` fixes the first basis vector (PROVEN). -/
lemma cycDiagEnd_apply_basis_zero {A : Type*} [CommRing A] {W : Type*} [AddCommGroup W]
    [Module A W] (b : Module.Basis (Fin 2) A W) (a : A) :
    cycDiagEnd b a (b 0) = b 0 := by
  rw [cycDiagEnd, Matrix.toLin_self, Fin.sum_univ_two]
  simp [Matrix.diagonal]

/-- `diag(1, a)` scales the second basis vector by `a` (PROVEN). -/
lemma cycDiagEnd_apply_basis_one {A : Type*} [CommRing A] {W : Type*} [AddCommGroup W]
    [Module A W] (b : Module.Basis (Fin 2) A W) (a : A) :
    cycDiagEnd b a (b 1) = a • b 1 := by
  rw [cycDiagEnd, Matrix.toLin_self, Fin.sum_univ_two]
  simp [Matrix.diagonal]

/-- **Flat prolongations of a PRODUCT** (sorry leaf; the group-scheme
product): if `ρ₁` and `ρ₂` have flat prolongations at `v` and the space
of `ρ` is, equivariantly, the product of their spaces, then `ρ` has one
too. Intended proof: the witnessing Hopf orders `G₁, G₂` over `𝒪ᵥ` are
combined into `G₁ ⊗[𝒪ᵥ] G₂` (mathlib's `HopfAlgebra S (B ⊗[R] A)`
instance; finite and flat because each factor is), whose generic fibre
`Kᵥ ⊗ (G₁ ⊗ G₂) ≃ₐ[Kᵥ] (Kᵥ ⊗ G₁) ⊗[Kᵥ] (Kᵥ ⊗ G₂)` is étale by
`Algebra.Etale.baseChange` + `Algebra.Etale.comp`, and whose
`Kᵥᵃˡᵍ`-points are the PRODUCT of the two point groups
(`Algebra.TensorProduct.lift`, with the convolution product of the
tensor Hopf algebra computing componentwise because
`comul_{G₁ ⊗ G₂} = tensorTensorTensorComm ∘ (comul ⊗ comul)`). The
`Γ Kᵥ`-action is postcomposition on both factors, so the splitting is
equivariant and `Additive` of it is the required additive
isomorphism. -/
theorem hasFlatProlongationAt_of_prod
    {v : HeightOneSpectrum (NumberField.RingOfIntegers ℚ)}
    {A₁ : Type*} [CommRing A₁] [TopologicalSpace A₁]
    {M₁ : Type*} [AddCommGroup M₁] [Module A₁ M₁]
    {A₂ : Type*} [CommRing A₂] [TopologicalSpace A₂]
    {M₂ : Type*} [AddCommGroup M₂] [Module A₂ M₂]
    {ρ₁ : GaloisRep ℚ A₁ M₁} {ρ₂ : GaloisRep ℚ A₂ M₂}
    (h₁ : ρ₁.HasFlatProlongationAt v) (h₂ : ρ₂.HasFlatProlongationAt v)
    {A : Type*} [CommRing A] [TopologicalSpace A]
    {M : Type*} [AddCommGroup M] [Module A M]
    (ρ : GaloisRep ℚ A M) (e : (M₁ × M₂) ≃+ M)
    (he : ∀ (σ : Field.absoluteGaloisGroup ℚ) (x : M₁ × M₂),
      e (ρ₁ σ x.1, ρ₂ σ x.2) = ρ σ (e x)) :
    ρ.HasFlatProlongationAt v :=
  sorry

/-- **The CONSTANT group scheme, over a general base** (PROVEN): a Galois
representation of a number field `K` on a FINITE coefficient ring `B` with
TRIVIAL action has a flat prolongation at every place. The witness is the
constant group scheme on the finite abelian group `B`, produced by base change
from the auxiliary base `R`: the Hopf algebra

  `H := GroupFunctions R (Multiplicative B)`

of `R`-valued functions on `B` with `comul (e_g) = Σ_{a + b = g} e_a ⊗ e_b`,
`counit f = f 0`, antipode `f ↦ f ∘ (-·)`
(`Fermat/FLT/Mathlib/RingTheory/HopfAlgebra/GroupFunctions.lean`; the object was
ABSENT FROM MATHLIB on this pin — `Pi.instCoalgebraStruct` is the componentwise
coalgebra, not the one dual to the group law — and was built there). The three
inputs of `GaloisRep.hasFlatProlongationAt_of_hopf_package` are then:

* `H` is finite free over `R` on the indicator basis `e_g`, hence flat;
* its generic fibre is `K ⊗[R] H ≃ₐ[K] (B → K)`
  (`GroupFunctions.baseChangeAlgEquiv`), a finite product of copies of `K`,
  hence étale by `Algebra.FormallyEtale`'s finite-product instance;
* its `Kᵃˡᵍ`-points are the evaluations `f ↦ f g`, one for each `g : B`
  (`GroupFunctions.exists_eq_pointAlgHom`, over `R`, transported to `K ⊗[R] H`
  through the convolution-compatible tensor–hom adjunction `AlgHom.liftEquiv`
  and `liftEquiv_convMul`), their convolution product is the group law of `B`
  (`GroupFunctions.pointAlgHom_convMul`), and `Γ K` acts TRIVIALLY on them
  because each takes its values in the image of `R`
  (`GroupFunctions.comp_pointAlgHom`) — which is exactly the trivial action of
  `trivialQuotChar`.

Stated over a general `K` deliberately: at `K = ℚ` the literal `ℚ` makes
instance search return `DivisionRing.toRatAlgebra` for `Algebra ℚ ℚ̄` where the
flat-prolongation package uses `AlgebraicClosure.instAlgebra ℚ`, and the
resulting `Algebra`/`CommSemiring` mismatches break `AlgHom.liftEquiv`
elaboration. With `K` abstract there is nothing to mismatch, and the
instantiation below fixes the instances by unification. -/
theorem hasFlatProlongationAt_trivialQuotChar_of_base
    {K : Type u} [Field K] [NumberField K]
    (v : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (R : Type u) [CommRing R] [Algebra R K]
    [Algebra R (HeightOneSpectrum.adicCompletionIntegers K v)]
    [Algebra R (HeightOneSpectrum.adicCompletion K v)]
    [IsScalarTower R (HeightOneSpectrum.adicCompletionIntegers K v)
      (HeightOneSpectrum.adicCompletion K v)]
    [IsScalarTower R K (HeightOneSpectrum.adicCompletion K v)]
    (B : Type u) [CommRing B] [TopologicalSpace B] [Finite B] :
    (trivialQuotChar K B).HasFlatProlongationAt v := by
  classical
  haveI : Fintype B := Fintype.ofFinite B
  -- the generic fibre is a finite product of copies of `K`, hence étale
  haveI : Algebra.Etale K (K ⊗[R] GroupFunctions R (Multiplicative B)) :=
    Algebra.Etale.of_equiv
      (GroupFunctions.baseChangeAlgEquiv R (Multiplicative B) K).symm
  -- the `Kᵃˡᵍ`-points of the constant group scheme over `R` are `B` itself
  let e₁ : Multiplicative B ≃*
      WithConv (GroupFunctions R (Multiplicative B) →ₐ[R] AlgebraicClosure K) :=
    GroupFunctions.pointsMulEquiv R (Multiplicative B) (AlgebraicClosure K)
  -- the tensor–hom adjunction, compatible with the convolution products
  let e₂ : WithConv (GroupFunctions R (Multiplicative B) →ₐ[R] AlgebraicClosure K) ≃*
      WithConv ((K ⊗[R] GroupFunctions R (Multiplicative B)) →ₐ[K] AlgebraicClosure K) :=
    { toFun := fun χ => WithConv.toConv (AlgHom.liftEquiv R K
        (GroupFunctions R (Multiplicative B)) (AlgebraicClosure K) χ.ofConv)
      invFun := fun φ => WithConv.toConv ((AlgHom.liftEquiv R K
        (GroupFunctions R (Multiplicative B)) (AlgebraicClosure K)).symm φ.ofConv)
      left_inv := fun χ => WithConv.ext ((AlgHom.liftEquiv R K
        (GroupFunctions R (Multiplicative B)) (AlgebraicClosure K)).symm_apply_apply χ.ofConv)
      right_inv := fun φ => WithConv.ext ((AlgHom.liftEquiv R K
        (GroupFunctions R (Multiplicative B)) (AlgebraicClosure K)).apply_symm_apply φ.ofConv)
      map_mul' := fun χ₁ χ₂ => WithConv.ext (liftEquiv_convMul χ₁ χ₂) }
  let E := e₁.trans e₂
  refine (trivialQuotChar K B).hasFlatProlongationAt_of_hopf_package (v := v) R
    (GroupFunctions R (Multiplicative B))
    { toFun := fun x => Multiplicative.toAdd (E.symm (Additive.toMul x))
      invFun := fun b => Additive.ofMul (E (Multiplicative.ofAdd b))
      left_inv := fun x => by
        show Additive.ofMul (E (E.symm (Additive.toMul x))) = x
        rw [MulEquiv.apply_symm_apply]
        rfl
      right_inv := fun b => by
        show Multiplicative.toAdd (E.symm (E (Multiplicative.ofAdd b))) = b
        rw [MulEquiv.symm_apply_apply]
        rfl
      map_add' := fun x y => by
        show Multiplicative.toAdd (E.symm (Additive.toMul x * Additive.toMul y)) = _
        rw [map_mul]
        rfl } ?_
  -- equivariance: the Galois action on the points is trivial, and so is `ρ`
  intro σ φ
  have hcomp : σ.toAlgHom.comp φ = φ := by
    apply (AlgHom.liftEquiv R K (GroupFunctions R (Multiplicative B))
      (AlgebraicClosure K)).symm.injective
    rw [liftEquiv_symm_comp]
    obtain ⟨g, hg⟩ := GroupFunctions.exists_eq_pointAlgHom
      ((AlgHom.liftEquiv R K (GroupFunctions R (Multiplicative B))
        (AlgebraicClosure K)).symm φ)
    rw [hg, GroupFunctions.comp_pointAlgHom]
  have hrho : ∀ y : B, (trivialQuotChar K B) σ y = y := fun _ => rfl
  rw [hcomp, hrho]

/-- **The CONSTANT group scheme** (PROVEN, 2026-07-26): a Galois representation
on a FINITE module with TRIVIAL action has a flat prolongation at every place.

This is `hasFlatProlongationAt_trivialQuotChar_of_base` at `K = ℚ` with the
auxiliary base `R = ℤ` — the smallest base carrying the constant group scheme
and mapping compatibly into both `ℚ` and `𝒪ᵥ`, so that
`GaloisRep.hasFlatProlongationAt_of_hopf_package` applies at EVERY place `v` of
`ℚ` at once (rather than only at places of the form `q.toHeightOneSpectrum…`,
which is what `hasFlatProlongationAt_of_dvr_package`'s `ℤ_(q)` base would give).
The five scalar-tower hypotheses hold for `ℤ` by
`Mathlib/Algebra/Module/NatInt.lean`'s `IsScalarTower ℤ R M` instance. -/
theorem hasFlatProlongationAt_trivialQuotChar
    {v : HeightOneSpectrum (NumberField.RingOfIntegers ℚ)}
    (B : Type) [CommRing B] [TopologicalSpace B] [Finite B] :
    (trivialQuotChar ℚ B).HasFlatProlongationAt v :=
  hasFlatProlongationAt_trivialQuotChar_of_base v ℤ B

/-- **The DIAGONALIZABLE (`μ`-typed) group scheme** (sorry leaf): the
rank-one cyclotomic member over a FINITE coefficient ring has a flat
prolongation at every place. The witness is `Spec 𝒪ᵥ[D]`, the group
algebra (mathlib's `MonoidAlgebra.instHopfAlgebra`) of the character
group `D = (Multiplicative B →* (ℚ̄)ˣ)`: it is finite free over `𝒪ᵥ`,
its generic fibre `Kᵥ[D]` is étale over `Kᵥ` in characteristic zero,
and its `Kᵥᵃˡᵍ`-points are `D →* (Kᵥᵃˡᵍ)ˣ` (`MonoidAlgebra.lift`),
which character BIDUALITY identifies with `B` itself
(`CommGroup.monoidHomMonoidHomEquiv`, applicable because a finite ring
`B` admitting a ring map from `ℤ_ℓ` is killed by a power of `ℓ` — the
kernel of `ℤ_ℓ → B` is a nonzero ideal `ℓ^k ℤ_ℓ` — so its exponent is
an `ℓ`-power and `ℚ̄` has enough roots of unity for it). Under that
identification `σ` acts by `ζ ↦ ζ ^ χ_cyc(σ)` on the values, which is
exactly multiplication by `cycUnitChar ℓ B σ` on `B`: that is the
defining property of the cyclotomic character
(`cyclotomicCharacter.toZModPow` + `modularCyclotomicCharacter.unique`,
the same route as `adicArithFrob_rootsOfUnity_pow_of_ne` above). -/
theorem hasFlatProlongationAt_cycScalarRep {ℓ : ℕ} [Fact ℓ.Prime]
    {v : HeightOneSpectrum (NumberField.RingOfIntegers ℚ)}
    {B : Type} [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
    [Algebra ℤ_[ℓ] B] [Finite B]
    (hcont : Continuous (algebraMap ℤ_[ℓ] B)) :
    (cycScalarRep hcont).HasFlatProlongationAt v :=
  sorry

/-- **The Eisenstein member over a FINITE coefficient ring has a flat
prolongation at every place** (PROVEN from the three group-scheme
leaves above): the diagonal member `diag(1, χ_cyc)` on a rank-two
carrier is, in the chosen basis, the product of the trivial character
on the first coordinate and the rank-one cyclotomic member on the
second, so the additive identification `B × B ≃+ N`,
`(x, y) ↦ x • b 0 + y • b 1`, is `Γ_ℚ`-equivariant and
`hasFlatProlongationAt_of_prod` applies. -/
theorem hasFlatProlongationAt_cycDiagRep {ℓ : ℕ} [Fact ℓ.Prime]
    {v : HeightOneSpectrum (NumberField.RingOfIntegers ℚ)}
    {B : Type} [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
    [Algebra ℤ_[ℓ] B] [Finite B]
    {N : Type*} [AddCommGroup N] [Module B N]
    (hcont : Continuous (algebraMap ℤ_[ℓ] B)) (b : Module.Basis (Fin 2) B N) :
    (cycDiagRep hcont b).HasFlatProlongationAt v := by
  classical
  let e2 : (B × B) ≃+ (Fin 2 → B) :=
    { toFun := fun p => ![p.1, p.2]
      invFun := fun f => (f 0, f 1)
      left_inv := fun _ => rfl
      right_inv := fun f => by funext i; fin_cases i <;> rfl
      map_add' := fun _ _ => by funext i; fin_cases i <;> rfl }
  let e : (B × B) ≃+ N := e2.trans b.equivFun.symm.toAddEquiv
  have hev : ∀ p : B × B, e p = p.1 • b 0 + p.2 • b 1 := by
    intro p
    show b.equivFun.symm ![p.1, p.2] = _
    rw [Module.Basis.equivFun_symm_apply, Fin.sum_univ_two]
    simp
  refine hasFlatProlongationAt_of_prod
    (hasFlatProlongationAt_trivialQuotChar (v := v) B)
    (hasFlatProlongationAt_cycScalarRep (v := v) hcont) _ e ?_
  intro σ x
  obtain ⟨x₁, x₂⟩ := x
  show e (x₁, cycUnitChar ℓ B σ • x₂) = (cycDiagRep hcont b) σ (e (x₁, x₂))
  rw [hev, hev, cycDiagRep_apply, map_add, map_smul, map_smul,
    cycDiagEnd_apply_basis_zero, cycDiagEnd_apply_basis_one, smul_eq_mul, smul_smul,
    mul_comm x₂]

/-- The concrete ring of integers is COMPACT (PROVEN): it carries the
`ℤ_ℓ`-module topology (`isModuleTopology_integralClosure_padicInt`) and
is module-finite over the compact `ℤ_ℓ`, so it is the continuous image
of a compact `ℤ_ℓⁿ`. -/
theorem compactSpace_integralClosure_padicInt {ℓ : ℕ} [Fact ℓ.Prime]
    (L : IntermediateField ℚ_[ℓ] (AlgebraicClosure ℚ_[ℓ])) [FiniteDimensional ℚ_[ℓ] L] :
    CompactSpace (IntegralClosure ℤ_[ℓ] L) := by
  haveI := isModuleTopology_integralClosure_padicInt L
  obtain ⟨n, φ, hφ⟩ := Module.Finite.exists_fin' ℤ_[ℓ] (IntegralClosure ℤ_[ℓ] L)
  exact hφ.compactSpace (IsModuleTopology.continuous_of_linearMap φ)

/-- **The open quotients of the concrete ring of integers are FINITE**
(PROVEN): the quotient is compact (continuous image of the compact
`𝒪`) and discrete (the singleton `{mk y}` is the image of the open
coset `y + I` under the open quotient map), hence finite. This is the
step that turns the open-ideal quantifier of `GaloisRep.IsFlatAt` into
a FINITE group-scheme question. -/
theorem finite_quotient_of_isOpen_integralClosure {ℓ : ℕ} [Fact ℓ.Prime]
    (L : IntermediateField ℚ_[ℓ] (AlgebraicClosure ℚ_[ℓ])) [FiniteDimensional ℚ_[ℓ] L]
    (I : Ideal (IntegralClosure ℤ_[ℓ] L))
    (hI : IsOpen (I : Set (IntegralClosure ℤ_[ℓ] L))) :
    Finite (IntegralClosure ℤ_[ℓ] L ⧸ I) := by
  haveI := compactSpace_integralClosure_padicInt L
  haveI : DiscreteTopology (IntegralClosure ℤ_[ℓ] L ⧸ I) := by
    refine discreteTopology_iff_isOpen_singleton.mpr fun x => ?_
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
    have hset : ({Ideal.Quotient.mk I y} : Set (IntegralClosure ℤ_[ℓ] L ⧸ I)) =
        Ideal.Quotient.mk I '' ((fun z => y + z) '' (I : Set (IntegralClosure ℤ_[ℓ] L))) := by
      ext w
      constructor
      · intro hw
        rw [Set.mem_singleton_iff] at hw
        exact ⟨y + 0, ⟨0, I.zero_mem, rfl⟩, by rw [add_zero]; exact hw.symm⟩
      · rintro ⟨u, ⟨z, hz, rfl⟩, rfl⟩
        simp only [Set.mem_singleton_iff, map_add]
        rw [Ideal.Quotient.eq_zero_iff_mem.mpr hz, add_zero]
    rw [hset]
    exact QuotientRing.isOpenMap_coe I _ (isOpenMap_add_left y _ hI)
  exact finite_of_compact_of_discrete

/-- **Flatness of the Eisenstein member at `ℓ`** (PROVEN assembly over
the three group-scheme leaves above; see the section note): over the
ring of integers
`𝒪 = IntegralClosure ℤ_ℓ L` of a finite extension `L/ℚ_ℓ`, the
diagonal representation `1 ⊕ χ_cyc,ℓ` is flat at `ℓ` — it is the
Galois module of geometric points of the `ℓ`-divisible group
`ℚ_ℓ/ℤ_ℓ × μ_{ℓ^∞}` tensored with `𝒪`. Proof: an open ideal `I ⊆ 𝒪`
has FINITE quotient (`finite_quotient_of_isOpen_integralClosure`: `𝒪`
is compact and `𝒪/I` is discrete), the base change of the diagonal
member along `𝒪 → 𝒪/I` IS the diagonal member over `𝒪/I` in the
base-changed basis (compared through `LinearMap.toMatrix_baseChange`,
both matrices being `diag(1, χ_cyc)`), and over a finite coefficient
ring the diagonal member has a flat prolongation
(`hasFlatProlongationAt_cycDiagRep`), namely the product of the
constant group scheme on `𝒪/I` with the `μ`-typed group scheme
`μ_{𝒪/I}` — which is where the three remaining group-scheme leaves
sit. -/
theorem isFlatAt_cycDiagRep {ℓ : ℕ} [Fact ℓ.Prime]
    (L : IntermediateField ℚ_[ℓ] (AlgebraicClosure ℚ_[ℓ])) [FiniteDimensional ℚ_[ℓ] L]
    {W : Type*} [AddCommGroup W] [Module (IntegralClosure ℤ_[ℓ] L) W]
    [Module.Finite (IntegralClosure ℤ_[ℓ] L) W] [Module.Free (IntegralClosure ℤ_[ℓ] L) W]
    (hcont : Continuous (algebraMap ℤ_[ℓ] (IntegralClosure ℤ_[ℓ] L)))
    (b : Module.Basis (Fin 2) (IntegralClosure ℤ_[ℓ] L) W) :
    (cycDiagRep hcont b).IsFlatAt
      (Nat.Prime.toHeightOneSpectrumRingOfIntegersRat (Fact.out : ℓ.Prime)) := by
  classical
  constructor
  intro I hI
  haveI : Finite (IntegralClosure ℤ_[ℓ] L ⧸ I) :=
    finite_quotient_of_isOpen_integralClosure L I hI
  haveI : IsScalarTower ℤ_[ℓ] (IntegralClosure ℤ_[ℓ] L) (IntegralClosure ℤ_[ℓ] L ⧸ I) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hcontI : Continuous (algebraMap ℤ_[ℓ] (IntegralClosure ℤ_[ℓ] L ⧸ I)) := by
    have hfun : (algebraMap ℤ_[ℓ] (IntegralClosure ℤ_[ℓ] L ⧸ I) :
        ℤ_[ℓ] → (IntegralClosure ℤ_[ℓ] L ⧸ I)) =
        (Ideal.Quotient.mk I) ∘ (algebraMap ℤ_[ℓ] (IntegralClosure ℤ_[ℓ] L)) := rfl
    rw [hfun]
    exact continuous_quot_mk.comp hcont
  have hrep : (cycDiagRep hcont b).baseChange (IntegralClosure ℤ_[ℓ] L ⧸ I) =
      cycDiagRep hcontI
        (Algebra.TensorProduct.basis (IntegralClosure ℤ_[ℓ] L ⧸ I) b) := by
    refine GaloisRep.ext fun σ => ?_
    have hBC : ((cycDiagRep hcont b).baseChange (IntegralClosure ℤ_[ℓ] L ⧸ I)) σ =
        LinearMap.baseChange (IntegralClosure ℤ_[ℓ] L ⧸ I) ((cycDiagRep hcont b) σ) :=
      LinearMap.ext fun x => by
        induction x using TensorProduct.induction_on with
        | zero => simp
        | add u w hu hw => simp only [map_add, hu, hw]
        | tmul r w => simp
    rw [hBC, cycDiagRep_apply, cycDiagRep_apply,
      cycUnitChar_algebraMap (A := IntegralClosure ℤ_[ℓ] L)
        (B := IntegralClosure ℤ_[ℓ] L ⧸ I) σ]
    apply (LinearMap.toMatrix
      (Algebra.TensorProduct.basis (IntegralClosure ℤ_[ℓ] L ⧸ I) b)
      (Algebra.TensorProduct.basis (IntegralClosure ℤ_[ℓ] L ⧸ I) b)).injective
    simp only [cycDiagEnd, LinearMap.toMatrix_baseChange, LinearMap.toMatrix_toLin]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.diagonal, Matrix.map_apply]
  rw [hrep]
  exact hasFlatProlongationAt_cycDiagRep hcontI _

/-- **The Eisenstein member is hardly ramified** (PROVEN assembly; the
sorries below it are now the three GROUP-SCHEME leaves under
`isFlatAt_cycDiagRep` — `hasFlatProlongationAt_of_prod`,
`hasFlatProlongationAt_trivialQuotChar`,
`hasFlatProlongationAt_cycScalarRep`): over the
ring of integers of a finite extension
`L/ℚ_ℓ`, the diagonal member `1 ⊕ χ_cyc,ℓ` has cyclotomic determinant
(`det diag(1, χ_cyc) = χ_cyc`, PROVEN), is unramified outside `{2, ℓ}`
(PROVEN over the arithmetic leaf), flat at `ℓ`
(`isFlatAt_cycDiagRep`, PROVEN), and tame at `2` with the TRIVIAL quotient
character on the first coordinate (PROVEN: the first diagonal entry is
`1`, and the trivial character is unramified with square one). -/
theorem isHardlyRamified_cycDiagRep {ℓ : ℕ} [Fact ℓ.Prime] (hℓodd : Odd ℓ)
    (L : IntermediateField ℚ_[ℓ] (AlgebraicClosure ℚ_[ℓ])) [FiniteDimensional ℚ_[ℓ] L]
    {W : Type*} [AddCommGroup W] [Module (IntegralClosure ℤ_[ℓ] L) W]
    [Module.Finite (IntegralClosure ℤ_[ℓ] L) W] [Module.Free (IntegralClosure ℤ_[ℓ] L) W]
    (hcont : Continuous (algebraMap ℤ_[ℓ] (IntegralClosure ℤ_[ℓ] L)))
    (b : Module.Basis (Fin 2) (IntegralClosure ℤ_[ℓ] L) W)
    (hrank : Module.rank (IntegralClosure ℤ_[ℓ] L) W = 2) :
    IsHardlyRamified hℓodd hrank (cycDiagRep hcont b) := by
  classical
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- cyclotomic determinant
    intro g
    rw [GaloisRep.det_apply, cycDiagRep_apply, det_cycDiagEnd]
    rfl
  · -- unramified outside `{2, ℓ}`
    intro q hq hq2ℓ
    exact isUnramifiedAt_cycDiagRep_of_ne hcont b hq hq2ℓ.2
  · -- flat at `ℓ`: PROVEN over the three group-scheme leaves
    exact isFlatAt_cycDiagRep L hcont b
  · -- tame at `2`: quotient by the first coordinate, TRIVIAL character
    refine ⟨b.coord 0, fun a => ⟨a • b 0, by simp⟩, trivialQuotChar ℚ_[2] _,
      fun g w => ⟨?_, ?_, fun g' => ?_⟩⟩
    · rw [GaloisRep.map_apply, cycDiagRep_apply]
      exact coord_zero_cycDiagEnd b _ w
    · intro σ _
      exact rfl
    · exact one_mul 1

/-- Mapping `(X - 1)(X - q)` along a ring homomorphism (PROVEN
bookkeeping, shared by the two realization leaves below). -/
lemma map_X_sub_one_mul_X_sub_natCast {A B : Type*} [CommRing A] [CommRing B]
    (f : A →+* B) (q : ℕ) :
    ((Polynomial.X - Polynomial.C 1) * (Polynomial.X - Polynomial.C (q : A))).map f =
      (Polynomial.X - Polynomial.C 1) * (Polynomial.X - Polynomial.C (q : B)) := by
  rw [Polynomial.map_mul, Polynomial.map_sub, Polynomial.map_sub, Polynomial.map_X,
    Polynomial.map_C, Polynomial.map_C, map_one, map_natCast]

/-- **The reducible eigensystem is `(X - 1)(X - q)`** (PROVEN assembly
over the Eisenstein character dichotomy): for a hardly ramified `ρ`
whose base change to `ℚ̄_p` is NOT irreducible, the eigensystem
polynomial `Pv v` at the place of every prime `q ∉ S ∪ {p}` is exactly
`(X - 1)(X - q)` IN `E[X]`. Route: the diagonal characters `χ₁, χ₂` of
the reducibility analysis satisfy `χ₁ + χ₂ = 1 + χ_cyc`
(`char_add_char_eq_one_add_cyclotomicCharacter`) and `χ₁χ₂ = χ_cyc`
(the determinant identity, read off `coeff 0` via
`charFrob_coeff_zero_eq_natCast`); at the arithmetic Frobenius of `q`
the cyclotomic character is `q` (PROVEN
`cyclotomicCharacter_adicArithFrob_natCast`), so the mapped Frobenius
charpoly is `X² - (1+q)X + q = (X - 1)(X - q)`, and `ψ`-injectivity
descends the identity from `ℚ̄_p[X]` to `E[X]` (a ring homomorphism
out of `ℚ` is unique, so the coefficients on both sides are the `ψ`-
resp. identity-images of the SAME rational polynomial). -/
theorem eisenstein_Pv_eq_of_not_isIrreducible
    [Algebra R (AlgebraicClosure ℚ_[p])]
    [ContinuousSMul R (AlgebraicClosure ℚ_[p])]
    (hZinj : Function.Injective (algebraMap ℤ_[p] R))
    (hRinj : Function.Injective (algebraMap R (AlgebraicClosure ℚ_[p])))
    (hρ : IsHardlyRamified hpodd hv ρ)
    (hred : ¬ (ρ.baseChange (AlgebraicClosure ℚ_[p])).IsIrreducible)
    {E : Type v} [Field E] [NumberField E] (ψ : E →+* AlgebraicClosure ℚ_[p])
    {S : Finset (HeightOneSpectrum (NumberField.RingOfIntegers ℚ))}
    {Pv : HeightOneSpectrum (NumberField.RingOfIntegers ℚ) → Polynomial E}
    (heig : ∀ v ∉ S,
      (ρ.charFrob v).map (algebraMap R (AlgebraicClosure ℚ_[p])) = (Pv v).map ψ)
    {q : ℕ} (hq : q.Prime) (hqp : q ≠ p)
    (hqS : hq.toHeightOneSpectrumRingOfIntegersRat ∉ S) :
    Pv hq.toHeightOneSpectrumRingOfIntegersRat =
      (Polynomial.X - Polynomial.C 1) * (Polynomial.X - Polynomial.C (q : E)) := by
  classical
  obtain ⟨χ₁, χ₂, hcont₁, hcont₂, hone₁, hone₂, hmul₁, hmul₂, hchar⟩ :=
    exists_char_charpoly_map_eq_of_not_isIrreducible hv hred
  have hsum := char_add_char_eq_one_add_cyclotomicCharacter hpodd hv hZinj hRinj hρ
    χ₁ χ₂ hcont₁ hcont₂ hone₁ hone₂ hmul₁ hmul₂ hchar
  -- the Frobenius charpoly in the freshly spelled global-Frobenius form
  -- (the `Subsingleton.elim` juggle of `exists_rat_trace_coeff_of_not_isIrreducible`)
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
  set g₀ : Field.absoluteGaloisGroup ℚ := Field.absoluteGaloisGroup.map (algebraMap ℚ
    (HeightOneSpectrum.adicCompletion ℚ hq.toHeightOneSpectrumRingOfIntegersRat))
    (Field.AbsoluteGaloisGroup.adicArithFrob hq.toHeightOneSpectrumRingOfIntegersRat)
    with hg₀
  -- the trace identity at the Frobenius: `χ₁ + χ₂ = 1 + q`
  have hsq : χ₁ g₀ + χ₂ g₀ = 1 + (q : AlgebraicClosure ℚ_[p]) := by
    have h := hsum g₀
    rw [hg₀, cyclotomicCharacter_adicArithFrob_natCast hq hqp, map_natCast] at h
    rw [hg₀]
    exact h
  -- the determinant identity at the Frobenius: `χ₁ · χ₂ = q`
  have hc0 := charFrob_coeff_zero_eq_natCast hpodd hv hρ hq hqp
  have hpr : χ₁ g₀ * χ₂ g₀ = (q : AlgebraicClosure ℚ_[p]) := by
    have h0 : ((ρ.charFrob hq.toHeightOneSpectrumRingOfIntegersRat).map
        (algebraMap R (AlgebraicClosure ℚ_[p]))).coeff 0 = χ₁ g₀ * χ₂ g₀ := by
      rw [hcp, hchar g₀, Polynomial.mul_coeff_zero]
      simp only [Polynomial.coeff_sub, Polynomial.coeff_X_zero, Polynomial.coeff_C_zero,
        zero_sub, neg_mul_neg]
    rw [← h0, hc0]
  -- the split quadratic collapses to `(X - 1)(X - q)` over `ℚ̄_p`
  have hfact : (Polynomial.X - Polynomial.C (χ₁ g₀)) * (Polynomial.X - Polynomial.C (χ₂ g₀)) =
      (Polynomial.X - Polynomial.C 1) *
        (Polynomial.X - Polynomial.C ((q : AlgebraicClosure ℚ_[p]))) := by
    have hexp : ∀ a c : AlgebraicClosure ℚ_[p],
        (Polynomial.X - Polynomial.C a) * (Polynomial.X - Polynomial.C c) =
          Polynomial.X ^ 2 - (Polynomial.C a + Polynomial.C c) * Polynomial.X +
            Polynomial.C a * Polynomial.C c := by
      intro a c
      ring
    rw [hexp, hexp]
    simp only [← Polynomial.C_add, ← Polynomial.C_mul]
    rw [hsq, hpr, one_mul]
  -- the mapped eigensystem polynomial over `ℚ̄_p`
  have h1 : (Pv hq.toHeightOneSpectrumRingOfIntegersRat).map ψ =
      (Polynomial.X - Polynomial.C 1) *
        (Polynomial.X - Polynomial.C ((q : AlgebraicClosure ℚ_[p]))) := by
    rw [← heig _ hqS, hcp, hchar g₀, hfact]
  -- descend along the injective `ψ`
  refine Polynomial.map_injective ψ ψ.injective ?_
  rw [h1, map_X_sub_one_mul_X_sub_natCast ψ q]

end EisensteinDiagonal

/-- **Eisenstein realizations at odd residue characteristics** (PROVEN
assembly, DECOMPOSED 2026-07-24; the REDUCIBLE branch of the
realization atom below): if the base
extension of the hardly ramified `ρ` to `ℚ̄_p` is NOT irreducible, its
eigensystem is realized integrally at every odd `(ℓ, φ)` — with no
modular form involved. The classical route: by the proven reducibility
analysis (`exists_char_charpoly_map_eq_of_not_isIrreducible`) and the
Eisenstein character dichotomy
(`char_add_char_eq_one_add_cyclotomicCharacter`, with the determinant
condition `χ₁χ₂ = χ_cyc`), the mapped charpolys degenerate to
`(X − 1)(X − q)` away from finitely many places, so `Pv v` has RATIONAL
coefficients there (`ψ` is injective and ring homs out of `ℚ` are
unique), `(Pv v).map φ = (X − 1)(X − q)` for EVERY `φ`, and the
explicit representation `1 ⊕ χ_cyc,ℓ` on `ℤ_ℓ²` (over `L = ⊥`,
`IntegralClosure ℤ_ℓ ℚ_ℓ`) realizes it: hardly ramified (unramified
outside `{ℓ}` ⊆ `{2, ℓ}`; flat at `ℓ` as the Tate module of
`μ_{ℓ^∞} × ℚ_ℓ/ℤ_ℓ`; unramified hence tame at `2`; cyclotomic
determinant) with `charFrob v = (X − 1)(X − q)` by the proven
`cyclotomicCharacter_adicArithFrob_natCast`. See DECOMPOSITION PLAN
item 5 in `Fermat/FLT/Modularity/Interface.lean`.

DECOMPOSED (2026-07-24) into a PROVEN assembly over the
`EisensteinDiagonal` section above: the eigensystem identification is
the PROVEN `eisenstein_Pv_eq_of_not_isIrreducible`; the realizing
member is the explicit `cycDiagRep` over `IntegralClosure ℤ_ℓ ⊥` on
the `Type v` carrier `ULift (Fin 2 → 𝒪)`, hardly ramified by the
PROVEN assembly `isHardlyRamified_cycDiagRep` and matching Frobenius
charpolys by the PROVEN `charFrob_cycDiagRep_of_ne`. The two remaining
sorried sub-leaves are now both PROVEN
(`cyclotomicCharacter_eq_one_of_mem_localInertiaGroup_of_ne`, μ_{ℓ^∞}
unramified away from `ℓ`, and `isFlatAt_cycDiagRep`, the
`ℤ/ℓⁿ × μ_{ℓⁿ}` flat prolongations); what remains under the latter are
the three `ρ`-free group-scheme leaves listed at
`hasFlatProlongationAt_cycDiagRep`. -/
theorem exists_hardlyRamified_ringOfIntegers_realizations_of_not_isIrreducible
    [Algebra R (AlgebraicClosure ℚ_[p])]
    [ContinuousSMul R (AlgebraicClosure ℚ_[p])]
    (hZinj : Function.Injective (algebraMap ℤ_[p] R))
    (hRinj : Function.Injective (algebraMap R (AlgebraicClosure ℚ_[p])))
    (hρ : IsHardlyRamified hpodd hv ρ)
    (hred : ¬ (ρ.baseChange (AlgebraicClosure ℚ_[p])).IsIrreducible)
    {E : Type v} [Field E] [NumberField E] (ψ : E →+* AlgebraicClosure ℚ_[p])
    (S : Finset (HeightOneSpectrum (NumberField.RingOfIntegers ℚ)))
    (Pv : HeightOneSpectrum (NumberField.RingOfIntegers ℚ) → Polynomial E)
    (heig : ∀ v ∉ S,
      (ρ.charFrob v).map (algebraMap R (AlgebraicClosure ℚ_[p])) = (Pv v).map ψ) :
    ∃ (T : Finset (HeightOneSpectrum (NumberField.RingOfIntegers ℚ))),
      ∀ (ℓ : ℕ) (_hℓ : Fact ℓ.Prime) (hℓodd : Odd ℓ)
        (φ : E →+* AlgebraicClosure ℚ_[ℓ]),
      ∃ (L : IntermediateField ℚ_[ℓ] (AlgebraicClosure ℚ_[ℓ]))
        (_ : FiniteDimensional ℚ_[ℓ] L)
        (W : Type v) (_ : AddCommGroup W)
        (_ : Module (IntegralClosure ℤ_[ℓ] L) W)
        (_ : Module.Finite (IntegralClosure ℤ_[ℓ] L) W)
        (_ : Module.Free (IntegralClosure ℤ_[ℓ] L) W)
        (hW : Module.rank (IntegralClosure ℤ_[ℓ] L) W = 2)
        (τ : GaloisRep ℚ (IntegralClosure ℤ_[ℓ] L) W)
        (_r : AlgebraicClosure ℚ_[ℓ] ⊗[IntegralClosure ℤ_[ℓ] L] W
          ≃ₗ[AlgebraicClosure ℚ_[ℓ]] Fin 2 → AlgebraicClosure ℚ_[ℓ]),
        IsHardlyRamified hℓodd hW τ ∧
        ∀ v ∉ T, (ℓ : NumberField.RingOfIntegers ℚ) ∉ v.asIdeal →
          τ.IsUnramifiedAt v ∧
          (τ.charFrob v).map
              (algebraMap (IntegralClosure ℤ_[ℓ] L) (AlgebraicClosure ℚ_[ℓ])) =
            (Pv v).map φ := by
  classical
  refine ⟨S ∪ {hp.out.toHeightOneSpectrumRingOfIntegersRat}, ?_⟩
  intro ℓ hℓ hℓodd φ
  haveI := hℓ
  -- the explicit member `1 ⊕ χ_cyc,ℓ` over the integers of `L = ⊥`, on the
  -- `Type v` carrier `ULift (Fin 2 → 𝒪)` framed by the standard basis
  have hcont : Continuous (algebraMap ℤ_[ℓ]
      (IntegralClosure ℤ_[ℓ] (⊥ : IntermediateField ℚ_[ℓ] (AlgebraicClosure ℚ_[ℓ])))) :=
    continuous_algebraMap_integralClosure_padicInt _
  let b : Module.Basis (Fin 2)
      (IntegralClosure ℤ_[ℓ] (⊥ : IntermediateField ℚ_[ℓ] (AlgebraicClosure ℚ_[ℓ])))
      (ULift.{v} (Fin 2 → IntegralClosure ℤ_[ℓ]
        (⊥ : IntermediateField ℚ_[ℓ] (AlgebraicClosure ℚ_[ℓ])))) :=
    (Pi.basisFun _ (Fin 2)).map
      (ULift.moduleEquiv : ULift.{v} (Fin 2 → IntegralClosure ℤ_[ℓ]
        (⊥ : IntermediateField ℚ_[ℓ] (AlgebraicClosure ℚ_[ℓ]))) ≃ₗ[IntegralClosure ℤ_[ℓ]
          (⊥ : IntermediateField ℚ_[ℓ] (AlgebraicClosure ℚ_[ℓ]))] _).symm
  haveI hWfin : Module.Finite
      (IntegralClosure ℤ_[ℓ] (⊥ : IntermediateField ℚ_[ℓ] (AlgebraicClosure ℚ_[ℓ])))
      (ULift.{v} (Fin 2 → IntegralClosure ℤ_[ℓ]
        (⊥ : IntermediateField ℚ_[ℓ] (AlgebraicClosure ℚ_[ℓ])))) := Module.Finite.of_basis b
  haveI hWfree : Module.Free
      (IntegralClosure ℤ_[ℓ] (⊥ : IntermediateField ℚ_[ℓ] (AlgebraicClosure ℚ_[ℓ])))
      (ULift.{v} (Fin 2 → IntegralClosure ℤ_[ℓ]
        (⊥ : IntermediateField ℚ_[ℓ] (AlgebraicClosure ℚ_[ℓ])))) := Module.Free.of_basis b
  have hrank : Module.rank
      (IntegralClosure ℤ_[ℓ] (⊥ : IntermediateField ℚ_[ℓ] (AlgebraicClosure ℚ_[ℓ])))
      (ULift.{v} (Fin 2 → IntegralClosure ℤ_[ℓ]
        (⊥ : IntermediateField ℚ_[ℓ] (AlgebraicClosure ℚ_[ℓ])))) = 2 := by
    rw [rank_eq_card_basis b, Fintype.card_fin]
    norm_num
  refine ⟨⊥, inferInstance,
    ULift.{v} (Fin 2 → IntegralClosure ℤ_[ℓ]
      (⊥ : IntermediateField ℚ_[ℓ] (AlgebraicClosure ℚ_[ℓ]))),
    inferInstance, inferInstance, hWfin, hWfree, hrank,
    cycDiagRep hcont b, (b.baseChange (AlgebraicClosure ℚ_[ℓ])).equivFun,
    isHardlyRamified_cycDiagRep hℓodd ⊥ hcont b hrank, ?_⟩
  intro w hwT hwℓ
  obtain ⟨q, hq, rfl⟩ := exists_prime_toHeightOneSpectrumRingOfIntegersRat w
  have hqS : hq.toHeightOneSpectrumRingOfIntegersRat ∉ S := fun hmem =>
    hwT (Finset.mem_union_left _ hmem)
  have hqp : q ≠ p := by
    rintro rfl
    exact hwT (Finset.mem_union_right _ (Finset.mem_singleton_self _))
  have hqℓ : q ≠ ℓ := by
    rintro rfl
    exact hwℓ
      ((Nat.Prime.mem_toHeightOneSpectrumRingOfIntegersRat_asIdeal hq _).mpr (by simp))
  refine ⟨isUnramifiedAt_cycDiagRep_of_ne hcont b hq hqℓ, ?_⟩
  rw [charFrob_cycDiagRep_of_ne hcont b hq hqℓ, map_X_sub_one_mul_X_sub_natCast,
    eisenstein_Pv_eq_of_not_isIrreducible hpodd hv hZinj hRinj hρ hred ψ heig hq hqp hqS,
    map_X_sub_one_mul_X_sub_natCast]

/-- **Automorphy core over concrete rings of integers, odd residue
characteristics** (PROVEN assembly as of 2026-07-23 — see the
DECOMPOSED note at the end): the eigensystem `(E, S, Pv)` attached
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
ramified shape. RE-AUDIT (2026-07-23, fresh against the actual pin —
see the refreshed VOCABULARY OBSTRUCTION below for the details): the
obstruction stands; the pin's only new Hecke material is
`Mathlib.NumberTheory.HeckeRing.Defs` (abstract double-coset modules,
no ring product, no action on modular forms), and the reference
project's `IsAutomorphicOfLevel` interface is confirmed unvendorable
and non-restating (totally-real-`F` quaternionic shape, ≈22.8k-line
closure with sorried definitions).

DECOMPOSED (2026-07-23, opening the modularity subtree — this
supersedes the "no carrier is statable" conclusion of the notes above:
`Fermat/FLT/Modularity/Interface.lean` now provides a sound carrier as
REAL code, the Diamond–Shurman 5.8.5 coefficient characterization
`Modularity.IsWeightTwoEigenform` on the pin's analytic `CuspForm`,
sidestepping the still-absent Hecke operators) into a PROVEN dichotomy
assembly over three strictly shallower sorried nodes:

1. `Modularity.exists_weightTwoEigenform_of_isIrreducible` (sorry
   node, interface file; SHARED with the `λ ∣ 2` atom below) — on the
   irreducible branch the eigensystem arises from a normalized
   weight-2 eigenform of level `Γ₀(2)` (Wiles–Taylor–Wiles/
   Skinner–Wiles + Ribet level lowering; the fused "member existence +
   hardly ramified model" shape of the SOUNDNESS AUDIT is resolved by
   the level-2 pin-down, which forces the hardly ramified shape of the
   attached representations).
2. `exists_ringOfIntegers_realizations_of_weightTwoEigenform` (sorry
   node, above) — Eichler–Shimura/Deligne attachment with integral
   model at odd `ℓ`, for level-2 eigenforms; `ρ`-free.
3. `exists_hardlyRamified_ringOfIntegers_realizations_of_not_isIrreducible`
   (PROVEN assembly as of 2026-07-24, above; two `ρ`-free sub-leaves
   remain sorried) — the reducible/Eisenstein branch, where no
   cusp form matches the eigensystem (`1 ⊕ χ_cyc` realizes it
   explicitly).

The assembly (below) is the excluded-middle split on irreducibility of
`ρ ⊗ ℚ̄_p` — the same first move as the trace-shadow dichotomy
(`exists_isAlgebraic_trace_coeff`). -/
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
      ∀ (ℓ : ℕ) (_hℓ : Fact ℓ.Prime) (hℓodd : Odd ℓ)
        (φ : E →+* AlgebraicClosure ℚ_[ℓ]),
      ∃ (L : IntermediateField ℚ_[ℓ] (AlgebraicClosure ℚ_[ℓ]))
        (_ : FiniteDimensional ℚ_[ℓ] L)
        (W : Type v) (_ : AddCommGroup W)
        (_ : Module (IntegralClosure ℤ_[ℓ] L) W)
        (_ : Module.Finite (IntegralClosure ℤ_[ℓ] L) W)
        (_ : Module.Free (IntegralClosure ℤ_[ℓ] L) W)
        (hW : Module.rank (IntegralClosure ℤ_[ℓ] L) W = 2)
        (τ : GaloisRep ℚ (IntegralClosure ℤ_[ℓ] L) W)
        (_r : AlgebraicClosure ℚ_[ℓ] ⊗[IntegralClosure ℤ_[ℓ] L] W
          ≃ₗ[AlgebraicClosure ℚ_[ℓ]] Fin 2 → AlgebraicClosure ℚ_[ℓ]),
        IsHardlyRamified hℓodd hW τ ∧
        ∀ v ∉ T, (ℓ : NumberField.RingOfIntegers ℚ) ∉ v.asIdeal →
          τ.IsUnramifiedAt v ∧
          (τ.charFrob v).map
              (algebraMap (IntegralClosure ℤ_[ℓ] L) (AlgebraicClosure ℚ_[ℓ])) =
            (Pv v).map φ := by
  by_cases hirr : (ρ.baseChange (AlgebraicClosure ℚ_[p])).IsIrreducible
  · -- modular branch: level-2 eigenform existence + attachment
    obtain ⟨f, S', hf, hmatch⟩ :=
      Modularity.exists_weightTwoEigenform_of_isIrreducible hpodd hv hZinj hRinj
        hρ hirr ψ S Pv heig
    exact exists_ringOfIntegers_realizations_of_weightTwoEigenform S' Pv hf hmatch
  · -- Eisenstein branch: the reducible eigensystem is realized explicitly
    exact exists_hardlyRamified_ringOfIntegers_realizations_of_not_isIrreducible
      hpodd hv hZinj hRinj hρ hirr ψ S Pv heig

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

RE-AUDIT (2026-07-23, against the actual pin and reference tree,
refreshing the above): (1) the pin has gained exactly one Hecke item,
`Mathlib.NumberTheory.HeckeRing.Defs` — abstract Hecke-triple
double-coset modules ONLY; the convolution product/ring structure of
its "later files" is not in the pin (nothing imports it), and grep
confirms zero hits for Hecke operators on modular forms, newforms,
Atkin–Lehner, eigenforms, or attached Galois representations. (2) The
reference `IsAutomorphicOfLevel` remains unvendorable AND would not
restate these leaves even if vendored: its transitive FLT-internal
closure is 122 files / ≈22.8k lines (quaternionic automorphic forms,
Fujisaki finiteness, adelic Haar measure), it contains sorried
members (including a sorried `IsQuaternionAlgebra (E ⊗[F] D)`
instance inside its own interface layer), and it is stated for
totally real `F` with `2 < [F(ζ_p):F]` — the quaternionic shape the
reference project reaches from `ℚ` only through the (sorried)
`cyclic_base_change`; our leaves are the classical `ℚ`-level
Eichler–Shimura statements, so bridging would ADD Jacquet–Langlands/
base-change content, not remove any. (3) A minimal SHARED interface
for this leaf and `exists_realization_at_two_generated` was examined
and rejected as unsound-or-empty: a "newform datum" carrier has no
definable type (and a sorried opaque `Prop` definition is not a
legitimate leaf — `sorry` may only replace proofs of stated goals),
while a carrier-free shared statement necessarily degenerates to the
literal conjunction of the two atoms — the Brauer–Nesbitt trap below blocks
the only genuine factorization ("bare member matching `Pv`, then
upgrade to a hardly ramified integral model"), and at `λ | 2` the
generated coefficient field is already the exact Eichler–Shimura
output shape with zero slack. The two atoms stay fused and separate.

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

/-- **Eisenstein realization at the even prime** (PROVEN assembly,
DECOMPOSED 2026-07-24; the
REDUCIBLE branch of the `λ ∣ 2` atom below): if the base extension of
the hardly ramified `ρ` to `ℚ̄_p` is NOT irreducible, its eigensystem
is realized over any generated coefficient field `K ⊆ ℚ̄_₂` — with no
modular form involved. The classical route mirrors the odd-`ℓ`
Eisenstein leaf
(`exists_hardlyRamified_ringOfIntegers_realizations_of_not_isIrreducible`):
the reducible eigensystem degenerates to `(X − 1)(X − q)` with RATIONAL
coefficients away from finitely many places (proven reducibility
analysis + the Eisenstein character dichotomy + injectivity of `ψ`), so
`(Pv v).map φ₀ = (X − 1)(X − q)` for the given `φ₀`, and the explicit
representation `1 ⊕ χ_cyc,2` on `K²` realizes it (unramified outside
`{2}`, absorbed by `T`; `charFrob v = (X − 1)(X − q)` by the proven
`cyclotomicCharacter_adicArithFrob_natCast`). See DECOMPOSITION PLAN
item 5 in `Fermat/FLT/Modularity/Interface.lean`.

DECOMPOSED (2026-07-24) into a PROVEN assembly over the
`EisensteinDiagonal` section above, exactly as at the odd-`ℓ`
Eisenstein leaf: the eigensystem identification is the PROVEN
`eisenstein_Pv_eq_of_not_isIrreducible`, the realizing member is the
explicit `cycDiagRep` at `ℓ = 2` over `K` itself on `Fin 2 → K` with
the standard basis (no integral model and no hardly-ramifiedness are
demanded at the even prime, so the field-level member suffices), and
the Frobenius charpolys match by the PROVEN `charFrob_cycDiagRep_of_ne`.
The single remaining sorried sub-leaf here is the `ρ`-free arithmetic
`cyclotomicCharacter_eq_one_of_mem_localInertiaGroup_of_ne` (at
`ℓ = 2`: `μ_{2^∞}/ℚ` is unramified away from `2`); the generation
hypothesis `_hgen` is not consumed — any `K` with an embedding of `E`
carries the member. -/
theorem exists_realization_at_two_generated_of_not_isIrreducible
    [Algebra R (AlgebraicClosure ℚ_[p])]
    [ContinuousSMul R (AlgebraicClosure ℚ_[p])]
    (hZinj : Function.Injective (algebraMap ℤ_[p] R))
    (hRinj : Function.Injective (algebraMap R (AlgebraicClosure ℚ_[p])))
    (hρ : IsHardlyRamified hpodd hv ρ)
    (hred : ¬ (ρ.baseChange (AlgebraicClosure ℚ_[p])).IsIrreducible)
    {E : Type v} [Field E] [NumberField E] (ψ : E →+* AlgebraicClosure ℚ_[p])
    (S : Finset (HeightOneSpectrum (NumberField.RingOfIntegers ℚ)))
    (Pv : HeightOneSpectrum (NumberField.RingOfIntegers ℚ) → Polynomial E)
    (heig : ∀ v ∉ S,
      (ρ.charFrob v).map (algebraMap R (AlgebraicClosure ℚ_[p])) = (Pv v).map ψ)
    (K : IntermediateField ℚ_[2] (AlgebraicClosure ℚ_[2]))
    [FiniteDimensional ℚ_[2] K] (φ₀ : E →+* K)
    (_hgen : K = IntermediateField.adjoin ℚ_[2]
      (Set.range fun x : E => (φ₀ x : AlgebraicClosure ℚ_[2]))) :
    ∃ (T : Finset (HeightOneSpectrum (NumberField.RingOfIntegers ℚ)))
      (τ : GaloisRep ℚ K (Fin 2 → K)),
      ∀ v ∉ T, τ.IsUnramifiedAt v ∧ τ.charFrob v = (Pv v).map φ₀ := by
  classical
  -- the structure map `ℤ_2 → K` is continuous for the subspace topology
  have hcont : Continuous (algebraMap ℤ_[2] K) := by
    refine continuous_induced_rng.mpr ?_
    have hcomp : Continuous (algebraMap ℤ_[2] (AlgebraicClosure ℚ_[2])) := by
      rw [IsScalarTower.algebraMap_eq ℤ_[2] ℚ_[2] (AlgebraicClosure ℚ_[2])]
      exact (continuous_algebraMap ℚ_[2] (AlgebraicClosure ℚ_[2])).comp
        continuous_subtype_val
    exact hcomp.congr fun z =>
      IsScalarTower.algebraMap_apply ℤ_[2] K (AlgebraicClosure ℚ_[2]) z
  refine ⟨S ∪ {hp.out.toHeightOneSpectrumRingOfIntegersRat,
    Nat.prime_two.toHeightOneSpectrumRingOfIntegersRat},
    cycDiagRep hcont (Pi.basisFun K (Fin 2)), ?_⟩
  intro w hwT
  obtain ⟨q, hq, rfl⟩ := exists_prime_toHeightOneSpectrumRingOfIntegersRat w
  have hqS : hq.toHeightOneSpectrumRingOfIntegersRat ∉ S := fun hmem =>
    hwT (Finset.mem_union_left _ hmem)
  have hqp : q ≠ p := by
    rintro rfl
    exact hwT (Finset.mem_union_right _ (Finset.mem_insert_self _ _))
  have hq2 : q ≠ 2 := by
    rintro rfl
    exact hwT (Finset.mem_union_right _
      (Finset.mem_insert_of_mem (Finset.mem_singleton_self _)))
  refine ⟨isUnramifiedAt_cycDiagRep_of_ne hcont (Pi.basisFun K (Fin 2)) hq hq2, ?_⟩
  rw [charFrob_cycDiagRep_of_ne hcont (Pi.basisFun K (Fin 2)) hq hq2,
    eisenstein_Pv_eq_of_not_isIrreducible hpodd hv hZinj hRinj hρ hred ψ heig hq hqp hqS,
    map_X_sub_one_mul_X_sub_natCast]

/-- **Automorphy atom at the even prime, generated coefficients**
(PROVEN assembly as of 2026-07-23 — see the DECOMPOSED note at the
end): given a finite-dimensional coefficient subfield `K ⊆ ℚ̄_₂` which
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
keeps the fused Eichler–Shimura + local–global shape. RE-AUDIT
(2026-07-23): confirmed against the actual pin — see the refreshed
RE-AUDIT note at `exists_hardlyRamified_integral_realizations_core`;
item (3) there records why a minimal interface SHARED with the odd-ℓ
atom was examined and rejected (no definable carrier; the carrier-free
version degenerates to the conjunction of the two atoms; this leaf's
generated-coefficient-field shape is already the zero-slack
Eichler–Shimura output).

DECOMPOSED (2026-07-23, opening the modularity subtree — superseding
the "no carrier" conclusion above exactly as at the odd-`ℓ` atom: the
interface file provides the Diamond–Shurman 5.8.5 carrier
`Modularity.IsWeightTwoEigenform` as real code) into a PROVEN
dichotomy assembly over three strictly shallower sorried nodes:

1. `Modularity.exists_weightTwoEigenform_of_isIrreducible` (interface
   sorry, SHARED with the odd-`ℓ` atom) — the level-2 eigenform behind
   the eigensystem on the irreducible branch.
2. `Modularity.exists_realization_at_two_of_weightTwoEigenform`
   (interface sorry, `ρ`-free) — Eichler–Shimura/Deligne at `λ ∣ 2`
   for level-2 eigenforms, over exactly the generated coefficient
   field; also dischargeable via `dim S₂(Γ₀(2)) = 0`.
3. `exists_realization_at_two_generated_of_not_isIrreducible` (PROVEN
   assembly as of 2026-07-24, above; one `ρ`-free arithmetic sub-leaf
   remains sorried) — the reducible/Eisenstein branch (`1 ⊕ χ_cyc,2`
   over `K`).

The assembly (below) is the same excluded-middle split on
irreducibility of `ρ ⊗ ℚ̄_p` as at the odd-`ℓ` atom. -/
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
      ∀ v ∉ T, τ.IsUnramifiedAt v ∧ τ.charFrob v = (Pv v).map φ₀ := by
  by_cases hirr : (ρ.baseChange (AlgebraicClosure ℚ_[p])).IsIrreducible
  · -- modular branch: level-2 eigenform existence + attachment at `λ ∣ 2`
    obtain ⟨f, S', hf, hmatch⟩ :=
      Modularity.exists_weightTwoEigenform_of_isIrreducible hpodd hv hZinj hRinj
        hρ hirr ψ S Pv heig
    exact Modularity.exists_realization_at_two_of_weightTwoEigenform S' Pv hf
      hmatch K φ₀ hgen
  · -- Eisenstein branch: the reducible eigensystem is realized explicitly
    exact exists_realization_at_two_generated_of_not_isIrreducible hpodd hv hZinj
      hRinj hρ hirr ψ S Pv heig K φ₀ hgen

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
