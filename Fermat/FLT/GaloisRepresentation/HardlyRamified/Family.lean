/-
Copyright (c) 2025 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard
-/
module

public import Fermat.FLT.GaloisRepresentation.HardlyRamified.Defs
public import Fermat.FLT.Deformations.RepresentationTheory.GaloisRepFamily
import Mathlib.Algebra.Field.ULift
import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Mathlib.LinearAlgebra.Charpoly.BaseChange

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

/-- **Algebraicity/finiteness core of the eigensystem stratum** (sorry
node): away from a finite set of places, the coefficients of the mapped
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
bare mathematical content in minimal vocabulary. -/
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
        ((ρ.charFrob v).map (algebraMap R (AlgebraicClosure ℚ_[p]))).coeff n ∈ E :=
  sorry

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

/-- Every finite place of `ℚ` is the place of a rational prime (PROVEN):
the surjectivity half of the primes ↔ places dictionary, needed to
convert the prime-indexed unramifiedness field of `IsHardlyRamified`
into the place-indexed unramifiedness that
`GaloisRepFamily.isCompatible` consumes. -/
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

/-- **Automorphy core of the realization stratum, odd residue
characteristics** (sorry node): the eigensystem `(E, S, Pv)` attached
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
this leaf is the sole surviving automorphy sorry at odd `ℓ`. -/
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
      ∀ (ℓ : ℕ) (hℓ : Fact ℓ.Prime) (hℓodd : Odd ℓ)
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
        (r : AlgebraicClosure ℚ_[ℓ] ⊗[A] W ≃ₗ[AlgebraicClosure ℚ_[ℓ]]
          Fin 2 → AlgebraicClosure ℚ_[ℓ]),
        IsHardlyRamified hℓodd hW τ ∧
        ∀ v ∉ T, (ℓ : NumberField.RingOfIntegers ℚ) ∉ v.asIdeal →
          τ.IsUnramifiedAt v ∧
          (τ.charFrob v).map (algebraMap A (AlgebraicClosure ℚ_[ℓ])) =
            (Pv v).map φ :=
  sorry

/-- **Residue characteristic 2 member of the realization stratum**
(sorry node): the eigensystem `(E, S, Pv)` is realized at the even
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
model. -/
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
            (Pv v).map φ :=
  sorry

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

1. `exists_hardlyRamified_integral_realizations` (sorry node) — at odd
   `ℓ`, the hardly ramified integral model `τ` over `A ↪ ℚ̄_ℓ` with
   the unramifiedness and charpoly matching stated at the integral
   level (with exceptional set `T₁`). The sole automorphy content at
   odd `ℓ`; see its docstring for the vocabulary obstruction to a
   further newform-datum split and the Brauer–Nesbitt soundness
   constraint forcing the model to be produced there.
2. `exists_realizations_at_two` (sorry node) — the bare member at
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
   2026-07-23 both strata are PROVEN assemblies; the surviving sorried
   leaves are `exists_finiteDimensional_coeff_field` (the Hecke-field
   finiteness core) and `exists_realizations_of_eigensystem` (the
   `λ`-adic realizations of the eigensystem).

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
