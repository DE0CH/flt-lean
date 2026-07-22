/-
Copyright (c) 2025 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard
-/
module

public import Fermat.FLT.GaloisRepresentation.HardlyRamified.Defs
public import Fermat.FLT.Deformations.RepresentationTheory.GaloisRepFamily

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

/-- **Eigensystem stratum** (sorry node): the Frobenius characteristic
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
shadow in the available vocabulary. -/
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
          (Pv v).map ψ :=
  sorry

/-- **Spreading stratum** (sorry node): a hardly ramified `p`-adic
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
here avoids quantifying over abstract families in the hypotheses. -/
theorem exists_family_of_eigensystem
    [Algebra R (AlgebraicClosure ℚ_[p])]
    [ContinuousSMul R (AlgebraicClosure ℚ_[p])]
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
        (ρ.baseChange (AlgebraicClosure ℚ_[p])).conj r' = σ hp ψ) :=
  sorry

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
   into the two sorried strata above: the eigensystem stratum
   (`exists_numberField_eigensystem` — the Frobenius data descend to a
   number field, i.e. the Hecke-field/eigenform-congruence content) and
   the spreading stratum (`exists_family_of_eigensystem` — the
   compatible family attached to the eigensystem, i.e.
   Eichler–Shimura/Deligne plus local-global compatibility).

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
  obtain ⟨i, hinj, -, hconti⟩ := hembed
  letI ia : Algebra R (AlgebraicClosure ℚ_[p]) := i.toAlgebra
  haveI ics : ContinuousSMul R (AlgebraicClosure ℚ_[p]) :=
    continuousSMul_of_algebraMap _ _ hconti
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
