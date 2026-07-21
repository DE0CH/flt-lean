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

/-- **B6b** (sorry node): a hardly ramified `p`-adic representation lives in
a compatible family of Galois representations, all of whose
odd-residue-characteristic members are themselves hardly ramified. -/
theorem mem_isCompatible (hρ : IsHardlyRamified hpodd hv ρ) :
    IsInHardlyRamifiedFamily (p := p) ρ :=
  sorry

end GaloisRepresentation.IsHardlyRamified
