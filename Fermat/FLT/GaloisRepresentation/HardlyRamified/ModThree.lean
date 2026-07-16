/-
Copyright (c) 2025 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard
-/
module

public import Fermat.FLT.GaloisRepresentation.HardlyRamified.Defs

/-!
# Mod-3 hardly ramified representations

A mod-3 hardly ramified representation is shown to be an extension of
the trivial character by the mod-3 cyclotomic character.
-/

@[expose] public section

namespace GaloisRepresentation.IsHardlyRamified

local notation3 "Γ" K:max => Field.absoluteGaloisGroup K

universe u

set_option warn.sorry false in
/-- **Mod-3 reducibility** (sorry node): a mod-3 hardly ramified
representation has a `Γ ℚ`-stable proper nonzero submodule. Content:
if irreducible, then absolutely irreducible (`OddAbsIrred`, vendored
PROVEN — oddness gives complex conjugation a 1-dim fixed space), the
projective image is a subgroup of `PGL₂(𝔽̄₃)` classified by Dickson
(vendored PROVEN), and the hardly-ramified ramification constraints
(unramified outside 3, flat at 3, tame at 2) eliminate every case via
discriminant bounds — the classical Serre §5.4/Tate argument for
`p = 3`. (Upstream comment: `Field k` can probably be relaxed to
`(3 : k) = 0`.) -/
theorem mod_three_reducible {k : Type u} [Finite k] [Field k] [Algebra ℤ_[3] k]
    [TopologicalSpace k] [DiscreteTopology k]
    (V : Type*) [AddCommGroup V] [Module k V] [Module.Finite k V] [Module.Free k V]
    (hV : Module.rank k V = 2) {ρ : GaloisRep ℚ k V}
    (hρ : IsHardlyRamified (show Odd 3 by decide) hV ρ) :
    ∃ W : Submodule k V, W ≠ ⊥ ∧ W ≠ ⊤ ∧
      ∀ g : Γ ℚ, W.map (ρ g) ≤ W :=
  sorry

set_option warn.sorry false in
/-- **Trivial quotient from the stable line** (sorry node): given a
`Γ ℚ`-stable proper nonzero submodule (a line, by rank 2) of a mod-3
hardly ramified representation, the QUOTIENT character is trivial —
producing the equivariant surjection `π` onto the trivial 1-dimensional
representation. Content: the two characters of the resulting extension
multiply to the mod-3 cyclotomic character (`det` condition of
`IsHardlyRamified`); the hardly-ramified conditions make the quotient
character unramified everywhere (unramified outside 3 directly;
flatness at 3 forces the quotient of the connected-étale sequence to be
unramified at 3 as well); Minkowski-style triviality (the machinery of
`open_normal_subgroup_eq_top_of_inertia_le`, already derived) closes.
If instead the SUB-character is the trivial one, swap via the second
stable line obtained from semisimplicity or run the argument on the
dual — the classical bookkeeping of Serre §5.4. -/
theorem mod_three_of_stable_line {k : Type u} [Finite k] [Field k] [Algebra ℤ_[3] k]
    [TopologicalSpace k] [DiscreteTopology k]
    (V : Type*) [AddCommGroup V] [Module k V] [Module.Finite k V] [Module.Free k V]
    (hV : Module.rank k V = 2) {ρ : GaloisRep ℚ k V}
    (hρ : IsHardlyRamified (show Odd 3 by decide) hV ρ)
    (W : Submodule k V) (hW0 : W ≠ ⊥) (hWtop : W ≠ ⊤)
    (hWstable : ∀ g : Γ ℚ, W.map (ρ g) ≤ W) :
    ∃ (π : V →ₗ[k] k) (_ : Function.Surjective π),
    ∀ g : Γ ℚ, ∀ v : V, π (ρ g v) = π v :=
  sorry

/-- **Mod-3 classification** (DERIVED 2026-07-16 from the two nodes
above): a mod-3 hardly ramified representation is an extension of the
trivial character by the (mod-3 cyclotomic) character: there is a
`Γ ℚ`-equivariant surjection onto the trivial 1-dimensional
representation. Input to **B6c** (`Threeadic.lean`). Reducibility
(`mod_three_reducible`, the Dickson/discriminant content) produces the
stable line; the quotient-character analysis
(`mod_three_of_stable_line`) produces the surjection. -/
theorem mod_three {k : Type u} [Finite k] [Field k] [Algebra ℤ_[3] k] --
    [TopologicalSpace k] [DiscreteTopology k]
    (V : Type*) [AddCommGroup V] [Module k V] [Module.Finite k V] [Module.Free k V]
    (hV : Module.rank k V = 2) {ρ : GaloisRep ℚ k V}
    (hρ : IsHardlyRamified (show Odd 3 by decide) hV ρ) :
    ∃ (π : V →ₗ[k] k) (_ : Function.Surjective π),
    ∀ g : Γ ℚ, ∀ v : V, π (ρ g v) = π v := by
  obtain ⟨W, hW0, hWtop, hWstable⟩ := mod_three_reducible V hV hρ
  exact mod_three_of_stable_line V hV hρ W hW0 hWtop hWstable

end GaloisRepresentation.IsHardlyRamified
