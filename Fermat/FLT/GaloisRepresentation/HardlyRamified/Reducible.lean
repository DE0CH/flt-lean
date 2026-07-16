/-
Reducible.lean — own work for the Fermat project (not vendored from the FLT
project).

**B5**: a hardly ramified mod-`ℓ` Galois representation with `ℓ ≥ 5` is not
irreducible.

This is the deep arithmetic input to Fermat's Last Theorem. The mathematical
route (which this tree must eventually formalize in full, per the
no-citation-terminal-nodes policy):

* an irreducible hardly ramified mod-`ℓ` representation lifts to an `ℓ`-adic
  hardly ramified representation (a modularity-lifting / deformation-theory
  argument — the FLT project's B6(a));
* the lift fits into a weakly compatible family (B6(b)), so there is a
  hardly ramified `3`-adic member;
* hardly ramified `3`-adic representations are classified: they are
  extensions of the trivial character by the cyclotomic character (B6(c)),
  hence reducible — contradiction with irreducibility of the residual
  representation.

Equivalently, in classical language: by modularity (Wiles–Taylor–Wiles) and
Ribet's level lowering, an irreducible hardly ramified representation would
come from a weight-2 cusp form of level 2, and no nonzero such forms exist.

The statement is recorded here as an explicit `sorry` node of the dependency
tree, to be decomposed further (B6a/B6b/B6c) in subsequent layers.
-/
module

public import Fermat.FLT.GaloisRepresentation.HardlyRamified.Defs
public import Fermat.FLT.GaloisRepresentation.HardlyRamified.Lift
public import Mathlib.Topology.Instances.ZMod

@[expose] public section

open GaloisRepresentation

/-- The natural `ℤ_ℓ`-algebra structure on `ℤ/ℓℤ`. -/
noncomputable local instance (ℓ : ℕ) [Fact ℓ.Prime] : Algebra ℤ_[ℓ] (ZMod ℓ) :=
  RingHom.toAlgebra PadicInt.toZMod

/-- **B5**: a hardly ramified mod-`ℓ` Galois representation of `Gal(ℚ̄/ℚ)`
with `ℓ ≥ 5` is not irreducible.

(Wiles–Taylor–Wiles modularity + Ribet level-lowering + the vanishing of the
space of weight-2 level-2 cusp forms; to be proven here via the hardly
ramified lifting route, see the module docstring.) -/
theorem GaloisRepresentation.not_isIrreducible_of_isHardlyRamified
    {ℓ : ℕ} [Fact ℓ.Prime] (hℓOdd : Odd ℓ) (hℓ5 : 5 ≤ ℓ)
    {V : Type*} [AddCommGroup V] [Module (ZMod ℓ) V]
    [Module.Finite (ZMod ℓ) V] [Module.Free (ZMod ℓ) V]
    (hdim : Module.rank (ZMod ℓ) V = 2)
    {ρ : GaloisRep ℚ (ZMod ℓ) V}
    (h : IsHardlyRamified hℓOdd hdim ρ) :
    ¬ ρ.IsIrreducible := by
  -- B5 from B6a + (B6b ∘ B6c) + Chebotarev–Brauer–Nesbitt: suppose `ρ` is
  -- irreducible; lift it (B6a), pin the residual Frobenius characteristic
  -- polynomials to those of `1 ⊕ χ̄` through the compatible family and the
  -- 3-adic classification (B6bc), and conclude that `ρ` cannot have been
  -- irreducible.
  intro hirr
  obtain ⟨L⟩ := exists_hardlyRamifiedLift hℓOdd hdim hℓ5 h hirr
  obtain ⟨S, hS⟩ := residual_charFrob_eq hℓOdd hℓ5 L
  exact not_isIrreducible_of_charFrob_eq S hS hirr
