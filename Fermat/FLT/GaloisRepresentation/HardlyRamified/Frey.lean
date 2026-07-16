/-
Copyright (c) 2025 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard
-/
module

public import Fermat.FLT.GaloisRepresentation.HardlyRamified.Defs
-- VENDORING ADDITION: B5 (hardly ramified ⇒ not irreducible), backing
-- `torsion_not_isIrreducible` below.
public import Fermat.FLT.GaloisRepresentation.HardlyRamified.Reducible
public import Fermat.FLT.FreyCurve.Basic
public import Fermat.FLT.EllipticCurve.Torsion
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.NumberTheory.ArithmeticFunction.Misc

/-!
# The Frey curve gives a hardly ramified representation

We prove that the `ℓ`-torsion of the Frey curve attached to a Frey package
is a hardly ramified Galois representation, and that this representation is
irreducible.
-/

@[expose] public section

variable (P : FreyPackage)

open GaloisRepresentation

/-- The natural `ℤ_p`-algebra structure on `ℤ/pℤ`. -/
noncomputable local instance (p : ℕ) [Fact p.Prime] : Algebra ℤ_[p] (ZMod p) :=
  RingHom.toAlgebra PadicInt.toZMod

/-- We cannot hope to make a constructive decidable equality on `AlgebraicClosure ℚ` because
it is defined in a completely nonconstructive way, so we add the classical instance. -/
noncomputable instance : DecidableEq (AlgebraicClosure ℚ) := Classical.typeDecidableEq _

theorem FreyCurve.torsion_isHardlyRamified :
    haveI : Fact (P.p.Prime) := ⟨P.pp⟩
    -- VENDORING CHANGE: the rank-2 hypothesis (a `sorry` in statement
    -- position upstream) is discharged by `p_torsion_rank`.
    IsHardlyRamified P.hp_odd
      ((P.freyCurve.map (algebraMap ℚ (AlgebraicClosure ℚ))).p_torsion_rank
        (Nat.cast_ne_zero.mpr P.hp0))
      (P.freyCurve.galoisRep P.p (show 0 < P.p from P.hppos)) :=
  sorry

-- VENDORING CHANGE: the `sorry` is replaced by the reduction to **B5**
-- (`GaloisRepresentation.not_isIrreducible_of_isHardlyRamified`, in
-- `Reducible.lean`): the torsion representation is hardly ramified
-- (`torsion_isHardlyRamified` above), and hardly ramified mod-`ℓ`
-- representations with `ℓ ≥ 5` are not irreducible.
theorem FreyCurve.torsion_not_isIrreducible :
    haveI : Fact (P.p.Prime) := ⟨P.pp⟩
    ¬ GaloisRep.IsIrreducible (P.freyCurve.galoisRep P.p P.hppos) :=
  haveI : Fact (P.p.Prime) := ⟨P.pp⟩
  GaloisRepresentation.not_isIrreducible_of_isHardlyRamified P.hp_odd P.hp5
    ((P.freyCurve.map (algebraMap ℚ (AlgebraicClosure ℚ))).p_torsion_rank
      (Nat.cast_ne_zero.mpr P.hp0))
    (FreyCurve.torsion_isHardlyRamified P)
