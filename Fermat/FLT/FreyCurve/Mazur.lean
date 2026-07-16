/-
Copyright (c) 2023 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, Ruben Van de Velde, Pietro Monticone
-/
module

public import Fermat.FLT.FreyCurve.Basic
public import Fermat.FLT.EllipticCurve.Torsion
import Fermat.FLT.FreyCurve.MazurTorsion
import Fermat.FLT.GaloisRepresentation.HardlyRamified.Frey
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.NumberTheory.ArithmeticFunction.Misc
/-!

# Irreducibility of the p-torsion of the Frey curve

A deep result of Mazur implies that the Frey curve is irreducible.

-/

@[expose] public section

open WeierstrassCurve

/--
The p-torsion in the Frey curve associated to a counterexample to FLT is irreducible.
-/
theorem FreyPackage.mazur (P : FreyPackage) :
    let E := P.freyCurve
    let p := P.p
    have : Fact p.Prime := ⟨P.pp⟩
    GaloisRep.IsIrreducible (E.galoisRep p P.hppos) := by
  -- VENDORING CHANGE: the original proof is `knownin1980s`, the FLT
  -- project's universal axiom for pre-1990 results ("this is in Serre's
  -- 1987 Duke paper"). Per project policy no such terminal citation nodes
  -- are allowed. The theorem is now DERIVED from the two explicit sorry
  -- nodes of `Fermat/FLT/FreyCurve/MazurTorsion.lean`: were the
  -- representation reducible, Serre's §4.1 analysis
  -- (`exists_torsion_embedding_of_not_isIrreducible`) would produce an
  -- elliptic curve over ℚ whose rational points contain ℤ/2 × ℤ/2p,
  -- contradicting Mazur's torsion theorem (`mazur_torsion_bound`).
  by_contra hred
  obtain ⟨E', hE', φ, hφ⟩ := P.exists_torsion_embedding_of_not_isIrreducible hred
  haveI := hE'
  exact WeierstrassCurve.mazur_torsion_bound E' P.pp P.hp5 φ hφ
