/-
The proof spine here is adapted from the FLT project's `FLT/Proof.lean`
(https://github.com/ImperialCollegeLondon/FLT), Copyright (c) 2026 Kevin
Buzzard, released under the Apache 2.0 license.
-/
import Fermat.FLT.FreyCurve.Mazur
import Fermat.FLT.GaloisRepresentation.HardlyRamified.Frey

/-!
# Fermat's Last Theorem for prime exponents `p ≥ 5`

This is the hard case of Fermat's Last Theorem, proved by Wiles and
Taylor–Wiles (1995) via the Frey–Serre–Ribet reduction to modularity of
semistable elliptic curves over `ℚ`.

The chain (mirroring the "boss theorems" B2–B4 of the FLT project's
`Proof.lean`):

* a counterexample with prime exponent `p ≥ 5` yields a `FreyPackage`
  (`Fermat/FLT/FreyCurve/FreyPackage.lean`, proven);
* the mod-`p` Galois representation on the `p`-torsion of the Frey curve of a
  Frey package is irreducible — Mazur (`Fermat/FLT/FreyCurve/Mazur.lean`,
  an open `sorry` node: to be fully formalized, no citation shortcuts);
* that representation is *not* irreducible — Wiles' modularity theorem plus
  Ribet's level lowering plus the absence of weight-2 level-2 cusp forms
  (`FreyPackage.galoisRep_not_irreducible` below, the CURRENT SORRY ROOT,
  = statement B4 of the FLT project).

See `PROGRESS.md` for the full dependency tree.
-/

open WeierstrassCurve

/-- **B4**: if `E` is the Frey curve attached to a Frey package `(a, b, c, p)`,
then the Galois representation on `E[p]` is *not* irreducible.

This is the hard arithmetic input: by Wiles–Taylor–Wiles the Frey curve
(being semistable) is modular; by Ribet's level-lowering the associated
mod-`p` representation, if irreducible, would come from a weight-2 cusp form
of level 2; there are no nonzero weight-2 cusp forms of level 2. -/
theorem FreyPackage.galoisRep_not_irreducible (P : FreyPackage) :
    let E := P.freyCurve
    let p := P.p
    have : Fact p.Prime := ⟨P.pp⟩
    ¬ GaloisRep.IsIrreducible (E.galoisRep p P.hppos) :=
  FreyCurve.torsion_not_isIrreducible P

/-- **There is no Frey package**: the `p`-torsion of its Frey curve would be
both irreducible (Mazur) and not irreducible (Wiles, Taylor–Wiles, Ribet). -/
theorem FreyPackage.false (P : FreyPackage) : False :=
  P.galoisRep_not_irreducible P.mazur

/-- **Fermat's Last Theorem for prime exponents `p ≥ 5`** (Wiles,
Taylor–Wiles). If `p ≥ 5` is prime, then `a ^ p + b ^ p = c ^ p` has no
solutions in nonzero natural numbers. -/
theorem fermatLastTheoremFor_of_five_le (p : ℕ) (hp : p.Prime) (h5 : 5 ≤ p) :
    FermatLastTheoremFor p :=
  FreyPackage.fermatLastTheoremFor_p_ge_5 ⟨FreyPackage.false⟩ p h5 hp
