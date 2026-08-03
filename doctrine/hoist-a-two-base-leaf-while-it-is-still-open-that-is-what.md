## HOIST A TWO-BASE LEAF WHILE IT IS STILL OPEN — that is what halves the count
(2026-07-31, `WeilPairingDet.lean`.) The same theorem sat as a live `sorry` in two
modules that do not import each other: Silverman *AEC* III.8.1 at an arbitrary base
(`MoretBailly.exists_weilPairing_mu_nondeg_of_natCast_ne_zero`) and the same six
clauses with the base fixed at `𝔽_q` and `σ` specialised to Frobenius
(`MazurTorsion.exists_weilPairing_mu_nondeg_of_coprime`). Both docstrings said
"closing one closes the other" and both were waiting for the other to be CLOSED
first. Neither ever would have been: the statement is an 8 500-line divisor
construction.
The move that worked costs nothing and does not need the mathematics: **put the
GENERAL statement in a module upstream of both, prove there whatever is not the
arithmetic input, leave ONE new leaf, and rewire BOTH consumers to it now.** The
𝔽_q copy became five lines (`Nat.Coprime N q` is `(N : ZMod q) ≠ 0`; the arbitrary
`k`-automorphism is instantiated at the Frobenius, which already existed as
`HasseBound.frobAlgEquiv`). Two leaves became one, the same day, with the hard
part untouched.
Corollary about what counts as progress: **an EQUIVALENCE-preserving cut is still
a cut.** Here the new leaf (`det ρ_{E,n} = χ_n`, one equation in `k̄`) is
equivalent to the old one — pairing ⟹ determinant and determinant ⟹ pairing — so
no mathematics was removed. What left the frontier permanently is the ~120 lines
of rank-two bookkeeping (bimultiplicativity, alternation, `e ^ n = 1`,
nondegeneracy, transport through the discrete logarithm) that every successor at
every base and level would otherwise have had to redo. Do not decline a cut
because "it does not make the hard part easier"; ask whether it deletes work that
would otherwise be repeated, and whether it makes the residue a shape another
proven theorem in the tree already has (here `WeilPairing.det_galoisRep_eq_cyclotomic`
over `ℚ`, which is now visibly a template rather than an unrelated theorem).
