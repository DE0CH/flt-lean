## A CORRECT "THE PIN LACKS X" AUDIT CAN HIDE THAT *THIS TREE* ALREADY PROVES X
(2026-07-31.) A task was commissioned to build `deg (div g) = 0` for a smooth proper curve,
on the strength of an audit — **entirely correct** — that `Mathlib` at this pin has no degree
of a divisor and no degree of a principal divisor, in any capitalisation.
`Fermat/FLT/ModularCurve/HyperellipticJacobian.lean` already carried
`PlaceData.degOf_divisor_eq_zero`, **PROVEN**, over the single leaf
`degOf_poleDivisor_eq_finrank_of_transcendental` (Stichtenoth I.4.11) — with the surrounding
bookkeeping (`div = div_0 − div_∞`, `div_0 g = div_∞ g⁻¹`, `K(g) = K(g⁻¹)`, the constant
case) already Lean.
**It was invisible because it is stated in a DIFFERENT FORMULATION.** That file works over an
abstract `PlaceSystem`/`PlaceData` interface — `ord : Places → F → ℤ` on the places of a
function field — sharing not one identifier with a scheme-theoretic search (`Scheme.ord`,
`AlgebraicCycle`, `divisor`, `degree`). **Identifier greps cannot cross a change of
formulation**, and `own.py`/`leafstat.py` are declaration-name based, so neither can they.
The correct pin-side absence claim is precisely what stops anyone looking further.
**The check is one command, because this development states its mathematics in PROSE in
docstrings, and prose survives a change of formulation where names do not:**
    grep -rn 'deg (div g) = 0' --include=*.lean Fermat/      # finds it instantly
So before building machinery for a NAMED CLASSICAL THEOREM, grep `Fermat/` for its INFORMAL
STATEMENT and for its CITATION (`Stichtenoth`, `I.4.11`, `Riemann–Roch`, `weak
approximation`) as well as for identifiers. When the theorem IS present in another
formulation the deliverable changes from "prove it" to "build the bridge" — and the two
formulations must be cut so they bottom out at the SAME single leaf, or you have
manufactured two open nodes where there is one.
This is the milder sibling of "Missing machinery may be DOWNSTREAM": there the theorem is in
a file that imports yours, so an identifier grep of the whole tree does find it. Here nothing
name-based can.
