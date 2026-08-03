## A TASK PROMPT NAMING A PROVEN HELPER IS NOT EVIDENCE THAT YOUR MODULE CAN IMPORT IT
(Same run.) The dispatch said, correctly, that
`AlgebraicGeometry.birationalOver_affineLine_of_ord_eq_sub`
(`Fermat/FLT/Mathlib/AlgebraicGeometry/CurveDivisorDegree.lean`) is PROVEN and *"has exactly
the geometric conclusion"*, and told me to reduce the genus-`0` branch to producing its input.
It is unreachable from `X0.lean`: `CurveDivisorDegree` collides with
`PrincipalDivisorDegree` on `AlgebraicGeometry.Scheme.ord_one` and `Scheme.ord_inv`, X0
imports the second, and X0 is the only module that sees both — so importing it is
`environment already contains …` before a line elaborates. X0's own import block says so, in
a comment, twenty lines long, at line 1063.
This is the mirror of the standing rule *"NOT IN MATHLIB, NOT IN `~/cs/FLT` — CHECK YOUR OWN
IMPORT LIST FIRST"*: there a theorem is present and believed absent; here it is present,
believed reachable, and is not. **Both are answered by the same two commands, and the second
is the one nobody runs:**
    grep -rn '<the helper>' Fermat/ --include=*.lean | head        # where does it live
    grep -n 'import.*<that module>' <your target module>           # can you SEE it
A prompt is written by someone reading the helper's file, not your module's header. When the
answer is "no", do not add the import and do not reconcile the collision as a side quest —
state your leaf in a form the reachable API can serve, and record the reduction the
unreachable one would give in the docstring, so the reconciliation's payoff is written down
where the next owner will find it.
