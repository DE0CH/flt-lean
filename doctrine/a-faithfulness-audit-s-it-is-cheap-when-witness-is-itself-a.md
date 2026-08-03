## A FAITHFULNESS AUDIT'S "IT IS CHEAP WHEN …" WITNESS IS ITSELF A PROOF OBLIGATION

(2026-07-31.) Audits in this development routinely end with a cheap case — "this structure is easy
to satisfy when `A` is finite; here is the witness" — and that clause is doing real work: it is the
evidence that the leaf is not asking a producer for MORE than the mathematics supplies. It is also
the clause nobody checks, because it reads like a reassurance rather than a claim.

`CubeModel`'s (`Fermat/FLT/Mathlib/NumberTheory/ProjectiveHeight.lean`) said "cheap exactly when
`A(ℚ)` is finite — `dim = 1`, `coords ≡ ![1]`, `cube = z`, `relDim = 0`". Two of its four
components are wrong, and both understate the witness: a CONSTANT `coords` satisfies
`injective_of_smul` only for a SUBSINGLETON group (take `c = 1` and the field forces `P = Q` for
every pair), and `z` is homogeneous of degree `1` where `cube_homogeneous` demands `2`. The claim
is true — an indicator witness works — but the recipe as written supported a far weaker statement
than the one it was cited for, and it had been copied verbatim into the audit of the leaf that has
to produce the structure (`nonempty_cubeModel_of_isAmpleSheaf_cube`).

Check the cheap case field by field against the structure, the same way you would check a
counterexample. It costs minutes, it is the half of an audit that can be checked without the
literature, and a wrong one propagates by quotation.

