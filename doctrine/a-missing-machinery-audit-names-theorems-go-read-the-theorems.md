## A "MISSING MACHINERY" AUDIT NAMES THEOREMS. GO READ THE THEOREMS.

(2026-07-31, `flt-lean-246`.) A mature leaf in this tree carries an inventory
paragraph — "what exists and is usable is X, Y, Z; what is missing is W". Those
paragraphs are written carefully and are usually right about what is ABSENT.
They are much less reliable about **how strong what is PRESENT is**, because the
author summarised the cited theorem in one clause instead of quoting it.

`exists_heightOneSpectrum_mul_span_eq_span_of_sup_eq_top` (Dirichlet for a
narrow ray class) had, in its own docstring and in its consumer's, the sentence
"`GaloisRepresentation/Chebotarev.lean` carries `infinite_setOf_isArithFrobAt`
…, so the DENSITY half does not have to be rebuilt". Read as prose that says
"some density material is available". The theorem's actual STATEMENT is **full
Chebotarev in ideal-theoretic existence form**: for every finite normal `L/F`
and every `τ ∈ Gal(L/F)`, infinitely many places of `F` are unramified in `L`
and carry `τ` as an arithmetic Frobenius — proven, in a file with no `sorry` in
it. Once that is read rather than summarised, the leaf becomes a fifteen-line
assembly over a citation that asks only for the ray class FIELD, with no
analysis in it at all. The same file also holds Weber's per-narrow-ray-class
counting theorem, which none of the three audits in that block mentions.

So the cheap check, before believing any inventory: `grep -n "theorem <name>"`
the cited file and **read the statement and the sorry status**, not the
docstring's clause about it. It costs one grep and it is the difference between
"needs a theory" and "needs fifteen lines".

**The check cuts BOTH ways, and the same agent got the other direction wrong an
hour later.** Two new modules (`NumberField/ArtinSymbol.lean`,
`NumberField/UnramifiedClassFieldExistence.lean`) had appeared on `main` with a
promising declaration list, and I wrote "the unramified existence theorem has
landed in the tree" into a docstring and a commit message on the strength of
that list. It has not: their two core statements
(`exists_hilbertClassField_artinIso`, `artinMap_toPrincipalIdeal`) are `sorry`.
A declaration list is not a proof status. Run `grep -n sorry` on the file and
attribute each hit to its enclosing declaration before writing "is in the tree"
anywhere — the phrase is read downstream as "usable today", and an inventory
that is wrong in this direction sends the next agent to import a leaf.

**The reusable cut this exposed, which applies wherever a leaf asks for a PRIME
with a prescribed splitting/class behaviour:** do not ask for the prime. Ask for
the finite normal extension and the Galois element that CUT OUT the condition,
and let in-tree Chebotarev produce the prime. That moves the whole analytic /
density half out of the citation and leaves the abelian existence theorem,
which is a different and much better-isolated obligation. Two things make the
resulting leaf safe rather than vacuous, and both must be checked: exclude the
places dividing the modulus explicitly (at `w ∣ 𝔣` the ray-class conclusion is
*unsatisfiable*, so a leaf without that clause is FALSE, not merely hard), and
note that Chebotarev itself forbids discharging the leaf by choosing an `L, τ`
whose Frobenius set is empty — the set is infinite for every `L, τ`, and
`Ideal.finite_factors` removes the finitely many divisors of the modulus.

