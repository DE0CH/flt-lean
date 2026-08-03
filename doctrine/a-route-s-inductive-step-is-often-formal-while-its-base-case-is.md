## A ROUTE'S INDUCTIVE STEP IS OFTEN FORMAL WHILE ITS BASE CASE IS THE WHOLE THEOREM — PERFORM THE STEP
(2026-08-01, `flt-lean-382`, on the second fundamental inequality
`index_relNormClassSubgroup_le_finrank_of_isUnramifiedAtInfinitePlaces` in
`NumberField/UnramifiedClassFieldExistence.lean`.)  A mature leaf's **Route** paragraph
routinely reads *"X for CYCLIC extensions, extended to abelian by induction along a cyclic
subextension using multiplicativity of Y in towers"*.  That sentence names two things of
very different price, and the second half is frequently **pure formal bookkeeping with no
arithmetic in it at all** — so it can be performed today, by anyone, without touching the
mathematics.  Here the whole dévissage (build the cyclic subgroup, take its fixed field,
inherit both unramifiedness hypotheses in both directions, induct on the degree) came to
~200 lines and compiled essentially first try, leaving the CYCLIC case as the only leaf.
**The test for whether the step is formal: is the quantity being chained an INDEX, a RANK,
a DEGREE — i.e. multiplicative along a tower — and is the multiplicativity a statement about
a GROUP HOMOMORPHISM you can name?**  If yes, mathlib's `Subgroup.index_map`
(`(H.map f).index = (H ⊔ f.ker).index * f.range.index`) plus antitonicity of the index does
the entire estimate in five lines, and everything else is instance plumbing.
**AND A RECORDED "THAT DÉVISSAGE DOES NOT WORK" NOTE MAY BE ABOUT A DIFFERENT QUANTITY.**
`ArtinSymbol.lean` carried, correctly and in bold, *"it does NOT follow for abelian `L/K` by
dévissage along a chain of cyclic steps: each step gives `[Fᵢ₊₁ : Fᵢ] ≤ h_{Fᵢ}`, and
multiplying them bounds `[L : K]` by `∏ h_{Fᵢ}`, not by `h_K`"*.  True, and about the naked
DEGREE inequality.  The NORM INDEX chains the other way and the same dévissage is sound —
which the same file elsewhere says in as many words (*"norm groups shrink under composita;
nothing analogous holds on the Galois side"*).  **Before inheriting a dévissage verdict,
check which quantity it was measuring and which way that quantity is monotone under the
combination.**  Two notes in one cluster can be individually right and jointly misleading.
### A FUNCTORIALITY MATHLIB LACKS MAY BE ONE `Function.surjInv` AWAY
Same task.  `ClassGroup.relNormHom : ClassGroup S →* ClassGroup R` (the ideal norm on class
groups) is **not** at this pin — mathlib has only `ClassGroup.extendedHom`, the pushforward
in the opposite direction — and it cannot be transported through
`ClassGroup R = (FractionalIdeal R⁰ K)ˣ ⧸ (principal)` because there is no relative norm on
FRACTIONAL ideals either.  It is nevertheless ~30 lines, by a recipe worth reusing whenever a
group is presented by a surjection from a MONOID:
* `ClassGroup.mk0 : (Ideal R)⁰ →* ClassGroup R` is a monoid hom and is SURJECTIVE
  (`ClassGroup.mk0_surjective`), and `ClassGroup.mk0_eq_mk0_iff` characterises its fibres;
* so prove the intended composite is constant on those fibres (here: apply `Ideal.relNorm` to
  `(x) I = (y) J`, using `Ideal.relNorm_singleton` and `Algebra.intNorm_eq_zero`), define the
  FUNCTION by `Function.surjInv`, and get `map_mul` from `MonoidHom.mk'` after
  `obtain ⟨I, rfl⟩ := mk0_surjective a` reduces both sides to generators;
* then never unfold it again: `relNormHom_mk0` is the whole interface, and transitivity in a
  tower (`relNormHom_comp`) is `Ideal.relNorm_relNorm` plus one `MonoidHom.ext`.
Lands in `Fermat/FLT/Mathlib/RingTheory/ClassGroupRelNorm.lean`.  The general shape —
*a hom out of a group presented as the image of a monoid factors as soon as it is constant on
the fibres, and `surjInv` is enough to build it* — applies to every "the norm/trace/degree
induces a map on classes" statement in this development.
### REPLACING THE FIRST PARAGRAPH OF A DOCSTRING ORPHANS THE REST — the merge-damage shape, self-inflicted
Same task, one build cycle.  An `Edit` whose `old_string` was the first four lines of a leaf's
docstring (to re-head it) left the remaining forty lines as **bare prose after the new
closing delimiter**, and the file then failed with a cascade of `unexpected token '*';
expected 'lemma'` / `unexpected token ','; expected ':'` **250 lines below the edit** — the
exact signature this file catalogues as merge damage, produced by an ordinary edit.
So: **when re-heading a docstring, replace the WHOLE docstring**, and after any edit that
touches a doc comment run the depth-plus-strays scan before building.  It is ten lines of
Python, it costs a second, and it distinguishes this from a real syntax error immediately:
    depth 0, see `/-` -> depth+1;  depth>0, see `-/` -> depth-1;
    depth 0, see `--` -> skip line;  depth 0, see `-/` -> RECORD IT
    # final depth must be 0 AND the stray list must be empty
