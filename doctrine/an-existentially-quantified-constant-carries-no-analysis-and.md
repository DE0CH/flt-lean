## AN EXISTENTIALLY-QUANTIFIED CONSTANT CARRIES NO ANALYSIS — and the PROVEN theorem below you may depend on your leaf

(2026-07-31, `flt-lean-92`, `Modularity/TateModule.lean`.) Two traps, one leaf, and the
first of them is worth checking on every leaf in this tree whose conclusion contains a
real number.

**1. `∃ C : ℝ, … ≤ C` IS NOT A BOUND.** `exists_boundedLevelScalar_atPrime_finiteBase` was
titled *"THE RIEMANN HYPOTHESIS FOR `A'`"*, cited Weil 1948, Mumford §19 and Tate 1966,
and its docstring told a prover the residue needed `#A'(k_m) = deg(F^m − 1)` and
**positivity of the Rosati involution**. Its conclusion is

    ∃ C : ℝ, ∀ n, ∃ u, u − s n ∈ Iⁿ ∧ ∀ φ : D →+* ℂ, ‖φ u‖ ≤ C

and the docstring itself says `C = 2√N` is the sharp value *"but the constant is left
EXISTENTIAL because nothing downstream uses it"*. **That clause destroys the analysis.**
`D →+* ℂ` is a FINITE type for a number field (`NumberField.Embeddings` registers the
`Fintype`), so the moment a single global `t` exists, `Set.range (fun φ => ‖φ t‖)` is a
finite set of reals, `Set.Finite.bddAbove` hands you `C`, and the archimedean clause is
five lines with no arithmetic in it. What is left is *"the trace of Frobenius is a global
algebraic integer"* — Weil's **rationality** half, which follows from finite generation of
the endomorphism module and has nothing archimedean in it. Rationality and the Riemann
hypothesis are a whole theory apart, and the leaf was advertising the wrong one.

**The check is mechanical and takes a minute: instantiate the existential yourself.** If
the bounded object is a SINGLE object (not a family), or the index set is finite, or the
constant may depend on everything in sight, then the bound is decoration and the content
is whatever produces the object. Sharp constants only carry content when something
downstream reads them — and a docstring that says nothing does is telling you so.

**2. A PROVEN THEOREM 1000 LINES BELOW YOU MAY BE PROVEN *OVER* YOUR LEAF.** This file's
own "A LEAF CAN BE CLOSED BY MOVING CODE" and "A DECLARATION-ORDER LEAF CLOSES BY MOVING"
sections say to grep below for a proven counterpart. Here there was one, and it was
perfect: `exists_frobEndoCharEq_of_mult_finiteBase`, PROVEN, ~1050 lines down, whose
conclusion subsumes the leaf at every geometric point, differing only in carrying `hdim'`
where the leaf carries `htower`. Everything about it reads as a hoist plus a bridge.

It is **circular**: it is proven over `exists_frobTraceAct_of_mult_finiteBase`, which
calls `exists_frobLevelTrace_of_mult_finiteBase`, which calls
`…_of_levelScalar_…` → `…_of_coherentLevelScalar_…` → the leaf. Five hops, none of them
visible in either docstring — both describe their own cut and neither mentions the other.

**So the declaration-order check is not `grep -n` on line numbers; it is the CALL GRAPH.**
Before treating a below-you theorem as a hoist, grep the file for YOUR leaf's name and
follow every hit that is a call site, not prose:

    grep -n '<yourLeafName>' <file> | grep -v '`'      # call sites, then their callers

If a path comes back to the candidate, the ordering is not an accident of layout — it is
the dependency, and no relocation can fix it.

**Corollary about equivalence, which is what the two checks together established.** Once
the archimedean clause was known free, the leaf turned out to be *equivalent* to the
conclusion of a theorem 200 lines below it — one direction already in the file, the other
proved in six seconds — with the hypothesis that separates them (`hlev`) derivable inline
from machinery already present. A leaf that is provably interchangeable with a downstream
theorem is not thereby closable; but say so in the docstring, because it doubles the
shapes a prover may attack and it stops the next agent re-deriving the equivalence. And
name the inline step: `hlev` here was STEP 2 of a 200-line proof, invisible from outside
until it was pulled out as `exists_frobLevelScalar_of_levelTateFrame_finiteBase`.

