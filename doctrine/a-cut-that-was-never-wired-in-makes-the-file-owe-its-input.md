## A CUT THAT WAS NEVER WIRED IN MAKES THE FILE OWE ITS INPUT TWICE — and both copies read as ordinary open leaves

(2026-08-01, `flt-lean-209`, `FreyCurve/MazurTorsion.lean`.)  On 2026-07-31 a branch
decomposed `jInvariant_eq_of_end_closure_eq_top` — the class-number-one input — into a
new predicate `IsCMJInvariantOfRel` plus two leaves, and documented the decomposition in
three docstrings.  **It never re-pointed the parent.**  A day later the parent was still
an independent `sorry` and the three new declarations were consumed by NOTHING anywhere
in the tree.  So the file owed complex multiplication *twice*, and the frontier counted
three leaves where the cut intended two.

This is the free-floating/orphan class arriving from a new direction, and it is the worst
one to see, because **the cut and the parent are in the same file, by the same author, and
both docstrings assert the relationship.** The parent's said "the ONLY REMAINING
COMPLEX-MULTIPLICATION INPUT of that cut"; the children's said "this is the only statement
in the cut of `jInvariant_eq_of_end_closure_eq_top` that needs the ring class field".  Both
sentences describe a dependency that the CODE does not have.  Every instrument agrees the
three leaves are ordinary open work: they emit honest `declaration uses 'sorry'` warnings,
a source scan finds them, `own.py` correctly reports them unowned.

**So: a docstring saying "X was cut out of Y" is a claim about Y's PROOF BODY.  Grep it.**
This is the sibling of the already-recorded *"a proven parent whose docstring names a
different leaf from its proof body"*: there the body named the wrong leaf, here the body
named none — the parent is still `sorry`, so it has no dependency edges at all, and a
sorried body is exactly what makes the orphan invisible.

    grep -rn '<the cut predicate>' --include=*.lean Fermat/     # hits only in its own region ⇒ never wired

**The repair is to WRITE THE ASSEMBLY, and it is usually short**, because the cut was
designed to make it short — here fifteen lines, and the one cast (`Int.cast_natCast`) the
parent's own docstring had predicted the consumer would need.  Doing it took the cluster
from three open leaves to two and moved the whole cluster into the root cone.  **Prefer it
to working the leaf you were dispatched at**: proving a leaf nothing consumes moves the
count and not the project, and a prover sent at a dead leaf has no way to tell.

Two riders from the same run:

* **Check the cut's own economics before adopting it.**  Here the two children were a
  UNIFORM statement (all CM `j`-invariants of one order share a minimal polynomial) plus a
  level-specific one; the parent follows from them by pure `minpoly` bookkeeping.  That is
  a good cut and wiring it in was the right call.  A cut whose children do not actually
  imply the parent is a different finding, and then the honest output is to say so and
  delete one side rather than to build glue that cannot exist.
* **When the assembly needs a lemma declared BELOW you, state the leaf so it does not.**
  The natural residual here — "there is a CM elliptic curve over `ℚ`" — would have given
  the `Subring.closure {φ} = ⊤` clause for free from a PROVEN lemma 2700 lines further
  down, which Lean's order forbids citing.  Hoisting it was rejected because it lives in a
  *different namespace* (`MazurIsogenyPrimeJ` against `MazurIsogenyPrimeJ.FixedLocusOfAdditive`),
  so the move would have renamed it and broken its four consumers.  The leaf was stated in
  the weaker `∃ c : ℚ` form instead, with the four-line bridge and the exact hoist a
  successor should make written into its docstring — which is the cheap side of
  CLAUDE.md's standing advice, and the namespace check is the part that is easy to skip.

