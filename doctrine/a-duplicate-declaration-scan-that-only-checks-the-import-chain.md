## A DUPLICATE-DECLARATION SCAN THAT ONLY CHECKS THE IMPORT *CHAIN* MISSES THE COMMONEST SHAPE

(2026-07-31, `flt-lean-307`, found by building merger release 29 and reading why
`X0.lean` would not start.)  `tools/merge/xdup.py` reported **zero** qualified
cross-file duplicates on a tree whose very next module failed with

    error: import Fermat.FLT.Mathlib.AlgebraicGeometry.CurveDivisorDegree failed,
    environment already contains 'AlgebraicGeometry.divDegree_eq_zero' from
    Fermat.FLT.Mathlib.AlgebraicGeometry.PrincipalDivisorDegree

The scan's pair test was `a in cone[b]` — it reported a pair only when one of the
two modules IMPORTS the other.  **Two files that do not import each other, while a
third imports both, are exactly what Lean rejects, and are exactly what the test
cannot see.**  That is also the commonest shape here, because it is what two
branches hoisting overlapping blocks into two NEW modules produce — neither new
module imports the other, and the old consumer imports both.

Fixed by computing, for each module, the set of modules that can SEE it (itself
plus everything importing it transitively) and reporting a pair whenever those
sets intersect.  Each pair is now tagged `ANCESTOR` or `SIBLING via <module>`,
and the witness is the module with the SMALLEST cone that sees both — picking the
alphabetically first names `Fermat.Basic` every time, which is true and useless.

**It went from 0 to 22 qualified pairs on the same tree**, in two clusters, and
both are live release blockers:

* `CurveDivisorDegree` ⟷ `PrincipalDivisorDegree`, 3 pairs
  (`divDegree_eq_zero`, `Scheme.ord_one`, `Scheme.ord_inv`), seen by `X0.lean`.
  `divDegree_eq_zero` is a `sorry` LEAF upstream and a PROVEN theorem downstream,
  with different statements (`hf : f ≠ 0` versus all `g`), so which copy survives
  is an author's decision and not a merge step;
* `HeckeQExpansion` ⟷ `HeckeAtkinLehner`, 19 pairs (`qCoeff`, `qCoeffL`,
  `heckeRep*`, `qParam_*`, …), seen by `Modularity.Interface`.  This is the
  collision the "TWO BRANCHES HOISTING OVERLAPPING BLOCKS" section above
  PREDICTED, arriving as forecast: a 19-declaration hoist and a 196-declaration
  hoist into two new modules, the smaller a strict subset of the larger.  The
  resolution that section prescribes — keep both modules, make the larger
  `public import` the smaller and delete its copies of the overlap — still applies.

The general rule, and it is the same one release 29's own commit message states
about its identifier class: **a scan that under-reports is worse than no scan,
because it certifies.**  Before quoting a clean run of any duplicate scan, check
that its notion of "can collide" is Lean's notion — which is *some single module
sees both*, never *one imports the other*.

