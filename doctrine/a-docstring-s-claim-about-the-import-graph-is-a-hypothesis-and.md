## A DOCSTRING'S CLAIM ABOUT THE IMPORT GRAPH IS A HYPOTHESIS, AND A FALSE ONE PICKS THE EXPENSIVE PLAN

(2026-07-31.) This file already treats a stale `(sorry leaf)` label as a phantom-work source.
The same failure at MODULE scale is worse, because it does not produce a wasted dispatch — it
produces a wasted *architecture*, and the agent that follows it never learns the plan was
avoidable.

`ProjectiveModelOverField.lean`'s header stated, twice, that "`EllipticScheme.lean` is
DOWNSTREAM of `MoretBailly.lean` and so cannot be imported there". Both closures were walked
at `7080929d`, with no module missing from either walk: `EllipticScheme` reaches 56 `Fermat.*`
modules and does not contain `MoretBailly`; `MoretBailly` reaches 170 and does not contain
`EllipticScheme`. **They are INCOMPARABLE.** So the import is available in either direction —
`MoretBailly` importing `EllipticScheme` adds 7 modules and no cycle.

What the false claim was buying: `exists_projGroupLawOverField_geomFibreAddEquiv` wants the ℚ
group-law development at a general base, and its docstring accordingly plans a REWRITE of an
11 832-line chart interface inside a 51 000-line module — ~20 minutes of elaboration per
iteration. The reachable plan is to generalise `ProjCoords`/`exists_projAdd` IN PLACE in
`EllipticScheme.lean`, recover ℚ as `(F := ℚ)`, and import. Nobody had checked, because the
header said not to.

**So before planning around "module A cannot see module B", walk the closures.** It is ten
lines and seconds of runtime:

    def imports(m):  # m.replace('.','/') + '.lean', regex ^(public )?import (Fermat[\w.]*)$
    def closure(m):  # BFS; ASSERT every visited module's file EXISTS — a silent
                     # FileNotFoundError truncates the walk and manufactures "incomparable"

The assertion matters more than the BFS: a swallowed missing file is exactly how this check
produces the answer you were hoping for.

Corollary, and the reason to fix the docstring rather than just route around it: an import-graph
claim is *cheap to verify and expensive to believe*, so it should never be carried as prose
without a stamp. Write the commit it was measured at, the way frontier counts are stamped.

