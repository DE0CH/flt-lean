## AN IMPORT CYCLE IS A WHOLE-PROJECT OUTAGE, AND THE BRANCH THAT CAUSES IT CHECKS THE DIRECT EDGE ONLY

(2026-07-31, release 28, and it cost the first two build rounds.) `flt-lean-389`
closed a leaf in `ModularCurve/HyperellipticJacobian.lean` by adding
`import Fermat.FLT.ModularCurve.X0`, under a comment that said in as many words
*"there is no cycle, since `X0.lean` does not mention"* this file.  The direct edge
really is absent.  The cycle is two hops long:

    X0  -->  FreyCurve/IsogenySignature  -->  HyperellipticJacobian  -->  X0

and both of the other edges are years-old and pre-existing.  The result is not a
red module: `lake build` fails on the ROOT target with `build cycle detected` and
**nothing in the project builds at all**, which reads like a catastrophically
broken tree rather than like one bad import line.

Three things follow, and the third is the one worth institutionalising.

* **Any import you ADD must be checked against the transitive closure, not the
  direct edge.**  Ten lines of Python, and it must ASSERT that every visited
  module's file exists — a swallowed `FileNotFoundError` truncates the walk and
  manufactures exactly the "incomparable, no cycle" answer you were hoping for.
* **A cycle-breaking hoist should go into a NEW MODULE, not into the destination
  the offending comment names.**  `flt-lean-389`'s note prescribed
  `Modularity/AbelianSchemeIsogeny.lean`, which is right architecturally and
  expensive in practice: `X0.lean` `public import`s it, so adding one import there
  rebuilds the largest cone in the tree.  A new module rebuilds only its own
  consumers, and it cannot conflict with anything.  Move the declarations
  VERBATIM with their docstrings; the only edit should be spelling out any
  `abbrev` (here `SpecQ`) that is declared in the module you are moving OUT of.
  An `abbrev` is reducible, so every existing call site elaborates unchanged and
  no delegation is needed.
* **The merge worker must run a cycle check as a standing release check**, beside
  the comment and scope scans.  It costs a second and its failure mode is total.

