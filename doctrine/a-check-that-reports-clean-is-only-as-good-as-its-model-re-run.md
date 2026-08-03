## A CHECK THAT REPORTS CLEAN IS ONLY AS GOOD AS ITS MODEL — RE-RUN IT AFTER MERGING A FIX TO IT

(2026-07-31, release 31.) `tools/merge/xdup.py` reported **0 qualified duplicate
pairs** on `merger`'s tree. Nine branches later — none of which touched a single
Lean declaration involved — it reported **21**, and both clusters were HARD
`environment already contains …` import failures, i.e. they stop a module before
one line of it elaborates. Nothing about the tree had changed. What had changed
is that one of the nine branches (`flt-lean-307`) carried a two-line fix to
`xdup.py` itself.

The bug is worth knowing because the same modelling error is easy to make again:
the pair test was `a in cone[b]` — *does one of the two modules IMPORT the
other?* Lean's condition is strictly weaker. **A collision happens as soon as
SOME SINGLE module sees both**, whether or not either sees the other. Two sibling
modules under a common consumer collide, and no import-cone pair test can see it.

So the rule, and it generalises past this one script: **when a merge brings in a
change to a CHECKER, re-run that checker on the tree you have already certified
with the old one.** A checker is not payload — its diff is three lines and its
blast radius is every previous clean verdict. The natural reading ("tooling
change, no Lean impact, no need to re-verify") is exactly backwards.

Corollary for reading a previous release's handover: "check X was clean" is a
statement about X *as it stood then*. Release 30's handover truthfully reported
zero qualified duplicates and the tree had two release-blocking collisions in it.

The two found this way, both the "TWO BRANCHES HOISTING OVERLAPPING BLOCKS"
shape CLAUDE.md already predicts by name:

* `Modularity/HeckeAtkinLehner.lean` (196 declarations hoisted out of
  `Interface.lean`) against `Modularity/HeckeQExpansion.lean` (19, a strict
  SUBSET), with `Interface.lean` `public import`ing both — 19 pairs. Resolved
  as prescribed: keep both modules, larger imports smaller, delete the overlap
  from the larger. `tools/merge/dedup_cross.py` body-compares first, which is
  what makes this mechanical: 18 bodies were byte-identical and one
  (`qCoeff_heckeOp`) was the same STATEMENT with a different proof, which the
  tool correctly refused to delete and left for a decision.
* `Mathlib/AlgebraicGeometry/PrincipalDivisorDegree.lean` against
  `…/CurveDivisorDegree.lean` on `Scheme.ord_one`/`Scheme.ord_inv`, seen by
  `ModularCurve/X0.lean`, the only module importing both.

