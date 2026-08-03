## A THEOREM THAT ESTABLISHES YOUR PIN INTERNALLY AND DOES NOT EXPORT IT BLOCKS THE **CUT**, NOT THE PROOF — AND A NON-PUBLIC IMPORT CAN MAKE THE REPAIR UNPERFORMABLE WHERE YOU NEED IT
(2026-08-02, `flt-lean-78`, `exists_geomFibreAddEquiv_hom_of_isWeierstrassModel`
in `FreyCurve/MazurTorsion.lean`.)  CLAUDE.md already records that *"that theorem
hands back X" is a claim about its CONCLUSION, not about its proof*, and prices
the repair as "export it, or re-derive it downstream".  There is a third
consequence that neither option covers, and it is the one that decides whether a
leaf can be decomposed at all.
That leaf bundles TWO things: build an identification `ε` of `E(ℚ̄)` with the
geometric fibre, and realise every Galois-equivariant isogeny as a scheme
morphism against it.  **The first half turned out to be already PROVEN** —
`exists_geomFibreAddEquiv_of_weierstrassModel` (`ModularCurve/EllipticScheme.lean`)
takes exactly the leaf's `IsWeierstrassModel` hypothesis and returns the
equivariant `≃+`; adding a non-public `import` and writing
`exists_geomFibreAddEquiv_of_weierstrassModel E d.ab hmod` closes both
equivariance clauses, verified green.  So the leaf was over-priced by a whole
construction, and had been for days.
**The split still does not happen, and the reason is worth naming.**  To cut
"produce `ε`" from "realise `χ` against `ε`", the residual must receive `ε`
PINNED.  Quantifying `ε` universally is not a safe restatement — at `E' = E`,
`χ = id` the `∀ ε ε'` form asserts every Galois-equivariant additive
automorphism of `E(ℚ̄)` is induced by a scheme endomorphism, i.e. lies in
`End_ℚ(E) = ℤ`, whereas Tate/Faltings only makes it a `ℤ̂ˣ`-scalar on torsion.
Faltings-hard at best, possibly FALSE; do not state it.  And the proven theorem
**establishes the pin internally and exports only the equivariance** — its proof
takes the chart `ι`, gets `ι₀ ≫ u = ι` from `exists_isIso_of_affineChart`, and
sets `e := e₀.trans (post u)`.
**THE THIRD CONSEQUENCE: the pin may be UNSTATEABLE in the file that needs it.**
The clause would have to mention the chart and the functor of points, and those
live in a module imported NON-PUBLICLY on purpose (here to keep the reserved
token `over` from escaping).  A non-public import reaches proof BODIES, so the
free half lands fine; it does not reach STATEMENTS, so the pinning hypothesis
cannot be written down locally at all — and making the import public is
known-bad.  So "re-derive it downstream", the cheap branch of the standing rule,
is simply unavailable, and the only repair is the one-clause strengthening in
the upstream module.
**Checks, in the order that costs least.**  Before pricing any leaf that both
CONSTRUCTS an identification and USES it:
* grep the tree for the CONSTRUCTION half's conclusion — in this development it
  is routinely already proven, in a mathlib-facing or chart-level module the
  consumer does not import ([[flt-inventory-audits-understate-what-exists]]);
* if it is, check whether it EXPORTS the property your residual would need to
  pin the object, or merely establishes it.  Read the conclusion, not the proof;
* if it does not, check whether the pinning clause is even UTTERABLE in your
  file — `grep -n 'import' <your module>` and ask whether the names the clause
  needs come through publicly.  If they do not, the cut belongs upstream and
  your run's deliverable is the one-clause strengthening task, not the cut.
Corollary for whoever writes such a producer: **when a theorem's proof pins its
output, export the pin.**  The cost is one conjunct at the moment of writing and
it is what decides, months later, whether a downstream leaf can be decomposed by
anyone at all.  A producer that returns an object with only the properties its
first consumer happened to need is the commonest way this tree manufactures an
undecomposable leaf.
