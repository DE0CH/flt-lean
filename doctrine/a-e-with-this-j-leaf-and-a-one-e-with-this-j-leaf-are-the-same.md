## A `∀ E WITH THIS j` LEAF AND A `∃ ONE E WITH THIS j` LEAF ARE THE SAME LEAF — and the bridge is a CERTIFICATE, not a theorem
(2026-08-02, `flt-lean-200`, `exists_cmSqrtEnd_of_mem_isolatedCMJInvariants` in
`ModularCurve/X0.lean`.)
A large family of leaves here has the shape *"for EVERY curve `E/ℚ` whose `j` is
`<tabulated value>`, `End(E_ℚ̄)` contains `…`"*.  That universal quantifier is free:
over an algebraically closed field the curves with a given `j` are all isomorphic, so
the leaf is EQUIVALENT to the same statement at ONE curve — which is the form the
mathematics (here Deuring) actually produces.  Recutting to the existential form is a
`1 → 1` trade that costs nothing and hands the residual to a prover in the shape their
citation delivers.
**Both halves of the bridge were already in this tree, already `public import`ed by the
target's own module, and had never been connected:**
* `WeierstrassCurve.Affine.Point.equivVariableChange`
  (`Fermat/FLT/Mathlib/AlgebraicGeometry/EllipticCurve/Affine/Point.lean`) — the additive
  isomorphism `(C • W).Point ≃+ W.Point` induced by a change of variables, PROVEN,
  including the additivity, which is the part that looks expensive;
* `WeierstrassCurve.exists_variableChange_of_j_eq`
  (`Mathlib/AlgebraicGeometry/EllipticCurve/IsomOfJ.lean`) — equal `j` over a SEPARABLY
  closed field produces the change of variables.
**What was missing is the one thing nobody looks for: a CERTIFICATE.**  `IsIsogeny`
carries `IsRationalMap`, which is *defined* as an explicit existential over five
polynomials `(A, B, C, D, E)`.  For a change of variables the coordinates are the affine
substitution `x ↦ u²x + r`, `y ↦ u³y + u²sx + t`, so the certificate is
`(u²X + r, 1, u³, u²sX + t, 1)` — both side conditions are `one_ne_zero`, no division
occurs, and the whole transport is `IsRationalMap.comp` twice.  Roughly 150 lines,
first-try green.
**So the standing check, before accepting a universal-over-an-isomorphism-class leaf as
the residual: does the tree have the point-level transport, and is the predicate you must
move defined by an explicit certificate?**  If it is, price the transport by WRITING the
certificate for your structural map, not by asking whether a transport theorem exists.
Predicates defined by `∃ witnesses, …` are cheap to move along maps that have a normal
form; predicates defined by a universal property are not.  The two read identically in a
Two riders, both of which decided this run:
* **the leaf's own "WHAT PROVING IT NEEDS" list was entirely correct and entirely beside
  the point.**  It named the uniformisation, the class polynomial and the
  lattice-endomorphism passage; none of that changed, because the recut is about the
  SHAPE of the statement and not its content.  A cost list is about the mathematics; it
  cannot tell you that the quantifier is free.  Read the quantifiers separately from the
  citation;
* **state the residual over the ALGEBRAIC CLOSURE, not over `ℚ`.**  Dropping the rational
  model makes the leaf strictly weaker for free (the parent's conclusion only mentions
  `(E⁄ℚ̄).Point`), and the `ℚ` form is recoverable from it by the same transport plus
  `EllipticCurve.ofJ`.  The one reason to prefer the `ℚ` form is if a DOWNSTREAM twin
  needs a rational curve — here `exists_cmEndomorphism_classNumberOne` in
  `FreyCurve/MazurTorsion.lean` does — and that is a decision to record rather than to
  make silently.
Accounting, in the shape the RECUT rule asks for: **the direct-sorry count did not move,
`1 → 1`, and no complex multiplication was proven.**  The receipt is one line and belongs
in the commit: `git diff HEAD~1 HEAD -- <file> | grep -E '^[+-] *sorry *$'` must show
exactly one `+  sorry` and one `-  sorry`.
