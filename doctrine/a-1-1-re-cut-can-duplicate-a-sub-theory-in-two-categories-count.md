## A `1 → 1` RE-CUT CAN DUPLICATE A SUB-THEORY IN TWO CATEGORIES — count THEOREMS, not leaves
(2026-08-02, `flt-lean-276`, on `finrank_cuspForm_eq_of_isCurveGenus` in
`ModularCurve/X0.lean`.)  This file's standing tie-breaker is *fewer OPEN leaves
after*, and a re-cut that is leaf-neutral is judged by *what is LEFT in the leaf*.
Both rules are right and both are blind to the failure below, which is the one
that decides most re-cuts of a bridge.
A bridge `A = C` is routinely split as `A = B` (analytic half) plus `B = C`
(algebraic half).  The tempting re-cut is to collapse the split and make `A = C`
itself the leaf: two leaves become one, and the survivor mentions fewer objects.
**Ask instead which THEOREMS each arrangement obliges somebody to prove.**  Here:
* as split, the algebraic half is Riemann–Hurwitz for `X_0(N) → X(1)` **on the
  scheme**, and the analytic half is uniformisation plus Hodge plus the
  comparison — Riemann–Hurwitz appears ONCE;
* collapsed, the survivor `dim_ℂ S₂(Γ₀(N)) = x0Genus N` still needs the genus of
  the modular curve, i.e. Riemann–Hurwitz **in the analytic category** — and a
  SIBLING leaf in the same file
  (`one_le_isCurveGenus_curveBaseChange_of_one_le_x0Genus`) still needs it in the
  algebraic one.  The same theorem, twice, in two categories, for a leaf count
  that went down by one.
So the collapse buys a better-looking frontier and costs a whole chapter.  **The
check is to list the classical theorems each arrangement needs and look for one
that appears twice under two names** — "Riemann–Hurwitz for a covering of Riemann
surfaces" and "Riemann–Hurwitz for a finite morphism of curves" share no
identifier and will never be flagged by any duplicate scan.  A split that makes
two halves meet through an EXPLICIT INTEGER (here `x0Genus N`) is exactly the
arrangement that lets a theorem be proved once and consumed on both sides; do not
undo one without checking what it was buying.
Corollary about rival cuts, since this one was a day old: a decomposition made
yesterday, with its rationale written on the parent, is evidence.  Re-deriving the
arithmetic and getting a better NUMBER is not a reason to overturn it — get a
better THEOREM COUNT or leave it alone, and either way write the audit down.
### Riders, both measured the same run
* **A `.lake` seeded before a large fast-forward reports `Unknown identifier` for
  SOME declarations of a file and resolves OTHERS.**  This worktree arrived 1521
  commits behind `main`; after the ff, a two-line scratch `#check`ing four names
  from `X0.lean` resolved one and reported the other three unknown — including
  `AlgebraicGeometry.IsCurveGenus`, whose module had NO olean on disk at all.  The
  partial success is the tell, and it reads as a namespace problem rather than a
  build problem.  **Check olean mtimes against `~/.flt-release-lake/build` before
  believing any name is missing**; if `git diff --stat $(cat ~/.flt-release-lake/sha)
  HEAD -- Fermat/` is empty, `rsync -a --delete` the snapshot in and re-probe.  It
  took 14 seconds here and every name then resolved.
* **A route's "this is a real step, called out so nobody discovers it halfway
  through" is exactly the clause to re-grep.**  `one_le_isCurveGenus_curveBaseChange_of_nontrivial_cuspForm`
  flagged `FiniteDimensional ℂ (CuspForm (Gamma0GL N) 2)` that way;
  `Fermat.cuspForm_finiteDimensional` has been PROVEN since 2026-07-24 in
  `ModularCurve/WeightTwoEigenform.lean`, which `X0.lean` `public import`s, and is
  one `haveI` away.  Two other docstrings in the same tree already record the same
  miss for other consumers.  A warning written to save the next agent time is
  written before anyone tried, and ages exactly like an absence claim.
