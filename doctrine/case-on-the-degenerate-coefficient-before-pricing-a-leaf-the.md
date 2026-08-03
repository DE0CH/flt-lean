## CASE ON THE DEGENERATE COEFFICIENT BEFORE PRICING A LEAF — the free half is usually most of it

(2026-07-31, `flt-lean-317`, `DifferentialCharacter.lean`'s last leaf,
`exists_wronskianPoly_scalar_charTwo_coprime`.) That leaf carried three screens of
careful, correct route analysis and read as uniformly hard: a valuation count on `ℙ¹`
that "closes EXCEPT where one of the two bounds is tight", with the tight case needing a
derivative identity nobody had written. Its conclusion is
`P·S = c·T·B` with `T := a₁′A + a₃′B` — **a LINEAR FORM in the structure constants of the
target curve.** One `by_cases W'.a₁ = 0` split it into

* `a₁′ ≠ 0`: `T = a₁′·(A − r′B)`, `r′ = a₃′/a₁′` — i.e. `T` is, up to a unit, a
  **companion** of `B` for which the file's existing machinery already applies verbatim
  (`wronskianPoly_sub`: `(A − r′B, B)` has the SAME Wronskian as `(A, B)`). ~120 lines,
  compiled first try, and `hone`/`hcurve` — the two big curve hypotheses — are **never
  used**;
* `a₁′ = 0`: `T` collapses to `a₃′·B`, the requirement DOUBLES to `2·ord_b B ≤ ord_b P`,
  and that is the whole of the residue.

**So: when a leaf's conclusion contains a linear form in constants that may vanish, split
on the leading coefficient FIRST, before costing anything.** The nondegenerate branch is
where the form is a companion of an object the file already handles, so it is usually
free; the degenerate branch is where the form loses a variable and the count doubles, and
that is the only place the missing mathematics lives. Costing the leaf as one object
prices the easy 90% at the hard 10%'s rate — which is exactly what had happened here, three
times, by three careful authors.

Two riders, both measured.

* **The parity lever is a one-line lemma and it is what the count was really waiting for.**
  In characteristic `2`, `(w²)′ = 2ww′ = 0`, so an EVEN power dividing `p` divides `p′` too
  (`charTwo_even_pow_dvd_derivative`, 6 lines). That upgrades
  `ord_b G ≤ ord_b(A′B − AB′) + 1` — the crude bound, which is short by exactly one — to
  the sharp `ord_b G ≤ ord_b(A′B − AB′)` at every place where a parity hypothesis is
  available. Whenever a count is short by one and a parity is in the hypotheses, this is
  the shape of the fix; the general form in characteristic `p` is `p ∣ k`.
* **The degree half can be free while the divisibility half is hard, and nobody checks.**
  The docstring priced degrees as "the same three cases read at `∞`". In fact
  `natDegree_wronskianPoly_succ_le` on the companion pair gives `deg P + 1 ≤ deg T + deg B`
  outright, and `deg S ≤ 1` absorbs the `+1` — no cases at all. Re-derive a "same as
  above" clause before budgeting for it.

Accounting note, in the shape CLAUDE.md's RECUT rule asks for: **the direct-sorry count did
not move, 1 → 1.** What changed is that the surviving leaf carries one extra hypothesis
(`W'.a₁ = 0`), mentions no `hparT`, and has a written-out Artin–Schreier route with every
valuation computed. Judge it by that, not by the delta.

