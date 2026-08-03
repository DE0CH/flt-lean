## A LEAF HANDED A DATUM `∃`-STYLE MAY NEED THE PINNING HYPOTHESIS TOO — `‖λ‖ = 1` IS NOT `λ = λ(f)`

(Same task, caught by instantiating the residue before committing it.) The natural way to
hand an Atkin–Lehner pseudo-eigenvalue across a cut is `(lam : ℂ) (hlam : ‖lam‖ = 1)
(hrel : ∀ n, b n = lam * conj (a n))`. That determines `b` from `lam` — and **leaves `lam`
free**, so the residual leaf quantifies over every unit, not over the actual
pseudo-eigenvalue. At `lam := 1` the two-term head collapses to `|Im a₂|·x²`, which is
below the tail bound at five of the six Galois-orbit representatives of `S₂(Γ₁(25))`. The
leaf was FALSE, and it typechecked, and its glue compiled green.

**The repair is to keep the hypothesis that pins the datum** — here `hb`, which makes `b`
the expansion of the NAMED Fricke partner, so `hrel` at `n = 1` with `a₁ = 1` reads
`b 1 = lam` and `lam` is determined. Cost: one extra binder the caller already holds.

**The standing check, and it is cheap: after cutting, instantiate the residue's free data
at its most degenerate admissible value and evaluate.** `lam := 1`, `λ := −1`, the trivial
character, the zero form. A datum constrained only by a NORM, an ORDER or a DEGREE is
free in every other direction, and the clause that looks like it pins it (`hrel` here)
usually pins something else. Same family as the recorded
"AN EXISTENTIALLY-QUANTIFIED CONSTANT CARRIES NO ANALYSIS" and "AN INTERFACE PREDICATE CAN
BE UNDER-COMMITTED", with the free parameter arriving through a CUT rather than through a
definition.

Corollary worth keeping when you do it: **state in the docstring that the redundant
hypotheses are handed over deliberately.** `hlam`/`hrel` here are literally the conclusion
of the sibling leaf the caller has already applied; they cannot make the statement false,
only easier, and a reader who deletes them as redundant re-opens the hole.


