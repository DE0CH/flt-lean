## WEAKEN THE LEAF TO WHAT THE ROUTE ACTUALLY PRODUCES — an `=` that polarises out of a `≤` is not a leaf
(2026-07-31, `flt-lean-314`, tenth pass on `EllipticCurve/IsogenyTrace.lean`.) A leaf
whose conclusion is a numerical IDENTITY is worth re-reading with one question: **does
the route named in its own docstring produce the identity, or does it produce an
inequality that somebody then has to sharpen?** Those are very different obligations,
and the sharpening step is routinely the entire difficulty.
`End.isXNormalForm_natDegree_parallelogram` asked for
`max(deg A₁, deg B₁) + max(deg A₂, deg B₂) = 2 max(deg A, deg B) + 2 max(deg C, deg D)`.
Its route counts the roots of a polynomial. **A root count is `#roots ≤ natDegree` by
nature**; turning it into `=` needs the counted polynomial to be SQUAREFREE, and the
file's own section header names that separability argument as "where the geometry
actually enters". The identity, however, is FORCED BY ITS OWN INEQUALITY: if
`deg(φ+ψ) + deg(φ−ψ) ≤ 2 deg φ + 2 deg ψ` for every pair, instantiate at the pair
`(φ+ψ, φ−ψ)` — whose sum is `[2]φ` and whose difference is `[2]ψ` — and `deg [2] = 4`
returns the reverse inequality. Three lines of ring theory, and the separability step is
deleted from the whole file.
The pattern is general, and worth checking on any leaf of this shape:
* **A quadratic-form / parallelogram identity polarises.** `≤` for all pairs is `=` for
  all pairs whenever the form is multiplicative against `[2]`. Same for the reverse
  direction: `≥` alone would do just as well.
* **A count, a rank, a dimension, a degree, a cardinality: ask which side the route
  gives you.** Fibre counts, root counts and codimension bounds all come out one-sided;
  the other side usually needs a separability, a flatness, or a genericity input that is
  a whole development.
* **The concavity version is the same move one level down.** Here the unit-shift
  instance `deg(χ+1) + deg(χ−1) ≤ 2 deg χ + 2` — ONE endomorphism, no pairing, no
  torsion module — already gives everything: applied at `χ + [k]` it says the second
  difference of `f k := deg(χ + [k])` is at most `2`, i.e. `f k − k²` is CONCAVE on `ℤ`,
  hence below its chord at `0`; the linear term is odd and cancels in `f m + f (−m)`;
  and multiplying by `φ̂` converts the pair `(φ, ψ)` into `(φ̂ψ, [deg φ])`. So the file's
  single remaining geometric input is one inequality about one endomorphism.
**Weakening a CONCLUSION is the one restatement whose earlier audit transfers**, and you
should say so explicitly rather than re-run it: every counterexample to the weaker form
is a counterexample to the stronger one, so an audit certifying the `=` form true
certifies the `≤` form true. But **re-check which hypotheses are still load-bearing** —
weakening the conclusion can make some of them removable and leaves others fatal, and
telling them apart is the actual work. Here `hφ ≠ 0` and `hψ ≠ 0` became harmless (the
adversarial pair `(X, 1)` gives a TRUE inequality) while `φ + ψ ≠ 0` and `φ − ψ ≠ 0`
stayed fatal (their certificate is vacuous, so `(X ^ 100, 1)` is admissible and the left
side is unbounded). Keep all four anyway when the consumer discharges them: a hypothesis
that cannot make a leaf false costs a prover nothing.
Accounting note, since the count does not move: one leaf in, one leaf out. What changed
is that the surviving statement is strictly weaker and its route no longer needs a
development that was never going to be written. **Judge this kind of pass by what is
LEFT in the leaf**, not by the delta — the tie-breaker "fewer OPEN leaves after" is for
choosing between rival cuts, not a reason to skip a weakening that is count-neutral.
