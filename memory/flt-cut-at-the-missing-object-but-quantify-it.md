---
name: flt-cut-at-the-missing-object-but-quantify-it
description: When a leaf's docstring names a MISSING OBJECT, cut there — but the cut is only a reduction if ONE object serves every instance; the per-instance form is usually equivalent to the conclusion
metadata:
  type: feedback
---

A leaf whose docstring says "what is genuinely missing is X" is telling you where
to cut. But **the per-instance form of X is usually logically equivalent to the
conclusion, and committing it is a restatement dodge that looks like progress.**

The measured case (2026-07-31, both Shimura algebraicity leaves,
`X0.lean`/`X1.lean`). The docstrings named the integral homology
`H₁(X, ℤ)` as a Hecke module. Two ways to ask for it:

* *per `n`* — "for each `n` there is an integer matrix with `a n` as an
  eigenvalue". This is **equivalent** to `∀ n, IsIntegral ℤ (a n)`: given
  integrality, take the companion matrix of the minimal polynomial. Zero
  mathematics moved.
* *simultaneously* — ONE lattice, ONE family `T : ℕ → Matrix (Fin r) (Fin r) ℤ`,
  ONE nonzero period vector that is a left eigenvector of every `T n` with
  eigenvalue `a n`. Strictly stronger than the conclusion, and exactly what a
  single `H₁` supplies. The residue becomes a statement about a CURVE instead of
  about an algebraic number.

**The test, before committing any cut: instantiate the proposed hypothesis one
instance at a time and try to build it from the conclusion you were trying to
prove.** If you can, the quantifier is in the wrong place, not the statement.

Two things that made this cut land rather than stall:

* **The downstream argument must become real code, not prose.** The whole of
  "so `a n` is a root of a monic integer characteristic polynomial" is ~15 lines
  over `Matrix.charpoly_monic` / `charpoly_map` / `eval_charpoly` /
  `exists_mulVec_eq_zero_iff`, now `Fermat/FLT/ModularCurve/HeckeLattice.lean`.
  A cut whose downstream half stays in a docstring has not been made.
* **Pick the convention the future producer will actually hold.** The period map
  gives `∑ i, φ(b i) * (toMatrix b b Tₙ) i j = aₙ * φ(b j)`, i.e. the ROW form
  `period ᵥ* T n = a n • period` — no transpose. Writing the structure with `*ᵥ`
  would have forced every future construction to transpose the matrix of the
  Hecke operator, which is where sign errors live.

Corollary on free-floating: the abstract-lattice → matrix bridge
(`ofPeriodMap`, from `[Module.Free ℤ L] [Module.Finite ℤ L]` plus a period
functional) is what the future prover needs, but it would be **free-floating**,
since its only consumer is a proof of the still-sorried leaf. Verify it, then
park it VERBATIM in the module docstring with a note that it compiled — the same
idiom `X1.lean` uses for its mechanized level-`0` falsity witness. See
[[flt-transport-the-twins-recut]] for why both level shapes must be cut by one
owner, and [[flt-cleaner-statement-harder-proof]] for the sibling question of
where to cut at all.
