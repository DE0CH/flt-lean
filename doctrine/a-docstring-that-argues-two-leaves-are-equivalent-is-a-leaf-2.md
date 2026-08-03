## A DOCSTRING THAT ARGUES TWO LEAVES ARE EQUIVALENT IS A LEAF-MERGE WAITING TO BE PERFORMED
(2026-07-31, done twice the same day — `X1.lean`'s `Γ₁` pair, then `X0.lean`'s `Γ₀` pair.)
Both files carried the same cut: one Katz–Mazur citation split into
`exists_<X>ModuliScheme` (`∃ R, …`) and `isAffine_of_<X>ModuliScheme` (`∀ R, IsAffine R.M`).
The `∀`-shaped half is the junk-witness shape this development is rightly afraid of, so each
docstring answered the worry in prose:
> `universal` is a **fine** moduli property, so any two inhabitants are related by a unique
> isomorphism (apply each one's `universal` to the other's universal family, and then to its own
> to see that the two composites are the identity).  `IsAffine` is invariant under isomorphism.
**That paragraph is not a caveat. It is a complete proof that one of the two leaves is free** —
it says `∃ R, IsAffine R.M` implies `∀ R, IsAffine R.M`, so merging the halves into the single
existential costs one thirty-line lemma and closes a leaf. Both files had it written out, in
full, for four days, under a heading that reads like a disclaimer.
Both docstrings also contained the explicit escape hatch — "if a prover would rather not pay it,
the honest weakening is to prove `∃ R, IsAffine R.M` instead … but then the two citation halves
fuse back together, which is the thing this cut exists to prevent." **The warning had the sign
backwards.** The cut was made so that no leaf carried both a citation and a formalisation; what
it actually produced was two leaves carrying ONE citation between them, because (8.1.1)'s
affineness clause is a remark on the construction of (4.7.2) and nobody proves it separately.
Fusing is a strict improvement whenever the two halves are not separately provable.
So, as a standing sweep: **grep docstrings for prose that relates two leaves**, not just for
`sorry`. The phrases that actually found these are `are the same statement`, `up to unique
isomorphism`, `invariant under isomorphism`, `junk-witness`, `would rather not pay`. Each hit is
a hypothesis that a leaf is free; it costs one read to check.
**The mechanical obstacle, and the cheap way through it.** The merge needs a rigidity lemma, and
a rigidity lemma needs the file's `IsBaseChangeOf.refl` / `.comp` calculus — which in `X0.lean`
sat 500 lines BELOW both leaves and below their consumer. Do not relocate the leaves (their
docstrings are long and their consumers are elsewhere): **hoist the calculus**. A line-range move
is safe when (a) it is namespace-balanced — every `namespace`/`end`/`section` pair in the moved
range is inside it — and (b) nothing in the skipped span uses the moved names. Both are one
`grep` each, and the move is then verbatim: `git diff` shows equal insertions and deletions.
**Corollary for the accounting.** `X0.lean` went 130 → 129 direct sorries while GAINING a
declaration. Merging leaves is one of the few moves that lowers the frontier without proving any
mathematics, so it does not show up in any "what got proven" report — say so explicitly, or the
delta looks unexplained.
