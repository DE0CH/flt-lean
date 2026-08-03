## AN AUDIT MARKED "RE-VERIFIED <yesterday>" CAN BE STALE ABOUT ITS OWN FILE

(2026-07-31.) `exists_nonconstant_toAbelianScheme_of_one_le_x0Genus`'s docstring in
`ModularCurve/X0.lean` carried a paragraph headed **RE-VERIFIED 2026-07-30**, whose
operative claim was that the modular route's first step "is still unstated — the only
dimension formula anywhere in the tree is `finrank_cuspForm_of_x0HeckeCharpolyTable`,
table-driven and declared below this leaf". The uniform bridge it wanted —
`finrank_cuspForm_eq_x0Genus`, `dim_ℂ S₂(Γ₀(N)) = x0Genus N` for **every** `N ≥ 1` —
had been stated **in the same file, on the same day**, three thousand lines further
down. The audit really was re-verified, against `85ee56a7`; the sibling leaf landed in
a later release a few hours after.

So the release window does not only invalidate OWNERSHIP records. It invalidates the
**absence claims inside docstrings**, and those are the more dangerous half, because a
docstring absence claim is read as a settled fact about the tree and carries a date
that makes it look fresh. **"RE-VERIFIED <date>" is evidence about a commit, not about
`main`** — and the same file is exactly where a rival leaf is most likely to appear,
since that is where the neighbouring work is being dispatched.

The check costs one `grep`: before believing any docstring clause of the form *"no such
theorem exists"*, *"the only one is X"*, or *"it is not in scope here"*, re-grep the
name and re-read the line numbers. Then **correct the docstring in place, next to the
stale claim rather than over it** — the reasoning that produced the claim is usually
still worth reading, and a leaf's audit history is how the next prover knows which axes
are exhausted.

Corollary, from the same leaf: when the correction lands, re-do the ARITHMETIC the stale
claim supported. Here the audit's conclusion — "a decomposition along the modular axis
produces two theory builds where there is now one leaf, which is why it has not been
taken" — was the whole reason the axis was declined, and with the dimension bridge
already stated it is off by one build.

