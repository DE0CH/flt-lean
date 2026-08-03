## "That theorem HANDS BACK X" is a claim about its CONCLUSION, not about its proof

(2026-07-31.) `exists_span_three_eq_maximalIdeal_and_finrank_eq_of_residueField`'s
docstring said, twice and in bold, that the only thing its proof was missing was one
`public import`, and that `exists_unramified_extension_of_residueField` "delivers
`𝔪_S = 𝔪_R·S` verbatim". The import claim was exactly right and saved real time. The
delivery claim was **false**: that theorem's proof does establish `𝔪_S = 𝔪_R·S`
internally (it is a named `have` in its body, `hmaxS`) and its conclusion does **not**
export it. So the consumer, having added the promised import, still could not close the
leaf.

The recovery was cheap once the shape was clear — `S` is free of rank `n` over `R` and
its residue field already has degree `n`, so `n = e·f` forces `e = 1`, which is a
general lemma (`maximalIdeal_eq_map_of_finrank_residueField_eq`, proved from mathlib's
`IsLocalRing.finrank_quotient_map` plus rank–nullity, ~30 lines) — but it is work
nobody had budgeted, and the docstring said it was not needed.

So: **when a docstring tells you what an upstream theorem gives you, read that
theorem's STATEMENT before believing it.** A `have` inside a proof is invisible to
every consumer. And the repair when the fact really is only internal is a choice with
different costs, worth making deliberately:
* *export it* — add the clause to the upstream conclusion and fix its consumers. Two
  lines, but it rebuilds everything downstream of a widely-imported module;
* *re-derive it downstream* — a self-contained lemma in the file you already own. More
  Lean, zero extra rebuild, no merge conflict with other agents.
Prefer the second when the upstream module has consumers outside your cone.

