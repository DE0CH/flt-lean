---
name: flt-cost-triage-prices-wrong-object
description: A cost verdict "quantity X is forced, so choosing Y cannot help" is only as good as the claim that the cost lives on X — ask what the method's inner loop ranges over.
metadata:
  type: project
---

(2026-08-01, `flt-lean-325`, the two `p = 37` rows of Mazur's non-CM table in `X0.lean`.)

Three docstrings said **DO NOT DISPATCH A PLAIN COMPUTATION AT THIS ROW**, backed by a
triage: the Frobenius certificate `H ∣ X^(ℓ^m) − X` needs `≈ deg H` identities at degree
`≤ 2·deg H`, and `deg H = 666` is forced at every `ℓ`, so no prime helps.

`deg H = 666` really is forced. The table is **not built over `H`** — the method FACTORS `H`
and builds one table per irreducible factor, which is what the `p = 11` row the same triage
cites for comparison actually does (five degree-11 tables, not one degree-55 table). Cost is
cubic in the FACTOR degree, and that is exactly what `ℓ` controls: `222` at `ℓ = 397`, `37`
at `ℓ = 1259`. ~35× cheaper, plus `m = 37` prime kills three coprimality clauses.

**Why:** forcing `deg H` forces the identity COUNT and nothing else; the degree at which
`ring_nf` closes each identity is free and is what dominates. "The parameter is forced" and
"the cost is forced" are different claims.

**How to apply:** before believing any "X is forced, so Y cannot help", name what the
method's inner loop ranges over and check the cost really lives on X. If the triage cites a
WORKED sibling, check its formula actually describes that sibling — it took one look at the
generated file here. And when a leaf is priced at a wall, ask whether the wall is in the
STATEMENT or in a parameter the statement merely happens to have fixed; a parameter fixed by
an earlier agent's search is a choice, not a constraint. Related: [[flt-leaf-cost-estimates-are-hypotheses]],
[[flt-decomposition-verdict-cost-list-is-a-hypothesis]].
