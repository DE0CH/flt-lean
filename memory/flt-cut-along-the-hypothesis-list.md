---
name: flt-cut-along-the-hypothesis-list
description: "When a leaf is atomic on every recorded conclusion-axis, look for two hypotheses that no single proof step spends together — that pair is the seam."
metadata: 
  node_type: memory
  type: project
  originSessionId: 9a12e20e-ba54-43ef-a875-78494056bcf4
  modified: 2026-08-01T17:35:35.515Z
---

(2026-08-01, `flt-lean-28`, `finrank_mulByElt_of_relativeDimension` in
`Modularity/TateModule.lean`.) Every cut-finding heuristic in CLAUDE.md looks at the
CONCLUSION — split a conjunction, peel a degenerate case, pin a witness, restate an
existential. A mature leaf has usually had all of those tried and recorded as refuted.
There is one more place to look and it costs one read: **the BINDER LIST.** For each
pair of hypotheses, ask whether any single step of the classical proof spends both. A
pair that is never spent together is a seam, and both residues are then stated in
vocabulary the file already has — no new definition, no theory budgeted.

Here `hdim` (relative dimension) and `m : Mult abK (𝓞 D)` (real multiplication) are
spent by disjoint halves of Mumford *AV* §19 Thm 4 — homogeneity of degree `2g` uses
the dimension, the monomial/Galois rigidity uses that `D` is a field. So
`deg [a]^{[D:ℚ]} = #(𝓞_D/(a))^{2g}` split into `deg [n] = n^{2g}` (no number field)
and `∃ k, ∀ a ≠ 0, deg [a] = #(𝓞_D/(a))^k` (no `SmoothOfRelativeDimension`), with an
assembly that reads the second at `a = 2` where the first evaluates the same degree.

**Why:** a split whose halves each mention fewer hypotheses is dispatchable at someone
who needs to know only half the setting, which is the real measure of a cut. The count
goes UP (`1 → 2`) and must be reported that way — the "fewer OPEN leaves" tie-breaker
is for choosing between RIVAL cuts, not an argument against a split into independent
theorems.

**How to apply:** before writing any Lean, list the leaf's hypotheses, list the steps
of the literature proof, and mark which step consumes which hypothesis. If the marking
partitions, cut there and write the assembly first (glue-first) to prove the partition
is real — the compiler checks it in seconds.

Companion technique, same run: **several recorded refutations with a COMMON
counterexample name their own residue.** That file recorded three refuted axes, all
with the same witness (a split prime with unequal local degrees). The statement that
kills the common witness *is* the missing content, and saying so is a proof of
minimality rather than a claim of sufficiency. Corollary for writing refutations:
record the WITNESS, not only the verdict — three witnesses are comparable, three
verdicts are three dead ends.

Related: [[flt-leaf-cost-estimates-are-hypotheses]],
[[flt-decomposition-verdict-cost-list-is-a-hypothesis]],
[[flt-atomicity-verdict-checks-hypotheses-only]].
