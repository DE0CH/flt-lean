## NEITHER IS A **DECOMPOSITION** — AND THE TWIN'S VERSION OF IT IS OFTEN STRICTLY STRONGER

(2026-08-02, `flt-lean-117`, `exists_stepanovRationalLinearFormsField_of_equationCount` in
`Modularity/Interface.lean`.) The section below says a FALSITY REPAIR does not reach the twin.
A DECOMPOSITION does not either, and it is easier to miss, because the twin's leaf is not
*wrong* — it is merely bigger than it needs to be, and nothing in the tree says so.

The instance. Schmidt's Weil-bound chain here runs in two parallel halves, `λ = 2` (irrational
branches) and `λ = 1` (rational branches), whose leaves are transcriptions of each other. On
2026-07-31 the `λ = 2` leaf was cut in two — an elementary Frobenius reduction
(`stepanov_ansatz_eval_sub_branchReduction_dvd`, which strips the two blocks `X^{qj}` and
`η^{qc}` from the ansatz) plus the real residue — and the parent became a **twelve-line**
proof. The `λ = 1` leaf was left in its old shape. The reduction lemma takes **no hypothesis on
the branch at all**, so it applied verbatim; the twin's cut was one `grep` away and sat unmade
for two days while the leaf drew dispatches.

**The check is cheap and it is not the falsity check: for each half of a twin pair, diff the
DECOMPOSITION DEPTH, not the statements.** Count the leaves each half rests on and read the
proof of the deeper one. If the deeper half's proof consumes a lemma whose hypotheses your half
also satisfies, the same cut is available. Here the tell was that the `λ = 2` parent's proof
body was twelve lines while the `λ = 1` parent's was `sorry` — two adjacent theorems with
near-identical statements and wildly different proof lengths is the signature.

**AND DO NOT STOP AT TRANSCRIBING — the twin usually has an extra hypothesis, and it usually
buys one more step.** The `λ = 2` reduction stops at `∑_{i,c} ζ^{qc}·E_{ic}(X)·η^i` with
`d²` polynomials over `K` and a scalar `ζ = η(x̄)` that is only in `K̄`. On a RATIONAL branch
`ζ = z̄` with `z ∈ K`, so `ζ^{qc} = z^c` **is a scalar of `K`** and is absorbed into the
coefficients: the residue becomes `∑_{i<d} G_i(X)·η^i` with `G_i ∈ K[X]` — `d` polynomials,
and no `K̄`-coordinate anywhere. That is a materially better leaf (it is literally "a single
`G ∈ K[X,Y]` with `deg_Y G < d` vanishes to order `M` along the branch", which is the shape the
literature's Case 1 works in), and it cost one extra 12-line lemma. **The rationality hypothesis
was doing nothing in the old statement and does the whole of the extra reduction in the new
one** — which is the general shape: a hypothesis that distinguishes the twins is exactly the
hypothesis the twin's cut can spend.

Two riders, both of which this run relied on:

* **The reduction lemma's own docstring said it needed no hypothesis on `η`**, in as many
  words, and that sentence is what makes the transcription legal. When you prove such a lemma,
  say which hypotheses it does NOT use — that sentence is what lets the twin reuse it without
  re-reading the proof.
* **A ROUTE AUDIT that says "this reduction is TRUE but is not a route" is a specification for
  the cut, not a prohibition.** This leaf carried one, at length, correctly: the pointwise
  Frobenius reduction is true and imposing it per point is `q·d·M` conditions against `q·M`
  unknowns, too many by the factor `d`. That is an argument against *counting* with it, not
  against *performing* it — performing it is exactly what moves the reduction out of the leaf
  and leaves the packaging behind. Move the audit to the new leaf verbatim when you do; its
  first half becomes the leaf's hypothesis and its second half is the leaf's residue,
  undiminished.

Accounting, in the shape the RECUT rule asks for: **1 → 1, and the receipt is one `-  sorry`
and one `+  sorry` in the diff** (plus a comment-stripped sorry-token count unchanged at 16,
validated against the build's 16 `declaration uses \`sorry\`` warnings for that file). No
signature moved, so no consumer could break. Judge it by what LEFT the leaf.

