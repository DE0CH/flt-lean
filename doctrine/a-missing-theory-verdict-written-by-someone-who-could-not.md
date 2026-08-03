## A "MISSING THEORY" VERDICT WRITTEN BY SOMEONE WHO COULD NOT IMPORT IT IS AN IMPORT FACT IN DISGUISE

(2026-07-31, `flt-lean-83`, `exists_frickeSlash_eq_smul_of_isNewEigenformAt`.) The leaf's
docstring said, in the file's usual careful style, that the proof "needs a genuinely missing
theory: Hecke operators as OPERATORS on `S₂(Γ₀(M))` … the commutation `W_M T_n = T_n W_M` …
and multiplicity one for the newspace", and backed it with a grep over `Fermat/`, the mathlib
pin and `~/cs/FLT/` that "returns no operator-level Hecke theory anywhere on this pin".

Every piece of that theory is PROVEN in this tree, in `Modularity/Interface.lean`:
`heckeTransform_slash_atkinLehnerRep` (the double-coset commutation),
`heckeOp_comm_atkinLehnerOp`, `heckeOp_apply_eq_smul_of_isWeightTwoEigenform` (the exact step
declared impossible — a coefficient-recurrence eigenform IS an operator eigenvector),
`exists_smul_of_heckeOp_eq_smul_of_not_dvd_level` (strong multiplicity one, in the leaf's own
conclusion shape) and the assembled `atkinLehnerOp_apply_eq_neg_qCoeff_smul`. Five
declarations, zero `sorry` among them.

**The mechanism, and it is systematic rather than a slip.** `Interface.lean` `public import`s
`ModularCurve/X0.lean`, so from inside `X0.lean` none of those names resolves, nothing
completes them, and no `example` referencing one will elaborate. An author working there
experiences the material as *absent*, and writes that down as a fact about the pin. The grep
that "confirms" it is then run with a mental filter for what could be used here, which is
exactly the filter that excludes the answer. Same shape as the self-certifying grep, but the
filter is the module graph rather than a spelling.

Two consequences worth acting on:

* **Run absence greps with NO import filter, then check reachability separately.** "Does it
  exist" and "may I name it here" are different questions and must be answered by different
  commands. Merging them turns a 200-line hoist into a "subtree to be built".
* **A cost-wall verdict in a file that sits UPSTREAM of the project's big interface module is
  suspect by default.** `X0.lean` had recorded this same error once before, for `heckeOp`
  itself; the repair was the hoist into `Modularity/HeckeOperator.lean` (612 lines, verbatim,
  justified by a reference scan showing the block named nothing else in `Interface.lean`),
  and `X0.lean` now imports it. That precedent is the template, not a one-off — when a leaf
  in an upstream module reports missing modular-forms theory, look for it in
  `Interface.lean` and price the hoist before pricing the mathematics.
* **Then actually PRICE it, by computing the closure rather than reading the section
  headings.** The five declarations above look like a `qCoeff`-plus-`AtkinLehner` shortlist;
  their transitive closure inside `Interface.lean` is **204 declarations and ≈ 9 000
  non-comment lines**, because multiplicity one runs on the Petersson inner product and drags
  in a fundamental-domain measure-theory block, the degeneracy operators, the oldform
  subspace and the Sturm bound. "The theory exists" and "the hoist is cheap" are separate
  claims; the first was the correction here, the second would have been a second error.
  A closure of that size must be dispatched as its own task and must not race a concurrent
  editor of the same file.
* **Compute the closure of what you ACTUALLY need, not of the headline theorem.** Dropping
  the one declaration whose conclusion names the eigenvalue's VALUE
  (`atkinLehnerOp_apply_eq_neg_qCoeff_smul`) took the closure from 204 declarations
  containing one `sorry` to **193 declarations containing none** — because the leaf being
  closed says `∃ c` and never asks what `c` is. A closure computed from the theorem that
  looks like your goal will routinely be bigger and dirtier than the one your goal needs.

The residue after such a hoist is usually small and is where the real work is. Here it is one
leaf: this file's `IsNewEigenformAt` (the sequence is not a stabilization) against
`Interface`'s `eigensystem_minimal` (no smaller divisor level realizes the eigensystem). The
two carriers do NOT bridge definitionally, and the needed direction is Atkin–Lehner Thm 1 /
Diamond–Shurman Thm 5.8.3.

