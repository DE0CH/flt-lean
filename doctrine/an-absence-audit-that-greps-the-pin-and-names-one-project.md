## AN ABSENCE AUDIT THAT GREPS THE PIN AND NAMES *ONE* PROJECT MODULE READS AS A PROJECT-WIDE CHECK — AND IS NOT ONE

(2026-07-31, `flt-lean-302`, `AbelianSchemeStruct.along_add_of_along_zero` in `X0.lean`.)
That leaf was cut as "the classical rigidity theorem for abelian schemes, ABSENT FROM THE
PIN, and this was CHECKED rather than assumed", with three case-insensitive `grep -rl`
runs quoted verbatim over `.lake/packages/mathlib/Mathlib` and `~/cs/FLT/FLT`, and then
this sentence:

> The only abelian-scheme development reachable from here is this project's own
> `Modularity/AbelianScheme.lean`, which states the structure and proves no rigidity.

All three greps re-run identically today. The last sentence is the false one, and it is
the only one about **this repository**. `grep -rn rigidity Fermat/` — one command, never
run — returns `AlgebraicGeometry.eq_comp_of_rigidity_axes` (PROVEN, in
`Fermat/FLT/Mathlib/AlgebraicGeometry/ProperPushforward.lean`, a **`public import` of
`X0.lean`**) and `Fermat.relPointPost_add` in `ModularCurve/EllipticScheme.lean`, which is
**the leaf's own statement**, proven 2026-07-27 and generalised from `Spec ℚ` to an
arbitrary base on 2026-07-29. The leaf closed as a **17-line bookkeeping bridge**.

Three things make this failure mode worse than the plain "inventory audits understate what
exists" already recorded above, and all three are cheap to defend against:

* **Naming one project module is what makes the paragraph convincing.** A verdict that
  said only "not in mathlib" invites the next reader to check the project. A verdict that
  says "the only development reachable from here is `X`, and `X` does not have it" reads
  as though the project half was searched too. It was not — one module was opened.
  **Quote the command, not the conclusion**, and if you did not grep `Fermat/`, say so.
* **"Reachable" is broader for a THEOREM than the public import graph.** `X0.lean` imports
  `EllipticScheme.lean` NON-publicly and on purpose; proof bodies are elided by the module
  system, so a non-public import reaches them and `relPointPost_add` was citable all along.
  An audit that reasons about what is "reachable" must say reachable *in a statement* or
  *in a proof body* — they are different questions with different answers.
* **The docstring contradicted another docstring in the same file, 29 000 lines apart.**
  This leaf called `relPointPost_add` "the `ℚ`-shaped special case"; `X0.lean:3261` says it
  "was already stated over an arbitrary base in everything but its signature — so it was
  generalised in place". Both were written from `X0.lean`. When two paragraphs in one file
  disagree about an upstream theorem's generality, the one that opened the theorem wins —
  go read the signature.

The standing check, before writing any "ABSENT" verdict and before believing one:

    grep -rn '<the concept, 2-3 spellings>' --include=*.lean Fermat/ | head
    grep -n 'import Fermat' <your module>        # non-public lines count for proof bodies

