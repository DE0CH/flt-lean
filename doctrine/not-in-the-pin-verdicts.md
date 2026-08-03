## not in the pin verdicts

(Cut verbatim out of CLAUDE.md's `THE GOAL: fully formalize Fermat's Last Theorem, no sorry, n` section at the 2026-08-03 doctrine split; nothing reworded.)

**A "NOT IN THE PIN" VERDICT IS A SEARCH RESULT, NOT A FACT — search for the OBJECT,
not for the THEORY** (2026-07-31, and it was worth roughly a whole classical theory).

`finrank_eq_one_of_forall_inertiaDeg_eq_one`, the density input of Chebotarev, was cut
with a docstring recording — as its reason for being deep — that "mathlib at this pin has
Dirichlet's theorem on primes in arithmetic progressions … and NOTHING over a general
number field", and the dispatching prompt repeated it as "there is no Chebotarev and no
Dedekind zeta anywhere in the pin (checked by grep on 2026-07-31)". Both are FALSE. The
pin contains

    Mathlib/NumberTheory/NumberField/DedekindZeta.lean
      NumberField.dedekindZeta
      NumberField.tendsto_sub_one_mul_dedekindZeta_nhdsGT   -- the CLASS NUMBER FORMULA
      NumberField.dedekindZeta_residue_pos

i.e. the simple pole of `ζ_K` at `s = 1` with nonzero residue, over an ARBITRARY number
field — the entire analytic depth of the classical argument. With it, the leaf went from
"build the analytic half of class field theory" to proven-in-a-day over three residual
statements of elementary Dirichlet-series bookkeeping.

**The failure mode is specific and repeatable.** The search was for the THEORY the
argument is usually narrated with ("Chebotarev", "Dirichlet density", "L(1,χ) ≠ 0"). What
was present was the OBJECT the proof actually consumes, under its own name, in a file
called exactly that. So: before costing a node off an absence claim, list the concrete
mathematical objects the proof needs — a zeta function, a residue, a counting asymptotic,
a covolume — and `ls` the mathlib directory each would live in. `ls
Mathlib/NumberTheory/NumberField/` would have ended this in one call.

Two corollaries, both paid for here:

* **A leaf's own "what it needs that the pin does not have" paragraph is the LEAST
  reliable line in its docstring**, because it is written by whoever declined to prove
  it, before anyone tried. Treat it exactly like the "MISSING MACHINERY" lists that
  [inventory audits understate what exists] already warns about.
* **Mathlib's proofs contain exported-worthy lemmas that are not exported.** The
  convergence input all three residual leaves need was sitting inside the class number
  formula's own proof body; lifting those eight lines out gave a proven
  `LSeriesSummable` at every real `s > 1`. When a mathlib theorem is *close* to what you
  want, read its PROOF, not just its statement.

