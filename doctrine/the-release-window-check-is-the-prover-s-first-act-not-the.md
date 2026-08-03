## THE RELEASE-WINDOW CHECK IS THE PROVER'S FIRST ACT, NOT THE ORCHESTRATOR'S

(2026-07-31, flt-lean-106, and it cost a full duplicate of a day-old file.)
The fifth-invisibility-class section above is written as advice to whoever
DISPATCHES. It is at least as much advice to whoever RECEIVES: a prover agent's
task prompt was built from `main`, and `main` is the frontier as of the last
release. **Run `git show merger:<file> | grep -n <declName>` for every leaf in
your prompt BEFORE your first edit** — it is one command per name and it is the
only thing standing between you and re-doing finished work.

What it cost here, concretely. Three leaves were named. On `merger`, two of the
three were **already proven** (`intBasis_indep_of_isCMByRamifiedMaximalOrder`,
`exists_isogenyCurve_thirtySeven`) and the third's missing bridge already existed
as a better-stated leaf with its own owner (`exists_end_of_relPointEndo`, which
strictly subsumes the `exists_endTransport_of_isCMByRamifiedMaximalOrder` this
worktree cut). Worse, `merger` already carried a
`Fermat/FLT/EllipticCurve/ThirtySevenKernelPolynomials.lean` at the SAME module
path, closing the SAME two rows, reached by the SAME quadratic-twist-by-`37`
insight, written a day earlier. Roughly a megabyte of generated Lean was
produced, compiled and verified for nothing.

Two things make this trap sharper than the section above suggests:

- **The prompt's own leaf list is the bait.** Every ownership check said the
  leaves were unowned, and every one was right: the owners had already stopped.
  "Nobody is working on it" and "it is already done" are the same observation
  from `main`.
- **A NEW FILE you are about to create is the highest-risk case, and the one
  nobody checks.** Ownership tests are written around declaration names in an
  existing file. A file that does not exist on your base has no name to grep and
  no `TARGET:` line to match, so it passes every test — while being exactly what
  a sibling agent decomposing the same leaf would also create, under exactly the
  same obvious name. So: **before writing a new module, `git show merger:<path>`
  and `git ls-tree merger -- <dir>`.** One command, and it is the only check
  that sees this.

The salvage, which is worth knowing because it turns a wasted run into a real
result: an independent second computation of a landed certificate is a genuine
cross-check. `gen37.py` was re-pointed at `merger`'s two models — different from
the ones it had generated — and re-confirmed `r_37 = 0` and the vanishing of the
reduced `multComp` sum at both rows. So the report to the merger is not "I
duplicated your work" but "your certificates are independently verified, decline
mine".

