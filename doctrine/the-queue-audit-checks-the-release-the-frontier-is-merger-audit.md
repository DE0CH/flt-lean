## THE QUEUE AUDIT CHECKS THE RELEASE; THE FRONTIER IS `merger`. AUDIT AGAINST `merger`.

(2026-07-31, `flt-lean-363`, measured: **three targets out of three** in one dispatch were
already proven.)

The fifth invisibility class above prescribes the right check —
`git show merger:<file> | grep -n <name>` — but states it as advice to the *worker*. The
dispatch side does not run it. A task dispatched this day named
`formalImmersion_of_cuspFormalImmersionCert`, `exists_isCusp_ne_neronSpAut_of_atkinLehnerPin`
and `redX_base_ne_of_isCusp`; all three are `sorry` on `main` and all three are **full `by`
proofs on `merger`**, which was 217 commits ahead. The audit that let them through was correct
about `main` and therefore useless: `main` is the frontier as of the last release, and 217
commits of proofs sit between it and reality.

Two things follow, and the second is the one that costs whole agents:

* **Audit queue entries against `merger`, not against the release.** One `git show` per
  candidate. It is the same command the doctrine already gives workers; run it where the task
  is written, not where it is received.
* **A leaf can be closed on `merger` *under a changed signature*.** All three above were not
  merely proven but restated — `q ≠ N` became `¬ q ∣ N`;
  `exists_isCusp_ne_neronSpAut_of_atkinLehnerPin` grew a generic-fibre pin `(wYQ, hwYQ, hpin)`
  because the integral moduli descent turned out to be impossible. So a worker who "finds it
  already proven" must compare the STATEMENT too before reporting the task obsolete; and a
  worker who proves the `main` version of such a leaf has written something that will not
  even elaborate after the merge.

Not a defect in the loop — the audit does what it says. It is the wrong reference tree.

**Corollary, same day and same shape: a leaf's SUPPORTING lemma can be WEAKENED on `merger`,
which silently invalidates a proof that is green on `main`.** `exists_diffCharScalar`
(`DifferentialCharacter.lean`) concludes an identity at every `P ≠ 0` off `ker φ` on `main`;
on `merger` it was proven, and the price was two new hypotheses in the conclusion,
`B.eval (x P) ≠ 0 → E.eval (x P) ≠ 0 →`. A three-line proof of
`exists_isCotangentScalar` over the `main` form compiles today and is *unprovable* over the
`merger` form. **So before building on a lemma, diff its statement against `merger` — not just
check that it exists.** A green build against a superseded hypothesis set is the "two
individually-correct repairs, fatal together" failure with a shorter fuse.

