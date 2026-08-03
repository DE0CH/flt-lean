## AN EXISTENTIAL WRAPPER WHOSE OTHER CONJUNCT PINS THE WITNESS IS NOT A CUT — it is the same leaf, spelled longer

(2026-08-02, `flt-lean-284`, on `exists_heckeMatrix_qCoeff_of_x0HeckeCharpolyTable` in
`ModularCurve/X0.lean`.) A standard and usually good move here is to restate a leaf so it
ASKS FOR LESS: replace `P (someComplicatedTerm)` by `∃ A, Q A ∧ P A`, where `Q` is a
concrete, low-vocabulary description a prover can supply directly. The 2026-07-31 recut of
that leaf did exactly this — `charpoly (toMatrix b b (heckeOp N ℓ)) = c` became
`∃ A, (A reproduces the q-expansion recursion) ∧ A.charpoly = c` — with a docstring saying
"nothing about modular forms survives except `qCoeff` itself, which is a number."

**The recut bought nothing, and the tell is visible without any mathematics: `Q` PINS `A`.**
The file's own `toMatrix_heckeOp_of_qCoeff`, declared thirty lines above and PROVEN, says
`Q A → A = toMatrix b b (heckeOp N ℓ)`. So the existential has exactly one witness, `P A` is
the old statement verbatim, and the two leaves are logically equivalent — indeed the recut
leaf's own consumer is the old statement, derived from it. The prover's burden did not move.

**The check is one grep and it takes a minute: for each conjunct you are adding, ask whether
the file already proves that it determines the existential variable.** A uniqueness lemma for
`Q` — `Q A → A = <the term you were trying to get rid of>` — is the refutation, and in a
development that cuts as aggressively as this one that lemma is usually *already there*,
because somebody proved it in order to consume the recut. Its presence is the signal, not a
convenience.

Three riders:

* **The dual is also worth checking, and it is what makes the recut look attractive**: the
  ADDED conjunct is usually FREE (here, `Q (toMatrix b b (heckeOp N ℓ))` is `qCoeff_heckeOp`
  plus a basis expansion). A conjunct that is both free and pinning is pure packaging: it
  cannot make the leaf easier, because a prover can always discharge it, and it cannot make
  the leaf harder, because it forces nothing new.
* **Do not revert on this finding alone.** Both forms are equivalent, so a revert is churn in
  whatever file the leaf lives in — for `X0.lean` the most contended in the repo — and it is
  a rival cut against a one-day-old deliberate edit. Write the equivalence INTO the docstring
  with the two lemma names that witness both directions, so the next agent does not cut it a
  third time, and spend the run on the cut that does reduce something.
* **Where the reducing cut lives is usually one consumer FURTHER DOWN.** A banked constant
  cannot appear in a statement that quantifies over the object it depends on — here `A`
  depends on the universally quantified basis `b`, exactly as that leaf's docstring says. It
  can appear at the first consumer that CHOOSES that object; here
  `exists_basis_charpoly_heckeOp`, which builds its basis out of `finrank = d`. So when a
  "why the existential and not a named constant" paragraph correctly blocks a cut, do not
  stop — ask which declaration downstream fixes the offending parameter, and cut there.

