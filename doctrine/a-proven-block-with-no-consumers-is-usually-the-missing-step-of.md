## A PROVEN BLOCK WITH NO CONSUMERS IS USUALLY THE MISSING STEP OF A NEARBY LEAF
(2026-08-02, `flt-lean-98`, closing `connected_locus_le_line_of_hopf_package` in
`HardlyRamified/Threeadic.lean`.) This file already has a rule for a leaf that is open
and DEAD (grep its consumers before proving it). The mirror case is more valuable and
nobody checks it: **a PROVEN theorem with no consumers, sitting on an open leaf.**
`exists_uniform_pow_localInertia_smul_connected_of_{threeTorsion_trivial,
threeTorsion_uniform,hopf_package}` was a three-declaration chain — one open leaf plus two
proven theorems over it — with **zero code occurrences anywhere under `Fermat/` other than
its own declarations**. Free-floating, which this project forbids. Its top theorem is
exactly the input the target leaf needed ("local inertia acts on the connected locus by ONE
natural number"), and consuming it turned a leaf priced at *Wiles's dévissage up the
`𝔪`-adic filtration* into a leaf about `3`-TORSION only.
**The check is one comment-stripped scan and it runs on the file you are already in:**
    for each PROVEN theorem in the file: count code occurrences of its name tree-wide
    == 1 (its own declaration)  ⇒  free-floating
A consumerless proven block was built FOR something; the author cut it, ran out of run, and
nobody wired it in. In a file where you are stuck, it is the single most likely thing to be
the step you are missing — and wiring it in is a structural win independently of your leaf,
because the alternative fate of free-floating code is deletion.
Corollary about the ACCOUNTING, since it is the shape that hides this work: the cut was
`3 → 3` direct sorries. Nothing closed on net. What changed is that the residue lost `n`,
the congruence level, the dévissage, the given generator and the Nakayama endgame, and
became the `hstab` hypothesis of a PROVEN sorry-free theorem two modules away. Say that in
the commit, because a `−1 +1` delta is indistinguishable from "nothing happened".
### Two riders, each of which cost a cycle
* **"X was deleted, recover it from git" is a claim to CHECK, not to act on.** The leaf's
  docstring said `le_span_singleton_sup_smul_pow_of_displacement_surjective` had been
  deleted with a refuted cone and was recoverable at a named commit; the dispatching prompt
  repeated it with the line number. It is **present and proven** in the same file, 1800
  lines above the leaf — it survived precisely because it never touched the refuted leaf,
  which the same docstring also says. One `grep -n` settles it, and it is the difference
  between using a lemma and re-deriving it. Same family as
  [[flt-deletion-claims-are-not-deletions]], now with the false claim inside the leaf's own
  docstring AND inside the prompt generated from it.
* **A scratch module must replicate the target file's `attribute [local instance]` lines,
  not only its `namespace`, `open`s and `local notation`s.** `Threeadic.lean:108` carries
  `attribute [local instance 2000] AlgebraicClosure.instAlgebra
  IsDedekindDomain.HeightOneSpectrum.instAlgebraAdicCompletion`, with a comment saying the
  project's import closure otherwise shadows the canonical `Algebra ℚ` instances. Without
  it, a term that the real file accepts fails in the scratch with an **`Application type
  mismatch` between two printed types that differ nowhere visible**, plus a
  `definitions were not unfolded because their definition is not exposed: IsAlgClosed.lift`
  note — which reads as a module-system problem and is an instance-diamond problem. Copy the
  whole preamble between `namespace` and the first declaration, not just the notations.
And the throughput number, because it is the reason this was affordable: the scratch loop
against the built olean was **8–20 s** per iteration, and one `lake env lean` of the real
11 000-line `Threeadic.lean` is **40 s**. The whole proof (≈270 lines) went from first draft
to green in seven scratch rounds and compiled in the real file first try.
