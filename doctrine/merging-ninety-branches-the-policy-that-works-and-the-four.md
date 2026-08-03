## MERGING NINETY BRANCHES: the policy that works, and the four checks that must go with it

(2026-07-31, release 24 — 92 branches, 51 clean, 41 conflicting, 1 declined.)

**Resolving to `ours` by default LOSES PAYLOAD, and the loss is silent.** Measured on this
batch: a plain `ours` resolution dropped branch-added declarations in 17 of the 41 conflicting
branches — 71 of them from `flt-lean-362` alone. The branch still becomes an ancestor, the
build is green, and nothing says the work is gone.

The policy that preserved both sides, per conflict hunk:

- **base empty** (both sides ADDED at the same point) → `ours + theirs`, *unless* every
  declaration `theirs` introduces is already declared in `ours` — then `ours` alone, because
  the same content reached `main` by another route and the union would duplicate it;
- **base non-empty** → `ours + theirs` whenever `theirs` declares a name the BRANCH ADDED
  (absent at the merge base) that `ours` does not have; otherwise `ours` plus the blocks
  `theirs` purely INSERTED relative to base (`difflib` opcodes, `insert` only).

That took 41 conflicting branches down to 7 needing hand work. **But the policy is only safe
because of the checks, and three of the four had to be fixed before they told the truth:**

1. *Every branch-added declaration is present in the resolved file.* Compute "branch added" as
   branch-decls minus MERGE-BASE-decls — not minus `main`'s, which flags every name `main`
   legitimately deleted.
2. *No newly duplicated declaration name*, **diffed against pre-merge `main`** — this tree has
   many legitimate same-name pairs.
   - **Qualify by NAMESPACE.** `fieldAct_mul`/`_one`/`_xx`/`_yy` exist in both `GeomPic` and
     `ConstFieldExt` in `HyperellipticJacobian.lean`; a flat scan calls all four duplicates.
   - **Keep DOTS in the name.** A regex ending the name at the first dot collapses
     `IsCharRootMultiset.eq_roots` and four siblings onto `IsCharRootMultiset` and reports it
     five times over.
   - **Strip comments LINE-granularly** (a block starts at a line whose first token is `/-`,
     ends at a line containing `-/`). Character-level nesting goes wrong on this tree's
     docstrings and then the scan cannot see real declarations at all.
3. *Block-comment nesting depth returns to zero in every file.* **This is the new one and it is
   the cheapest check in the list.** A conflict hunk can begin INSIDE a docstring; keeping
   `ours` keeps the `/--` while the `-/` was on the side you dropped, and the docstring then
   swallows the rest of the file. Four files this release. Lean says `unterminated comment` at
   the LAST LINE, thousands of lines from the damage, and the module plus everything importing
   it fails — twenty minutes into the release build. The scan finds all four in a second.
   The mirror case also occurs: `MordellWeil19.lean` kept HEAD's `-/` and then the branch's
   paragraph landed *after* it as bare prose, so 25 lines of English were parsed as Lean.
4. *The release build, three rounds minimum* — for the reason release 22 recorded: the errors
   are serialised behind each other by the import graph.

**And a fifth failure this policy CREATES, which no declaration-level check can see: a
duplicated HYPOTHESIS.** Two branches gave `DualStruct.weil_nondegenerate` the same level gate
in two different styles — one a named binder `(_hnF : (n : F) ≠ 0)`, one an anonymous
`(n : F) ≠ 0 →` — and the union demanded it twice while the sole consumer supplied it once.
That produced 22 `(kernel) application type mismatch` errors plus a
`declaration has metavariables`, all reported at the USE site, which reads exactly like a
broken proof and is not one. **When two branches repair the same statement, the union of their
edits is not the repair.** Diff the two signatures against the merge base before taking both.

Finally, the merge-order effect, since it is cheap to exploit: conflicts are evaluated against
`main` *as it stands when you merge*, so a branch that conflicts in one order can be clean in
another. 15 of this batch's branches went clean on a second pass simply because the earlier
merges had landed first.

