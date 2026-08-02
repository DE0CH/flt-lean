---
name: flt-close-duplicate-cut-by-renaming-winner
description: "When a duplicated cut leaves a sorried loser far ABOVE the proven winner, rename the winner to the loser's name — do not prove the loser and do not just delete it."
metadata: 
  node_type: memory
  type: project
  originSessionId: 31a477a6-a2f3-44d8-ba06-e11fae63e4a4
  modified: 2026-08-01T13:08:34.407Z
---

(2026-08-01, `flt-lean-24`, `exists_pow_Pz_mul_mem_idl` /
`exists_pow_X7_mul_mem_idl` in `ProjectiveEquationAdd2.lean`.)

Two branches cut `idl_isPrime` identically under different names; the union merge
kept both. The `X7` copy was PROVEN at line 1093 and consumed by `idl_isPrime`;
the `Pz` copy was a `sorry` at line 552 with **zero consumers**.

`[[flt-both-rival-cuts-landed]]` says to delegate rather than re-prove. That is
impossible when the loser sits ABOVE the winner — Lean has no forward reference —
which is the normal case, since the winner drags its machinery with it.

**Rename the WINNER to the loser's name, restate it in the loser's statement
shape, delete the stub.** Proof untouched; canonical name and statement survive;
count drops by one. Here the shapes differed only in existential placement
(`(∃ n, P n) ∨ (∃ n, Q n)` vs `∃ k, P k ∨ Q k`) — two lines of the proof's tail.

**Why:** proving the loser duplicates the machinery above it for a dead
declaration; deleting it throws away a name other branches and queue entries may
cite.

Three checks, all load-bearing:

* **The module docstring usually names the canonical side** — this one said the
  `X7` pair "should be DELETED once the saturation leaf is closed". Follow the
  file's recorded decision, not the name attached to the surviving proof.
* **Confirm the interface change is contained first** (it is a class-7 split
  otherwise): grep the removed names tree-wide, and
  `git diff --stat main merger -- <file>` must be empty.
* **A duplicated cut duplicates proof STEPS too.** `idl_isPrime` re-derived inline
  the induction that the proven `mem_idl_of_pow_Pz_mul_mem` states 600 lines
  above — so that declaration was free-floating. Folding it back made it live.

**Report the arithmetic honestly:** `−1` direct sorry, **zero** transitive change
(nothing reached the leaf). What genuinely changed: the module has no open leaf,
`equation_add2XYZ` is axiom-clean, and no future agent is dispatched at a dead
declaration. See [[flt-consumerless-leaf-is-dead-or-duplicate]].
