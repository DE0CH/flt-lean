---
name: flt-equivalence-prose-is-a-free-leaf
description: A docstring paragraph arguing two leaves are equivalent is a proof that one of them is free — merge them instead of believing the caveat
metadata:
  type: project
---

When a leaf's docstring answers the junk-witness worry with "any two inhabitants
are related by a unique isomorphism, and the property is isomorphism-invariant,
so `∀` and `∃` say the same thing here", that paragraph **is a proof sketch that
the `∀` leaf is free over the `∃` one**. Write it in Lean and the two leaves
become one. Done 2026-07-31 for both `Gamma1RigidifiedModuliScheme` (X1.lean)
and `RigidifiedModuliScheme` (X0.lean); each cost a ~30-line rigidity lemma over
`universal`'s uniqueness clause plus `IsBaseChangeOf.refl`/`.comp`, and each
dropped its file's direct-sorry count by one.

**Why:** the prose gets written precisely when a cut separates a citation from a
formalisation, and the author has to justify the `∀`-shaped residue. The
justification is the merge. Both X0 and X1 also carried an explicit "if a prover
would rather not pay it, weaken to `∃` … but then the halves fuse back together,
which is what this cut exists to prevent" — the sign was backwards: the two
halves were never separately provable (Katz–Mazur 8.1.1's affineness clause is a
remark on 4.7.2's construction), so fusing is a strict win by the
fewer-OPEN-leaves tie-breaker.

**How to apply:** sweep docstrings, not just `sorry` tokens, for `are the same
statement`, `up to unique isomorphism`, `invariant under isomorphism`,
`junk-witness`, `would rather not pay`. If the needed calculus lemmas sit below
the leaves, hoist the calculus rather than relocating the leaves — check the
range is namespace-balanced and that nothing in the skipped span uses the moved
names, then the move is verbatim. Still open in this shape:
`exists_rigidifiedModuliScheme_specF` / `isAffine_of_rigidifiedModuliScheme_specF`
over `RigidifiedModuliSchemeData` in X0.lean. See [[flt-two-leaves-may-be-one]]
and [[flt-cut-leftovers-close-sibling-leaves]].
