---
name: flt-leaf-can-be-atomic
description: A leaf whose target is "the orbit exhausts the set" admits no cut — stability/finiteness/degree all fail; write the atomicity audit into the docstring, and prove both directions before any restatement
metadata:
  type: project
---

(2026-07-31, flt-lean-249, `MazurCMForm.minpoly_eq_of_isCMJInvariant` in
`Fermat/FLT/FreyCurve/MazurTorsion.lean`.)

When a leaf's conclusion has the shape **"the orbit EXHAUSTS the set"**, every
companion fact of the shape **"the orbit stays INSIDE the set"** leaves the whole
theorem standing and adds a leaf. Galois stability of the predicate, finiteness
of the set, and the degree identity `|orbit(x)| = deg_ℚ x` are all true, all
independently useful, and none of them is a cut — the third is outright circular
here, because `|set| = h(−4n)` is a sibling leaf's content.

**Why:** an audit establishing that no cut exists is worth as much as a cut, and
it is the only artefact that stops the next three owners re-deriving it. The
docstring is where it belongs, beside the FALSITY AUDITs that play the same role.

**How to apply:** name each candidate cut and classify it — *circular*,
*containment-not-exhaustion*, or *renaming* — and include the tempting steps that
are FALSE with their witness (here `ℚ(j(𝔟)) ⊆ ℚ(j(𝔞))` fails: `ℚ(j)` is not
normal over `ℚ`, `D = −23` giving a non-normal cubic, even though the ring class
field `K(j)` is). When the only move left is a RESTATEMENT, prove both directions
first in a scratch module with the project predicate mocked as an opaque
`P : ℚ̄ → Prop` — an accidentally STRONGER restatement manufactures a harder or
false leaf at an unchanged frontier count. See [[flt-reduce-to-an-open-leaf-not-a-proof]]
and [[flt-cleaner-statement-harder-proof]].
