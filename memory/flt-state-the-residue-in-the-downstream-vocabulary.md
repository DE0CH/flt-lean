---
name: flt-state-the-residue-in-the-downstream-vocabulary
description: When a leaf's citation is PROVEN one module downstream, recut so the residue's conclusion is character-for-character the downstream theorem's, and prove the elementary half upstream.
metadata:
  type: project
---

(2026-08-02, `flt-lean-344`, `irrationalJ_of_selfNIsogenyPair_oneSixtyNine` in
`ModularCurve/X0.lean`.)

That leaf's docstring priced it at "the theory of complex multiplication ...
**Absent from mathlib as of this pin**: `grep -rn
"classPolynomial\|HilbertClassPolynomial\|ringClassField"
.lake/packages/mathlib/` returns nothing." The grep is correct and it is the
wrong tree. The entire discriminant-`−676` apparatus is PROVEN in
`Fermat/FLT/FreyCurve/MazurTorsion.lean` — `classPoly676_of_endSq_neg169`,
`classPoly676_no_rat_root`, `not_exists_thirteen_mul_of_ker_order_169`,
`classNumberOne_of_end_closure_eq_top` — which `public import`s `X0.lean`, so
nothing in `X0.lean` can name it.

**The move, when you find that, is NOT to hoist blind and NOT to stop.** A
hoist of four declarations plus their cone out of a 47 000-line contended file
is its own task. What one run CAN do, and what pays permanently:

1. **Split off whatever half of the leaf is ELEMENTARY and prove it upstream.**
   Here the leaf `W.j ∉ ℚ` bundled the CM identification of `j` with "the six
   roots of `H_{−676}` are irrational". The second is the rational root theorem
   plus one congruence mod `5` — 60 lines, no elliptic curve in it — and it is
   already PROVEN downstream, so copy it upstream **under a different name**
   with a docstring saying which copy should survive (CLAUDE.md's deliberate
   duplication rule). Byte-identical proofs of one proposition cannot drift.
2. **Restate the residue so its conclusion is CHARACTER FOR CHARACTER the
   downstream theorem's.** The new leaf concludes "`W.j` is a root of this
   degree-`6` literal", which is exactly `classPoly676_of_endSq_neg169`'s
   conclusion. When the hoist lands the leaf closes by ONE application instead
   of by a fresh development.
3. **Write the downstream inventory into the leaf's own docstring**, with the
   one-command refuting check (`grep` the name, read whether its body is
   `sorry`). That is the artefact that stops the next three agents re-deriving
   "CM theory is missing".

The count is `1 → 1` and must be reported that way; what changed is the surface
area of the residue, not the number of leaves.

**The generalisable check, and it costs one grep**: before believing a leaf's
"what proving it needs" paragraph, grep `Fermat/` for the CONCLUSION's shape —
here the degree-`6` coefficient literal itself, which is unmistakable — not for
the theory's name. An absence claim that quotes a `.lake/packages/mathlib/`
grep has by construction not looked in this project. Same family as
[[flt-inventory-audits-understate-what-exists]] and
[[audit-lacks-x-is-about-x]]; the new wrinkle is that the answer was DOWNSTREAM,
so even a whole-tree grep for the identifier only tells you that you cannot use
it — you still have to decide what to do, and (1)–(3) above are the answer.
