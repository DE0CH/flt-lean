---
name: flt-separation-audit-misses-citation-duplication
description: "A leaf kept separate from its sibling on quantifier grounds can still duplicate it — compare the THEOREM NUMBERS the two cite, not their statements."
metadata: 
  node_type: memory
  type: project
  originSessionId: cbf037b2-6919-464d-a4bf-b4879a9ee650
  modified: 2026-08-01T23:13:02.551Z
---

A `∀`-shaped leaf deliberately kept independent of its `∃`-shaped sibling
("it asserts no inhabitant, so it cannot subsume representability") can be
sound about the STATEMENTS and still be a duplicate, because the duplication
lives in the CITATIONS.

2026-08-01, `X0.lean`: `isAffine_rigidifiedModuliSchemeData_of_isUnit` was
kept apart from the two representability leaves for exactly that reason, and
the reason was correct. Its own docstring then said its content is
"`M(𝒮)` is affine" and "`M(𝒮, Γ₀(N)) ⟶ M(𝒮)` is finite" — the affineness
clause of Katz–Mazur **(4.7.2)** and the finiteness clause of **(6.6.1)**,
the same two theorems the other two leaves cite. One citation pair, three
obligations.

**Repair: not a fusion (which the separation audit rightly forbids) but
moving each clause onto the leaf that already cites its theorem.** Then the
third leaf has no citation left and is two lines. Frontier 101 → 100 in that
module, nothing opened, no leaf's reading grew.

**Detection, one pass:** read each leaf's "what is genuinely cited here"
sentence and compare NUMBERED RESULTS. Two leaves naming the same numbered
theorem are one citation split in two, however disjoint their Lean statements
look. Nothing else sees it — here the three statements shared no identifier
and all three were honestly open and unowned.

Riders: ask for the WEAKEST clause the consumer uses (`IsAffineHom π`, not
the `IsFinite π` the citation gives — `IsFinite` extends it, so the prover
loses nothing); check the twin file first, since `X1.lean` had done the same
cut a day earlier and it transcribed mechanically; and keep the old name as a
one-line corollary so no call site moves.

See [[flt-two-leaves-may-be-one]], [[flt-transport-the-twins-recut]],
[[flt-equivalence-prose-is-a-free-leaf]].
