---
name: flt-tower-needs-uniqueness-not-closure
description: "A \"choose the witnesses compatibly at every level\" leaf cannot be closed by a closure property — the recursion has no base case — so the uniqueness citation is unavoidable."
metadata: 
  node_type: memory
  type: project
  originSessionId: 6bc5ee82-4fcd-4c61-bc43-fab082d8f0c4
  modified: 2026-08-01T22:53:02.258Z
---

(2026-08-01, `flt-lean-371`, `nonempty_pDivisibleTowerAt_of_forall_hasFlatProlongationAt`
in `Fermat/FLT/Modularity/Interface.lean`.)

A leaf of the shape *"property `P` holds at every level `k`; choose the witnesses
COMPATIBLY"* looks like it should fall to an existing closure lemma. In this tree
`IsFlatPointsGroupAt.of_surjective` (`Deformations/RepresentationTheory/FlatPointsGroup.lean`)
is exactly the tempting one: it takes a flat model of `X`, an equivariant surjection
`X ↠ Y`, and produces a flat model of `Y` **as a Hopf order inside the given one** —
i.e. it even builds the comparison map.

**It cannot close such a leaf: a closure property runs DOWN the tower and the tower is
infinite UP.** Building `G k` from `G (k+1)` has no base case; building `G (k+1)` from
`G k` is "the model of level `k` inside any model of level `k+1` is isomorphic to the
one already chosen", which is UNIQUENESS. Check both directions before believing the
citation is avoidable — it took an afternoon here and the answer was no.

**Why:** the right move is then the DECOMPOSITION — name the citation, state it in the
one shape the consumer consumes, prove the leaf over it. Here: Raynaud–Fontaine full
faithfulness at `e < p − 1`, cut as `exists_algHom_of_hom_flatProlongation`, and the
leaf closed in ~20 lines (`choose` a model per level; the tower's reduction map is
equivariant by one `TensorProduct.induction_on` since `ρ.baseChange` acts through the
RIGHT tensor factor while the reduction acts on the LEFT; feed it to the citation).

**How to apply:** to tell a genuinely-new citation from one the tree already has, read
what the NEIGHBOURING DOCSTRINGS SAY THEY DECLINED, not just a name grep.
`Deformation.lean`'s `hasFlatProlongationAt_of_prod_injection` says in as many words
that Raynaud's bound governs UNIQUENESS "which is not asserted here; EXISTENCE by
schematic closure holds over an arbitrary DVR", and `isFlatAt_of_fibreProduct` says the
uniqueness route "is not the route taken". A development that has deliberately routed
around a theorem several times, in writing, is far stronger evidence of its absence than
any grep — and it also tells you which hypothesis the new leaf must carry.

See [[flt-inventory-audits-understate-what-exists]] for the opposite failure, and
[[flt-cut-at-the-missing-object]] for the general shape of naming the citation.
