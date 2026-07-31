---
name: flt-third-outcome-strengthen-the-axioms
description: A leaf over an axiomatized structure has a THIRD outcome besides prove/refute — the axioms under-determine it; strengthen the structure, but only if the construction that inhabits it pays nothing
metadata:
  type: project
---

When a leaf is stated over a `structure` that AXIOMATIZES an object (rather than
over a construction), "prove it" and "refute it with a counterexample" are not the
only outcomes. The third is: **the axioms do not determine the object where the leaf
looks**, so the leaf is neither provable nor refutable by an in-tree witness, and the
repair is to the STRUCTURE.

Found 2026-07-31 on `le_fixedSubmodule_gp_of_mem_Ioo` in
`Fermat/FLT/Deformations/RepresentationTheory/ArtinConductor.lean`.
`RamificationFiltration.gp_herbrand` pinned the upper-numbering filtration only AT
the Herbrand values `φ_D(m)`; the break decomposition needs it on the whole interval
`(φ_D(m), φ_D(m+1)]`. Inside the gap the axioms gave only a sandwich whose BOTH ends
are admissible. Probing with other levels is circular — the axiom relates every level
to `F` and no two levels to each other.

**The test that makes this a decision and not a shrug: does the CONSTRUCTION that
inhabits the structure satisfy the stronger axiom for free?** Here
`upperRamificationFiltration v u = P_v ⊓ ⨅_D D.gp (D.psiNat u)` and
`D.psiNat u = m+1` throughout the interval, so `≤` is `iInf_le` and `≥` is the
already-open leaf at the RIGHT endpoint composed with antitonicity. Zero new leaves.
If the construction had needed new input, the strengthening would have been a
disguised `sorry` and the answer would have been no.

Second thing to check, and it is what makes the trade safe rather than merely cheap:
which DIRECTION the consumers use the structure in. Strengthening shrinks the
admissible class, so `∀ F` theorems get weaker and `Nonempty` gets harder. Here
`IsSwanExponentAt = Nonempty ∧ ∀ F, …` and every `F` reaching a proof comes from the
construction, so both halves land on the safe side — and faithfulness IMPROVES,
because the genuine mathematical object is a singleton and every junk filtration
excluded is progress. Get that direction backwards and you have quietly weakened a
theorem instead of strengthening a model.

Write it up as a numbered FALSITY AUDIT in the structure's own docstring, keep the
analysis that proved the old axioms insufficient (it is the evidence for the repair),
and correct in place any route the leaf's docstring proposed that you found does not
work. See [[flt-cut-the-open-inclusion-not-the-equality]] for why the leaf was stated
as one inclusion — which is what made this diagnosis cheap.
