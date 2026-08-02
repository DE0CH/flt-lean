---
name: flt-relocation-cost-and-payoff-differ
description: "A relocation's cost is measured at the theorem whose statement you want; its payoff at the theorem you will cite — routinely 12x apart"
metadata: 
  node_type: memory
  type: project
  originSessionId: 737d6040-110f-4360-987e-9c7de2569969
  modified: 2026-08-01T18:26:03.269Z
---

(2026-08-01, `flt-lean-341`, extracting `HardlyRamified/Family.lean`'s Raynaud cone
down to `HardlyRamified/Threeadic.lean`.)

Measure the closure of the theorem you will **cite at the call site**, not of the one
whose name matches the mathematics. Here `isMultiplicativeType_corner_of_inertiaLevelOneFlag`
(coefficient-free, on the corner Hopf algebra) is **6 decls / 489 lines**, while the bridge
to any statement about the connected LOCUS OF POINTS —
`connected_point_smul_eq_cyclotomicCharacter_smul_of_hopf_package` — is **105 decls /
5752 lines**. The prompt costed it at "~2600", which is neither.

**And "coefficient-free" says nothing about whether you can USE it.**
`HasInertiaLevelOneFlag p G` is genuinely intrinsic, which is what makes it look free to
supply. It has exactly ONE producer in the tree, and that producer carries `hchar` —
global reducibility of `ρ` over `ℚ̄_p` by two continuous characters. So the hypothesis diff
of the theorem you want comes back CLEAN while the theorem stays uninstantiable: the cost
was pushed one level down into the predicate. Run, beside the hypothesis diff:

    grep -n '<Predicate>' <file>     # separate CONCLUSIONS from `h…` BINDERS

One conclusion and six binders = bottleneck; the producer's binder list is the price.

See [[flt-nonpublic-import-duplicate-cut]] for the third finding of that run: a transitive
import path through a NON-PUBLIC edge re-exports nothing, so "X reaches Y transitively"
never licenses "X can name what Y imports". Related: [[flt-leaf-cost-estimates-are-hypotheses]],
[[flt-inventory-audits-understate-what-exists]].

**When the plan dies, the residue is the deliverable** — name the missing producer, with
the numbers and the refutation, on the LEAF, stamped with the sha.
