---
name: lift-to-root-of-unity-by-factoring
description: "To lift a unit to a root of unity in a valued field, factor X^M-1 — never look for Hensel; and MulChar.ofRootOfUnity is in the pin"
metadata: 
  node_type: memory
  type: project
  originSessionId: ddab20b8-4b94-4c7a-a277-5ba1e82099a0
  modified: 2026-08-01T05:58:38.209Z
---

(2026-08-01, `flt-lean-164`, closing the Teichmüller half of Stickelberger.) A leaf
packaged over a BARE valuation (only `v 0 = ⊤`, `v 1 = 0`, multiplicativity,
ultrametric) looks unable to support a lifting statement — no ring of integers, no
maximal ideal, no completion, so nothing for Hensel to act on. The leaf's docstring
said exactly that and priced a hand-built residue field plus a subgroup count.

**None of it is needed.** To get an `M`-th root of unity `ζ` with `v (ζ·w − 1) > 0`
from `v w = 0` and `v (w^M − 1) > 0`: put `y := w⁻¹` and use that `X^M − 1` SPLITS
over an algebraically closed field, so `y^M − 1 = ∏_ζ (y − ζ)`; a product of positive
valuation has a FACTOR of positive valuation, and that factor is the lift. Inputs:
`IsAlgClosed.splits`, `Polynomial.splits_iff_card_roots`,
`Polynomial.prod_multiset_X_sub_C_of_monic_of_roots_card_eq`.

**Generalisable: a lifting statement in a valued field is a PRODUCT-FORMULA statement
whenever the target set is the root set of a split polynomial.** Hensel is for lifting
along an approximation; ask which situation you are in before pricing anything.

Riders: `MulChar.ofRootOfUnity` (+ `ofRootOfUnity_spec`) is in the pin and BUILDS a
character of a finite field from a generator and a root of unity — one call, not a
search through `zmodEquivZPowers`. And "a root of unity of order prime to `ℓ` that is
`≡ 1` IS `1`" is cheapest via the GEOMETRIC SUM (`geom_sum_mul`), not via
`∏_{η≠1}(1−η) = d`.

See also [[flt-leaf-cost-estimates-are-hypotheses]],
[[flt-inventory-audits-understate-what-exists]].
