---
name: flt-same-theorem-operator-on-other-side
description: "Two leaves can be one theorem with an operator on opposite sides of the equation; only the docstring PROSE matches, never the identifiers."
metadata: 
  node_type: memory
  type: project
  originSessionId: ab11faf7-7d5a-4e47-8ce3-599d46d18322
  modified: 2026-08-01T23:14:23.839Z
---

`det ρ_{E,n} = χ_n` (Silverman *AEC* III.8.1(e)) was carried as TWO `sorry`
leaves in two modules, with the determinant on opposite sides:

    WeilPairingDet.galois_apply_primitiveRoot_eq_pow_det  -- σ ζ = ζ ^ det(σ|E[n]), ζ primitive
    Modularity.det_nTorsion_eq_cyclotomicExponent         -- det(σ|E[n]) = c, given σ ζ = ζ ^ c

No shared identifier, no shared statement shape, different types. `dupstmt.py`
and `xdup.py` both blind by construction; every frontier scan honestly counts two.
**What matched was the prose `det ρ_{E,n} = χ_n` in both docstrings.**

So: grep for the CITATION and the classical statement in words —
`grep -rn 'III.8.1\|det ρ_{E,n}' --include=*.lean Fermat/` — not for names.

General shape: a leaf concluding `f(x) = c` and a leaf whose hypothesis names `c`
and concludes `g(c) = y`. Commonest here: determinant-vs-exponent,
degree-vs-valuation, index-vs-order.

**Accounting:** the downstream one was DERIVABLE from the upstream one, which was
already in its cone, so closing it added no `sorryAx` edge — a `−1` that buys no
mathematics. Say so; instruments cannot tell that from a real closure.
See [[flt-two-leaves-may-be-one]], [[flt-consumerless-leaf-is-dead-or-duplicate]].
