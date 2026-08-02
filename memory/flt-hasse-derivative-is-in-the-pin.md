---
name: flt-hasse-derivative-is-in-the-pin
description: "Schmidt's hyperderivative calculus is mathlib's Polynomial.hasseDeriv, with Leibniz, composition and the Taylor bridge — the Stepanov docstrings' 'genuinely required' means the JET recursion fails, not that the pin lacks it"
metadata: 
  node_type: memory
  type: reference
  originSessionId: b32ecbf6-4382-4a60-bb6a-9331617f15d1
  modified: 2026-08-02T09:55:16.307Z
---

Three docstrings in the `λ = 2` Stepanov cluster (`Modularity/Interface.lean`,
`Modularity/MoretBailly.lean`) say that over `𝔽_{p^f}` the jet route dies because
`stepanov_jet_dvd_core` needs `∀ j < M, (j ! : K̄) ≠ 0` (i.e. `M < p`) while
`2d(M+8)² ≤ q` forces `M ≫ p`, and conclude that **"Schmidt's hyperderivative
calculus in `K(X, 𝔶)` is genuinely required"**. The first clause is TRUE and the
second reads as *a theory that must be built*. It is in the pin:

    Mathlib/Algebra/Polynomial/HasseDeriv.lean
      Polynomial.hasseDeriv k : R[X] →ₗ[R] R[X]     -- LINEAR, over any CommRing
      hasseDeriv_mul   : hasseDeriv k (f*g) = ∑ ij ∈ antidiagonal k, ...   -- Leibniz
      hasseDeriv_comp  : (hasseDeriv k).comp (hasseDeriv l) = (k+l).choose k • hasseDeriv (k+l)
      natDegree_hasseDeriv_le : natDegree (hasseDeriv n p) ≤ natDegree p - n
      factorial_smul_hasseDeriv : ⇑(k ! • hasseDeriv k) = derivative^[k]
    Mathlib/Algebra/Polynomial/Taylor.lean
      taylor_coeff : (taylor r f).coeff n = (hasseDeriv n f).eval r

`factorial_smul_hasseDeriv` is the exact statement of what goes wrong with the jet
route and what fixes it: `stepanovJet` is `k! • hasseDeriv k`, and dividing by
`k!` is what needs `M < p`. `hasseDeriv` itself needs nothing.

So the missing input is NOT the univariate hyperderivative. It is the calculus in
the RING EXTENSION `K[X][y]/(F)` — differentiating a branch — which is genuinely
absent and is what §§7–9 is about. Say which of the two you mean when writing a
cost estimate; "the hyperderivative calculus" names both.

Same failure shape as [[audit-lacks-x-is-about-x]] and
[[flt-theory-absence-claims-need-a-directory]]: the verdict was about the ROUTE
(`stepanovJet`'s ordinary-derivative recursion) and was read as being about the
LIBRARY.
