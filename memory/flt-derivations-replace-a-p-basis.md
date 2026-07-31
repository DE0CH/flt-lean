---
name: flt-derivations-replace-a-p-basis
description: A dual family of derivations proves each step of the K^p-tower has degree p, so `ker d = K^p` needs no p-basis — the thing mathlib does not have
metadata:
  type: project
---

The classical proof that `{x ∈ K : dx = 0} = K^p` (`k` perfect, char `p`, `K/k`
finitely generated) writes `x` in the `K^p`-basis of monomials `t^α`, `α < p`
componentwise. That basis is a **p-basis**, and there is none in mathlib
(`grep pBasis` returns nothing at pin `a3364fa`). Costing the leaf off that
route makes it look like it needs a whole missing theory.

**It does not.** Once `Ω[K⁄k]` is free on `dt₁,…,dt_d` you have derivations
`∂ⱼ` with `∂ⱼ tᵢ = δᵢⱼ`, and *they* supply the degree count for free:

* `K^p ⊆ M := K^p(t₁,…,t_{j-1})` and `∂ⱼ` kills `K^p` (`D(y^p) = p·y^{p-1}Dy = 0`)
  and kills each `tᵢ`, `i < j` — and the kernel of a derivation is a SUBFIELD,
  so `∂ⱼ` kills all of `M`;
* therefore `tⱼ ∉ M`, because `∂ⱼ tⱼ = 1 ≠ 0`. That is the whole degree-`p`
  argument: `minpoly M tⱼ = X^p − C(tⱼ^p)` follows from
  `X_pow_sub_C_irreducible_of_prime` plus freshman's dream, and then polynomial
  division by the minpoly plus `derivative f = 0 ⇒ f` constant finishes.

So: peel the tower one generator at a time, each step ~60 lines, instead of
building a p-basis. Written up as `FLT.mem_of_derivation_step` and
`FLT.mem_of_forall_derivation_eq_zero` in
`Fermat/FLT/Mathlib/FieldTheory/KaehlerField.lean` (2026-07-31, sorry-free).

The general shape, worth reusing: **a hypothesis that a linear functional takes
the value 1 on a generator is a non-membership statement in disguise**, and
non-membership is usually what a degree count was wanted for.

See [[flt-omega-free-by-composing-formally-etale]] for where the `∂ⱼ` come from,
and [[flt-inventory-audits-understate-what-exists]] for the same failure mode
one level up (an audit's "MISSING MACHINERY" list is reliable about absence,
not about what the absence costs).
