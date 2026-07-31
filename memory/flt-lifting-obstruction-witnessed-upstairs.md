---
name: flt-lifting-obstruction-witnessed-upstairs
description: A leaf blocked because "the witness is not rational over k" may need no descent at all — if the property being contradicted is a LIFTING property, exhibit the obstruction over an extension, which is itself a k-algebra
metadata:
  type: project
---

`exists_weierstrassModel_of_ellipticScheme_field` (X0.lean) sat open because the
proven `ℚ`-chain carried `[PerfectField K]`, inherited from
`exists_singular_of_Δ_eq_zero`: over `𝔽₂(t)` the curve `y² = x³ + tx` has `Δ = 0`
and its singular point sits at `x = √t`, outside the base. Two docstrings priced
the fix as "testing smoothness after base change to `k̄` — a different argument",
i.e. as needing `L ⊗[K] CoordinateRing ≃ₐ[L] (E⁄L).CoordinateRing`, which the pin
does not have.

**It needed no base change of the object.** The property being contradicted was
`Algebra.FormallySmooth K R`, and formal smoothness over `K` lifts along EVERY
square-zero extension of `K`-ALGEBRAS. So the base stays `K` and only the TEST
RING grows, from `K[t]/(t³)` to `k̄[t]/(t³)`; `k̄` is perfect, so the singular
point exists there. Total cost: one generalised lemma, three
`IsScalarTower.algebraMap_apply K L _` rewrites, no new theory. Closed 2026-07-31.

**Why:** an extension `L/K` is itself a `K`-algebra, so anything built from `L` is
an admissible test object for a `K`-lifting property. Rationality of a witness is
an obstruction to a *particular* proof, never to the statement, whenever the thing
being refuted is "lifts along square-zero extensions".

**How to apply:** before pricing a "the witness is not rational" node as needing
descent, base change, or Galois theory, ask what property the witness is meant to
contradict. If it is a lifting/formal property (`FormallySmooth`, `FormallyEtale`,
`FormallyUnramified`, or any `∃ lift` criterion), take the witness upstairs and
enlarge the test object instead. Related: [[audit-searched-production-not-invariant]]
(the same shape — the audit searched for how to PRODUCE the object rather than for
the deciding invariant), and [[flt-cleaner-statement-harder-proof]].

Corollary that cost a compile cycle: `(E⁄L).toAffine.aᵢ` and
`algebraMap K L E.toAffine.aᵢ` are definitionally equal, so `exact` accepts either,
but `ring`/`linear_combination` treat them as DISTINCT ATOMS. Insert `rfl` haves and
`rw` them before any `linear_combination`.
