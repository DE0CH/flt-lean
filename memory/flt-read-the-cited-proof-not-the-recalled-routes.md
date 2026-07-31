---
name: flt-read-the-cited-proof-not-the-recalled-routes
description: A leaf that names a literature theorem AND prices "the only two routes" has usually priced the two famous routes, not the one its own citation takes — open the cited proof
metadata:
  type: project
---

`Interface.lean`'s strong-multiplicity-one leaf cited Miyake Thm 4.6.19 as its
statement and priced closure as *Rankin–Selberg* (no Rankin–Selberg integral in
the pin) or *Casselman* (no adelic dictionary), concluding a successor "should
expect to BUILD one of the two missing analytic theories". Both absence claims
are true and re-verified. **Miyake's own proof is neither**: functional equation
of `Λ` (Cor 4.3.7) + Euler products (Thm 4.5.16) + `f ∣ ω_N = c·f` for a
primitive form (Thm 4.6.15(2)) + a `p`-by-`p` local-factor comparison in which
Ramanujan (Thm 4.6.17) kills the bad cases.

Three of those four were already in the tree, sorry-free and reachable through
`X0.lean`'s public import of `ModularCurve/WeightTwoEigenform.lean`:
`cuspFEPair N hN f` IS the pair `(f, f ∣ W_N)` with `isStrongFEPair_cuspFEPair`
PROVEN (so mathlib's `IsStrongFEPair.Λ_eq` is the functional equation);
`exists_isLFunctionOf_of_isWeightTwoEigenform` is the analytic continuation;
`exists_satakeParams_of_isWeightTwoEigenform` /
`norm_coeff_le_two_mul_sqrt_of_not_dvd` are Ramanujan–Petersson in weight two.
The fourth is a cut leaf upstream (`exists_frickeSlash_eq_smul_of_isNewEigenformAt`).
Genuinely unbuilt: the Euler product (mathlib has
`NumberTheory/EulerProduct/Basic.lean`; the multiplicativity is in-tree), a page
of algebra, and the `IsWeightTwoEigenform N f` vs `IsWeightTwoEigenform N f a`
carrier bridge.

**Why:** a route estimate is written from the routes its author could recall;
the cited source is the one place a different route is guaranteed to be written
down, and here it was in the same three pages as the quoted statement.

**How to apply:** when a docstring names a literature theorem and prices the
routes, `grep` the book on disk for the theorem number and read the PROOF before
believing the pricing. Extends
[[flt-inventory-audits-understate-what-exists]] from inventories to ROUTES; as
always the mathlib half of such a verdict is frozen with the pin and the
`Fermat/` half rots.
