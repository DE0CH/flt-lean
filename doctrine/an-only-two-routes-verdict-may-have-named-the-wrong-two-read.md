## AN "ONLY TWO ROUTES" VERDICT MAY HAVE NAMED THE WRONG TWO — READ THE PROOF IN THE SOURCE IT CITES
(Same leaf, same day, and it is what actually moved the node.)
The leaf's docstring priced its own closure as *"Rankin–Selberg: needs the
Rankin–Selberg integral, which this pin does not have"* or *"Casselman: needs
the adelic dictionary, of which this pin has NONE"*, and concluded that a
successor *"should expect to BUILD one of the two missing analytic theories, and
should cost it as such."* Both absence claims are TRUE and were re-verified.
The verdict is still wrong, because **the docstring cites Miyake's Theorem
4.6.19 as the statement and never reads Miyake's PROOF, which is neither
route.** Read on disk (`~/flt-sources/miyake1989modularforms.txt`, line 7988) it
is: the functional equation of `Λ` (Cor. 4.3.7), the Euler products (Thm
4.5.16), `f ∣ ω_N = c·f` for a primitive form (Thm 4.6.15(2)), and then a
`p`-by-`p` comparison of local factors in which the Ramanujan bound (Thm 4.6.17)
kills the bad cases.
Three of those four are ALREADY IN THIS TREE, sorry-free and reachable from the
leaf through `X0.lean`'s public import of `ModularCurve/WeightTwoEigenform.lean`:
`cuspFEPair N hN f` IS the pair `(f, f ∣ W_N)` with `isStrongFEPair_cuspFEPair`
PROVEN, so mathlib's `IsStrongFEPair.Λ_eq` is the functional equation;
`exists_isLFunctionOf_of_isWeightTwoEigenform` is the analytic continuation;
`exists_satakeParams_of_isWeightTwoEigenform` and
`norm_coeff_le_two_mul_sqrt_of_not_dvd` are Ramanujan–Petersson in weight two.
The fourth is already a CUT LEAF upstream
(`exists_frickeSlash_eq_smul_of_isNewEigenformAt` in `X0.lean`). What is
genuinely unbuilt is the Euler product — for which mathlib has
`NumberTheory/EulerProduct/Basic.lean` and this file has the multiplicativity it
needs — plus a page of algebra and a carrier reconciliation.
**The generalisable check, and it is one `grep` of a book already on disk:
when a docstring names a theorem in the literature AND prices the routes, open
the cited proof and see which route it takes.** A cost estimate is written from
the routes its author could recall; the cited source is the one place a
different route is guaranteed to be written down. Here the recalled routes were
the two famous ones and the actual one was in the same three pages as the
statement the docstring quotes.
Corollary about where such an estimate goes stale: absence claims about MATHLIB
are frozen with the pin, but this verdict's real error was about `Fermat/` —
`cuspFEPair`, the Satake parameters and the `L`-function all postdate it. The
standing rule ([[flt-inventory-audits-understate-what-exists]]) applies to route
estimates and not only to inventories, and the half that rots is always the
project half.
