---
name: flt-structure-supplies-a-numeric-constraint
description: Generalising a leaf away from the structure it was stated over can silently drop a NUMERICAL constraint that no hypothesis then expresses — check by comparing degrees/ranks/lengths on both sides
metadata:
  type: project
---

When cutting a leaf, the instinct is to make the residual statement stop
mentioning the project's own vocabulary — replace `P.sheaf p` by "an arbitrary
invertible sheaf `L`", replace the structure by its data. **That move can turn a
true statement into a false one, because the structure was supplying a numerical
constraint that no hypothesis of the generalised statement expresses.**

Concrete instance (2026-07-31, `X0.lean`). Cutting
`IsRelPicZeroOf.exists_flatSurj_ajListSum` produced the divisor half

> fppf-locally, `L ⊗ ⊗ᵢ𝒪(−yᵢ) ∼ 𝒪(−o)^{⊗ d}` with `d = #{yᵢ}`.

Stated for `L = P.sheaf p` it is Riemann–Roch and TRUE. Stated for an arbitrary
invertible `L` it is **FALSE**, by one line: over `S = T = Spec k` with `deg L = m`,
comparing fibre degrees on the two sides (the `RelPicEquiv` twist `π^*N` has fibre
degree `0`) gives `m − d = −d`, so `m = 0`. `P` was the only thing in scope carrying
"relative degree zero", and there is no degree theory at this pin to state it as a
hypothesis instead.

**The check is cheap and mechanical: read a numerical invariant off both sides of
the conclusion** — fibre degree, rank, list length, dimension — and see whether the
generalised hypotheses force it to agree. Here the tell was that `l.length` occurs
TWICE in the conclusion, once counting sections and once counting copies of `𝒪(−o)`.
Relaxing the two to independent numbers makes the statement true for arbitrary `L`
and USELESS, because the assembly's induction produces equal lengths by construction
and can no longer close.

So the seam to prefer is: keep the structure in the statement, and delete the parts
of it the residual proof does not use — here the group law, `aj` and `inj` all went,
and only `P.sheaf` stayed. Record the refutation of the tempting generalisation in
the leaf's docstring, or the next agent will "simplify" the statement into a false
one. See [[flt-cleaner-statement-harder-proof]] and [[flt-leaf-names-wrong-half-as-hard]].
