## A NON-PUBLIC IMPORT UPSTREAM IS A DUPLICATE-CUT BLIND SPOT — GREP FOR THE CONTENT, NOT YOUR IMPORT CONE
(2026-07-31, `flt-lean-395`.  Three leaves, one piece of mathematics, cut by two
agents a day apart, and **every ownership and frontier check in this file passes on
all three.**)
`EllipticScheme.lean` is imported by exactly one module — `X0.lean` — and
**non-publicly, on purpose**: a `public import` propagates the reserved token `over`
and silently truncates a structure with a field of that name.  `X0.lean` records the
consequence for CONSUMERS and solves it with re-exports.  What nobody recorded is the
consequence for AUTHORS, one module further down:
* `X1.lean` `public import`s `X0.lean` and does not import `EllipticScheme` at all.
  So from `X1.lean` every declaration of `EllipticScheme.lean` is invisible — not
  merely unusable in a signature, but **absent from completion, from `#check`, and
  from any grep an author runs over their own import cone.**
* On 2026-07-30 `d528fc99` cut `exists_ellipticScheme_weierstrassChart_addEquiv_field`
  in `EllipticScheme.lean`: an elliptic scheme over ANY field `k`, with the chart and
  `Nonempty (RelPoint f (𝟙 (Spec k)) ≃+ (E⁄k).Point)`.
* On 2026-07-31 `f61f3888` cut `exists_ellipticScheme_of_weierstrass_field` in
  `X1.lean` — the SAME statement minus the chart conjunct — and then
  `exists_ellipticSchemeSection_of_weierstrassPoint`, weaker again.  Its docstring
  says the obstruction is that "`EllipticScheme.lean` is written at the concrete base
  `ℚ`" and budgets a ~12 000-line refactor.  **That was already false when written**:
  the file had grown a general-field layer (`exists_isIso_of_affineCharts_field`,
  `nonempty_addEquiv_of_weierstrassModel_field`) the previous day.
Why no existing check sees it.  The three statements share **no identifier**: one says
`(E⁄k).Point` and a chart, the others say `E.toAffine.Point` and an order.  `own.py`
and `leafstat.py` correctly report all three unowned and open; the frontier scan counts
three because there are three `sorry`s; the release build is green.  The duplication is
visible only by reading the two files together, and the import barrier is exactly what
stops an author from doing that.
**So, before cutting a leaf that generalises a base, a coefficient ring or a level:**
1. `grep -rn '<concept>_field\|{k : Type} \[Field k\]' --include=*.lean Fermat/` over
   the WHOLE tree.  Not your cone — the whole tree.  The generalisation you are about
   to budget for is routinely already half-done in the file you cannot see.
2. Ask which modules import the file you are generalising, and **whether any of them
   imports it non-publicly**.  A non-public import is a one-way mirror: that module can
   consume the file in proof bodies while every module below it is blind to it.
3. If your leaf's statement mentions none of the invisible module's vocabulary, you do
   not need a re-export and you do not need `public`: **a plain `import` reaches proof
   bodies**, so one non-public import line in YOUR file closes the leaf by `exact`.
   That is what was done here — `X1.lean` gained
   `import Fermat.FLT.ModularCurve.EllipticScheme`, and two leaves became two-line
   theorems.  Prefer this to a re-export in `X0.lean`: `X0.lean` is the hottest file in
   the tree (70 943 lines changed in the release-27 window alone) and every edit to it
   is a merge hazard, whereas an import line in your own file conflicts with nobody.
Corollary for docstrings, and it is the expensive half: **a leaf's "what a prover owes"
paragraph is a claim about another file, and it decays at that file's edit rate, not at
yours.**  This one named the obstruction precisely, priced it honestly, and was obsolete
within 24 hours because someone else fixed it.  Re-grep the named file before believing
a cost estimate about it — the same rule this file already states for
`[[flt-inventory-audits-understate-what-exists]]`, now with the import graph as the
reason the author could not have known.
