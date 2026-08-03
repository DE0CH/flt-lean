## THREE RIVAL CUTS OF ONE NODE: BUILD THE UNION OF THE REDUCTIONS THEY EACH CALL "FREE", THEN DELETE THE LOSERS
(2026-08-02, `flt-lean-270`, the Abel-theorem cluster in `ModularCurve/X0.lean`.
Frontier `101 → 99` in that file with no mathematics done.)
The section above tells a merge worker how to choose between two rival cuts, and the
one before it how to spot a duplicated cut from a parent whose docstring names a
different leaf from its proof body. Neither covers what a PROVER should do when it
arrives and finds **three** rival cuts of one node all merged, one wired and two
consumerless. The answer is not to pick a winner.
**Each rival's docstring names the reductions IT considered free, and the free lists
are DIFFERENT.** Here:
* the wired leaf (`listSum_map_eq_of_relPicEquiv_divisor`) took a natural family `c`
  plus its naturality hypothesis, and its sibling's docstring recorded that Yoneda
  turns that pair into a single morphism `κ` — *"`_hnat` is GONE, not dropped"*;
* the morphism-form rival (`listSum_map_post_eq_of_listSum_aj_eq`) had `κ` and equal
  list lengths, and recorded padding-by-base-points as the free step that buys the
  equal-length reduction — and separately named, as *"THE NEXT REDUCTION TO TRY"*,
  converting its hypothesis from `aj`-sums to sheaves;
* the third (`..._of_compactSpace`) recorded the `T.affineCover` reduction.
Compiling ALL of them — three short theorems, ~60 lines — produces a residual
strictly better than any of the three rivals: it has `κ` (no `c`, no `hnat`), equal
lengths, and the hypothesis in sheaf vocabulary, so **the base point cancels out of
the hypothesis entirely** and the statement is the textbook one. Then both losers are
provable consequences of the survivor, hence deletable, and the whole cluster's
analysis folds into one docstring.
**"Free" in a docstring means "not written".** Every one of these reductions had been
described as costless by whoever declined to write it, and each was in fact 10–30
lines. A leaf that has been cut three times has three such lists sitting unclaimed;
they are the cheapest work in the file and nobody collects them because each
individual list looks too small to dispatch at.
**The cost of leaving the losers is measurable, not theoretical.** Both consumerless
leaves had already drawn a dispatch each (`flt-lean-88`, `flt-lean-93`); both runs
ended with no sentinel. A consumerless `sorry` is a phantom frontier slot that draws
agents forever, and the two here were drawing them at a classical theorem
(Abel/theorem of the cube) that no agent can close in a run.
**Before deleting, check for a LIVE owner and say what happens if one lands a proof.**
`~/.flt-loop/jobs/<name>.json` with `sentinel: None`, no live `flt-job-<token>`
process, and an age in hours is a DEAD owner; a live one means leave the leaf alone.
Either way put the contingency in `to_merger`: here, "if 88 or 93 land a proof of
either deleted leaf, keep the deletion and use their proof to close the survivor — it
is the same mathematics".
### The Lean lever that made the padding cheap: a POWER may be DEFINITIONALLY a special case
`basePointIdealPow o g n` (`𝒪(−o)^{⊗n}`) and `relSectionIdealProd l` (`⊗_{y∈l} 𝒪(−y)`)
are two recursions with the SAME step `Io ⊗ ·`, so
    basePointIdealPow o g n = relSectionIdealProd (List.replicate n (relBasePoint o g))
is an **equality**, proved by `induction n` with `rfl` in both branches. With it the
entire exponent calculus one would otherwise write — `𝒪(−o)^{⊗(m+n)} ≅ 𝒪(−o)^{⊗m} ⊗
𝒪(−o)^{⊗n}`, invertibility of `𝒪(−o)^{⊗n}`, the interaction with padding — is the
GENERAL family's `append` lemma at `List.replicate_add`, plus
`isInvertibleSheaf_relSectionIdealProd` which already existed. One lemma replaced four.
**So when a file carries both `F (replicate n a)` and a bespoke `powerOf a n`, check
whether they are the same recursion before proving anything about the power.** In this
development bespoke powers are common because the general family is usually introduced
later, for a different consumer, and nobody goes back.
### Two smaller things, both worth a minute
* **Yoneda for a natural family is `IsJacobianOf.aj_val`'s proof with the family
  abstracted**, and it holds for ANY natural family on relative points — no curve, no
  base, no genus hypothesis. If a leaf takes `(c, hnat)`, it can take a morphism
  instead, and the conversion is six lines. Grep the file for `aj_val` and copy it.
* **Verify a giant-file recut in a scratch that `public import`s the module and
  restates everything with primed names.** Measured here: **7 s per round** against a
  full `lake build` of `X0.lean`; the ~350 lines transplanted into the real file
  unchanged and built first try. Nail the namespace first with a two-line `#check`
  scratch — X0's declarations are `Fermat.*` and the scope at the target was
  `section AlbaneseDescent` with `open CategoryTheory AlgebraicGeometry` plus
  `open _root_.CategoryTheory.Limits`.
