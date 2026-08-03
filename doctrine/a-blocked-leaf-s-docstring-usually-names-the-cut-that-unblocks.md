## A BLOCKED LEAF'S DOCSTRING USUALLY NAMES THE CUT THAT UNBLOCKS THE *GLUE* — take it

(2026-07-31, `flt-lean-205`, on `smoothLocus_pairSquareMap_le` in `X0.lean`.)

That leaf carried a careful pin audit ending "a worker sent here should expect to build a
theory", and the audit was RIGHT: the mathematics it needs is descent of formal smoothness
along a faithfully flat map, which mathlib records as an open `proof_wanted`
(`Algebra.FormallySmooth.of_formallySmooth_tensorProduct_of_faithfullyFlat`, needing
Raynaud–Gruson, Stacks `058B`). Re-checking the pin confirmed all three routes are absent —
the scheme-level `DescendsAlong @Smooth …` descends along a base change of the TARGET and not
of the SOURCE; the `Algebra.IsSmoothAt.of_formallySmooth_fiber` route reduces to formal
smoothness of a fibre over a field, and the only such statement in the pin
(`Algebra.FormallySmooth.of_perfectField`) is about a field EXTENSION, so even
characteristic zero does not shortcut it.

**But the same docstring's last paragraph named, in one sentence, the general lemma that
would discharge everything else** — "prove `p` flat, `x ∈ (p ≫ g).smoothLocus` ⟹
`p x ∈ f.smoothLocus` once, and `⊆` follows". Cutting exactly that out took two compiles and
about forty lines, and the leaf became PROVEN. The frontier count is unchanged (−1 here, +1
there) and that is not the point:

- the residual leaf is now **mathlib-shaped and reusable** — it is Stacks `02VL` at one point,
  stated for arbitrary schemes, and it will be discharged by a mathlib bump or by one
  ring-theory worker, whereas the old leaf could only be discharged by someone who also
  understood `pairSquareMap`;
- the **project-specific glue is gone for good**. Composition of `FormallySmooth` stalk maps,
  which projection is smooth and which is flat, the instance juggling for base changes of
  `Smooth af` — none of that was mathematics, all of it was work, and none of it has to be
  redone by whoever proves the real theorem;
- the audit stops being re-derived. It moved WITH the leaf, so the next owner reads it where
  the sorry is, not two files away.

**So the standing move on a "needs new theory" leaf is: before concluding it is a cost wall,
read its own docstring for the reduction it proposes, and if it proposes one, TAKE it.** A
leaf whose author bothered to write "the cheapest honest reduction is X" has done the design
work already; leaving X uncut wastes it, and every later owner pays the glue again.

Two smaller things from the same task, both measured:

- **Land the cut in an EXISTING mathlib-facing project module if one is already publicly
  imported by the target.** `Fermat/FLT/Mathlib/AlgebraicGeometry/Morphisms/SmoothLocusPerfect.lean`
  is 122 lines, imports only `Morphisms/{Smooth,Flat,FinitePresentation}`, and `X0.lean`
  already `public import`s it. So the cut cost ZERO new imports, zero import-position risk,
  and the helper elaborates in seconds instead of inside an 81 000-line file.
- **To test an edit to a giant file, MOCK the giant file's definitions as opaque variables.**
  The X0 proof was verified before touching X0 by a scratch importing only the helper module,
  in which `pairSquareMap u hu` was replaced by a variable `F : pullback af af ⟶ pullback bf bf`
  and `pairSquareMap_fst/_snd` by two hypotheses of the same shape. That checks the only things
  that can actually fail — instance resolution for the base changes, and whether the general
  lemma's implicit arguments match — in ~30 s rather than in a full rebuild. It is the
  "stub the siblings" trick applied to the target's own DEFINITIONS rather than to its
  neighbours. (It still proves nothing about the target's import surface or token scope; do
  the one real build.)

