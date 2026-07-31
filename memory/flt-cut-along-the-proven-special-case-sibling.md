---
name: flt-cut-along-the-proven-special-case-sibling
description: When a leaf has a PROVEN special-case sibling, cut it along that sibling's signature — the glue is a copy of the sibling's glue and verifies in seconds
metadata:
  type: feedback
---

A leaf stated over one of this project's bundled predicates (`weilValueProp`,
`IsWeilValue`, `IsEichlerShimuraTransform`, …) usually has its whole
mathematical content at a lower, **configuration** level, and very often that
configuration-level statement **already exists in the file, proven, in a special
case**. Cut the leaf along that existing signature.

`weilValueProp_self_of_even_of_ne_two` (alternation of the Weil pairing at even
level `> 2`) was cut this way on 2026-07-31. Sixty lines above it sat
`weilValue_two_torsion_config_eq_one`: the same configuration, the same engine
hypotheses, the same value equation, with `p = 2` hardcoded and the `2`-torsion
input `⊖P = P` as an extra hypothesis — **PROVEN**. Copying that signature with
`2 ↦ p` and `⊖P = P ↦ (p : ℤ) • P = 0` gives the general leaf, and the glue
(destructure the setup out of `hz`, read four abscissa avoidances off the
`F`/`F'` memberships, apply) is a **line-for-line copy of the proven sibling's
glue**.

**Why:** the glue is where a cut usually fails, and here it is already written
and already known to elaborate. The residue lands stated over an arbitrary
field with none of the project's wrapper vocabulary (no `ZMod q`, no `nTorsion`
subtype, no Frobenius, no uniqueness hypothesis), i.e. dispatchable to someone
holding only the textbook. And the general statement subsumes the sibling, which
is the tell that you cut in the right place.

**How to apply:**
* Before attacking a leaf, grep the file for a declaration whose conclusion has
  the same *shape* at a special parameter value — `_of_two`, `_of_prime`,
  `_levelOne`, `_specQ`. Read its signature, not its docstring.
* Copy that signature verbatim and generalize the parameter. Keep every
  hypothesis the caller can supply, even ones you cannot justify — they cost the
  prover nothing and cannot make the leaf false. Mark in the docstring which are
  defensive and which are load-bearing.
* **Do NOT reroute the proven sibling through the new sorried leaf.** It would
  enlarge the sorried cone for zero frontier gain.
* Verify the whole cut in a scratch module that `public import`s the *unedited*
  target: restate both blocks under primed names, and check the glue theorem
  emits **no** `declaration uses 'sorry'`. 34 s against ~25 min for a build of an
  80k-line module — see [[flt-see-the-merge-before-the-merger]] for the sibling
  discipline of checking things cheaply before paying for them.

Count is unchanged (1 leaf → 1 leaf); judge it by what is LEFT in the leaf.
