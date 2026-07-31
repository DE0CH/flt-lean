---
name: flt-every-vs-some-representing-object
description: A leaf saying "every object representing F has property P" cannot cite the literature, which only constructs one; prove uniqueness-up-to-iso and move P into the existence leaf
metadata:
  type: project
---

In `RelativePicard.lean` (2026-07-31) `smooth_of_isRelPicOf` and
`isSeparated_of_isRelPicOf` were stated as *every* `pstr` carrying
`IsRelPicOf strX pstr` is smooth / separated. Both read as research-scale.
Neither was: BLR 8.2/1 and 8.4/2 **construct** `Pic_{X/S}` and read the
properties off the construction, so the "every" shape has no citation to
follow.

**Why:** the bridge from "some" to "every" is a uniqueness lemma that is pure
Yoneda on the points type (`RelPoint`), provable from `surj` + `inj` +
`sheaf_pre` alone — `cmp`, `cmp_cmp`, `cmp_pre`, `toHom`,
`toHom_comp_toHom`, `isoOver`. ~60 lines, no geometry, compiled first try.
With it, `rw [← toHom_comp]; infer_instance` transports any
isomorphism-invariant property.

**How to apply:** before attacking a leaf whose only contentful hypothesis is
a representability structure (`IsRelPicOf`, `IsJacobianOf`, `IsAlbaneseOf`,
`AbelianSchemeStruct`, `IsRelPicZeroOf`), check whether its citation is about
all objects of a class or one constructed object. If they differ, prove the
uniqueness lemma and thread the property into the **conclusion of the existing
existence leaf** rather than opening a new one — the obligation lands on
whoever builds the scheme, who has it in hand anyway, and no leaf is created
(frontier went 9 → 7 here). Threading a clause is a RESTATEMENT, so re-run the
faithfulness audit against the composite; and if the existence theorem needs a
hypothesis the leaf lacks (here a section `o`), check the consumer can supply
it before adding it. See [[flt-two-leaves-may-be-one]] and
[[audit-searched-production-not-invariant]].
