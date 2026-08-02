---
name: flt-docstring-prescribes-the-rival-cut
description: "A dead leaf's docstring can name the live rival cut's construction verbatim; grep the CONSTRUCTION, not the leaf's vocabulary."
metadata: 
  node_type: memory
  type: project
  originSessionId: 32363faf-5755-490d-9f9c-20fb7f5891f4
  modified: 2026-08-02T16:47:38.871Z
---

(2026-08-02, `flt-lean-34`, `exists_valuationSubring_arithFrob_of_heightOneSpectrum`
in `Modularity/TateModule.lean`.)

One node, cut twice a day apart, both kept by a merge, **in the same file 300
lines apart**. Cut A (`ValuationSubring`/`gV`/`hcentre`, two leaves) is DEAD —
its assembly `exists_localRing_arithFrob_of_heightOneSpectrum` has zero
consumers. Cut B (`placeAbove`/`frobRestrict`, one leaf
`exists_residueHom_placeAbove`) is LIVE via
`exists_finset_abelianReductionDatum_of_mult`.

**No existing scan sees this.** The two cuts share no identifier, so name-based
`xdup.py`/`check-dup` are silent; and they are not alpha-variants but different
PACKAGINGS (existential over an abstract `V` vs over a named `def`), so
`dupstmt.py` is silent too. Every frontier scan counted two honest leaves and
`own.py` correctly said "unowned, open". The cluster drew THREE dispatches; two
were at dead leaves.

**The tell: the dead leaf's docstring PRESCRIBES the live cut's construction by
name** — "put `V := L ⁻¹' (localValuationSubring w)`", which is verbatim
`placeAbove`'s body, plus a "VERIFIED STARTING POINT" fragment that is that
`def`. The author wrote the paragraph, built it 450 lines earlier as a rival
cut, and never closed the leaf.

**So: when a docstring tells you what to construct, grep the file for that
CONSTRUCTION before constructing it** — grep `comap`, `localValuationSubring`,
the defining expression; never the leaf's own vocabulary, which the rival by
construction does not share. One `grep -n` found it.

Resolution follows [[flt-close-duplicate-cut-by-renaming-winner]]: Cut B wins
(one leaf vs two; its leaf is about one explicit ring where Cut A's quantifies
over an arbitrary one). **Close your own by delegation, do not delete the
sibling** — 8 lines over the winner's leaf, adding no `sorryAx` edge since that
leaf is already in the cone. The proof is the RECEIPT that makes the later
deletion safe. And check declaration order before "tidying": re-pointing the
dead assembly at the live one was illegal here, the live assembly being declared
200 lines below it.

Related: [[flt-consumerless-leaf-is-dead-or-duplicate]],
[[flt-both-rival-cuts-landed]], [[flt-two-leaves-may-be-one]].
