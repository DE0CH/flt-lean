## AN "IRREDUCIBLE" VERDICT SEARCHES FOR A PROOF. CHECK FIRST WHETHER A SIBLING LEAF ALREADY IS ONE.

(2026-07-31.) `birationalOver_affineLine_of_not_injective_aj` carried a dated,
twice-re-run, entirely correct irreducibility audit: Riemann–Roch for curves does
not exist in `Mathlib`, in `~/cs/FLT`, or in `Fermat/` — no `h⁰`, no genus, no
degree of a divisor, and the re-run on 2026-07-28 named the exact greps. Every
word of it was true, and the leaf was **one `exact` away from proven**.

The audit asked *how would I PROVE this*. What it never asked is *does this file
already STATE it*. Eleven hundred lines below, in the same file, sat
`birationalOver_affineLine_of_relPicEquiv_sectionIdeal` — "two distinct linearly
equivalent `K`-points force the fibre to be rational" — the same classical
theorem written in Picard language instead of Albanese language. The two leaves
were carrying **one** theorem twice, and the bridge between them was three lines
of `RelPicEquiv` algebra plus `IsJacobianOf.universal`.

Why the duplication is invisible to every check this file already prescribes:
the two statements share **no identifier**. One mentions `IsJacobianOf`, `aj`
and an `AbelianSchemeStruct`; the other mentions `RelPicEquiv`, `sectionIdeal`
and `curveBaseChangeProj`. A grep for either name finds nothing of the other,
`own.py` and `leafstat.py` both correctly report "unowned, still open", and the
frontier scan counts two leaves because there are two `sorry`s. Only the
DOCSTRINGS gave it away — both say "Riemann–Roch in degree 1" in prose.

So add this to a leaf's audit, before writing "IRREDUCIBLE":

**Grep the file's own docstrings for the NAME OF THE THEOREM you are about to
declare missing** — `RiemannRoch`, `Poincaré`, `Lüroth`, `autoduality` — not for
its identifiers. If another leaf's prose claims the same classical citation,
either one implies the other or the two should be merged; either way the second
`sorry` is not a second obligation. In this instance the payoff was −1 leaf, the
consolidated Riemann–Roch content in one statement, and a stale "IRREDUCIBLE"
retired.

Corollary, and it is the general shape: **a decomposition that lands in a
DIFFERENT vocabulary from an existing leaf will re-derive that leaf rather than
reuse it.** The Picard leaf was cut on 2026-07-28 and the Albanese one on
2026-07-27, one day apart, by owners who could not see each other. When you cut a
node, say in the docstring which classical theorem the pieces are, in words —
that sentence is the only thing that will match.

