## "THE OTHER SIDE DOES NOT HAVE THIS PROBLEM" MUST NAME THE **OBJECT** IT PROTECTS
(2026-07-31, the Hilbert twin of the `Patching.lean` `𝒟Q` refutation. This is a *different*
failure from "an audit is scoped to the object it names, never to the pattern" — that one is
about not looking; this one is about looking, finding a note, and being told the wrong thing.)
`Patching.lean`'s 2026-07-28 audit refuted a leaf because `IsWeaklyUniversalDeformation` is
existence-only and so pins `Runiv` in no direction. It then wrote, as an aside:
> The Hilbert twin does not have this problem because
> `exists_hilbertAuxDeformationRingPresentation` carries `h𝒟t : 𝒟.IsTraceGenerated`
> alongside `h𝒟w`, and trace generation is exactly what excludes `y`.
**Every clause of that is TRUE — about `𝒟`, the BASE-level datum.** That Hilbert theorem
*also* received `𝒟Q`, the RAISED-level one, under nothing but
`HilbertAuxDeformationDatum.IsWeaklyUniversal` — the same existence-only clause, on a ring
the sentence never mentions. So the Hilbert side had the identical defect, on the other ring,
for three days, PROTECTED BY A CORRECT NOTE. Anyone who checked found the note, read "the
Hilbert twin does not have this problem", and stopped.
A theorem's hypotheses routinely mention several bundled objects of the same kind. A
protection note that names the theorem and the hypothesis but not **which object of that
theorem is thereby pinned** is unfalsifiable by the reader who most needs it. So:
- **Writing one**: name the ring/module/datum. "`𝒟` is pinned by `h𝒟t`; `𝒟Q` is NOT pinned by
  anything" is one clause longer and would have prevented this.
- **Reading one**: before accepting "X does not have this problem", list the objects in X's
  hypotheses of the shape the defect attacks, and check the note covers each. Here that is
  `grep -n 'IsWeaklyUniversal' <the theorem>` — two hits, one covered, one not.
Same shape as "TWO INDIVIDUALLY-CORRECT REPAIRS CAN BE FATAL TOGETHER" above: a true
statement that is *scoped narrower than it reads* is more dangerous than a false one, because
it survives review.
