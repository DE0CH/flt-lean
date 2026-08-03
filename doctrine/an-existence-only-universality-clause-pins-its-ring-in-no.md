## AN EXISTENCE-ONLY UNIVERSALITY CLAUSE PINS ITS RING IN **NO** DIRECTION — AND THE AUDIT THAT FOUND THAT ONCE DOES NOT TRANSFER ITSELF

(2026-07-31, `Patching.lean`.) `IsWeaklyUniversalDeformation` is deliberately the
existence half only, and a 2026-07-28 audit refuted `exists_auxDeformationDiamondControl`
with the family `Runiv₀[[y_1, …, y_m]]`: a classifying map out of `Runiv₀` precomposed with
`constantCoeff` classifies just as well, so weak universality admits arbitrarily large
`Runiv` and any conclusion bounding it from ABOVE is false. That audit was written, the
repair (`hgen`, trace generation) was threaded through eight declarations, and everyone
moved on.

**`AuxDeformationDatum.IsWeaklyUniversal` is the SAME clause on a DIFFERENT ring**, and its
docstring says so in as many words — and both ring leaves take that datum as a hypothesis
and conclude something bounding `𝒟Q.R` from above. The identical family refutes both.
Nobody looked, because the leaf already carried a FALSITY AUDIT (about the `𝒪`-algebra
structure, repaired by `hcohen`) and a leaf that has been audited reads as a leaf that has
been checked.

So: **when an audit refutes a leaf because some bundled object is unpinned, grep for every
OTHER object in the same file with the same defining shape** — here, one `grep -n 'Only the
EXISTENCE half is asked'` would have found it. An audit is scoped to the object it names,
never to the pattern.

Corollary on where such a defect must be repaired: the conclusion is a statement about the
object, so **the leaf must PRODUCE the object, not receive it** (this file's own principle,
"a datum handed across a seam can only be constrained by what already saw it"). Three
cheaper repairs were checked and all fail — a hypothesis naming the received datum is
UNDISCHARGEABLE when the consumer chooses it internally; the universally-quantified form
(`∀ 𝒟, weakly universal → generated`) is refuted by the same witness and makes the package
vacuous; and a new leaf producing a "weakly universal AND trace-generated" datum is FALSE
as stated, because trace generation over `ℤ_[p]` forces the residue field to be the trace
field and nothing pins `k` to it (`ρbar` absolutely irreducible over `𝔽_p`, `k = 𝔽_{p²}`).

