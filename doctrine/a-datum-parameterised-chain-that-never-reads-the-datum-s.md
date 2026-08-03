## A DATUM-PARAMETERISED CHAIN THAT NEVER READS THE DATUM'S DEFINING FIELD IS A REFACTOR, NOT A REBUILD

(2026-08-02, `flt-lean-327`, `HardlyRamified/HilbertModularity.lean`.) This
development states long chains of theorems over a bundled `structure` — a
deformation datum, a moduli datum, a place system. When a SECOND structure
appears that differs from the first in one field (here `HilbertDeformationDatum`
against `HilbertAuxDeformationDatum`, differing only in `isHilbertHardlyRamified`
versus `isHilbertRaisedLevelHardlyRamified`), the whole chain becomes unavailable
at the second level, and the leaf that needs it there reads as a full-scale
transcription job.

**Measure what the chain actually consumes before pricing it.** One command:

    grep -o "𝒟\.[A-Za-z_']*" <the extracted chain> | sort | uniq -c

Here the six-link Carayol descent (533 lines) used `𝒟.R`, `𝒟.ρ`, `𝒟.π`,
`𝒟.π_surjective`, `𝒟.isAdic`, `𝒟.isAdicComplete`, `𝒟.resid` — and
`𝒟.isHilbertHardlyRamified` **exactly once**, through its `det` clause, which
the two structures share verbatim. So the chain was level-blind all along and
blocked only by its binder type.

**The refactor that costs nothing: a third structure with THE SAME FIELD NAMES.**
`HilbertCoeffDatum` holds the shared fields; the six proof bodies then transcribe
with **no character changed inside them**, because `𝒟.R`, `𝒟.resid`, … still
parse. The six original names become one-line wrappers `… 𝒟.toCoeff …`, so no
call site anywhere changes and the diff is auditable: the six STATEMENTS are
byte-identical to before. Verified in a scratch module in ~16 s per round before
a single line of the real file was touched.

Two mechanical points, both of which cost a round:

* **Make the `toCoeff` projections `@[reducible]`.** Without it,
  `𝒟.toCoeff.R` and `𝒟.R` are `rfl`-equal and not syntactically equal, and
  instance search does not cross that: every use site fails with
  `failed to synthesize Module ↥(hilbertTraceSubring ℓ 𝒟.ρ) 𝒟.toCoeff.R`, for a
  module structure that is visibly present.
* **Ascribe the type of the `obtain`** that consumes the generic theorem, so that
  everything downstream of it is phrased in the CONSUMER's vocabulary rather than
  in `𝒟.toCoeff`'s. `obtain ⟨ρ', e, he⟩ : <the statement you want> := <the generic
  theorem>` typechecks by defeq and removes the problem at the source; without it
  the failure reappears at every later step, including as a `rw` that cannot find
  a pattern it is displaying.

**And the reason to look for this at all: a leaf whose docstring says it is "the
exact twin" of a PROVEN theorem elsewhere is telling you the mathematics is done
and something bureaucratic is in the way.** Ask what the proven theorem's binder
list demands that your setting cannot supply, and check whether its PROOF demands
it too. Here it did not, and the answer was a structure, not a subtree.

### The sibling check: a helper's `[Finite]`/`[IsAdicComplete]` may be the whole leaf

Same task, and it is where the residue actually sits. The finite-level analogue
of the one genuinely new clause was PROVEN, and every tool in its proof is stated
for an ARBITRARY topological commutative ring — except one, which asks for
`[IsAdicComplete (IsLocalRing.maximalIdeal C) C]`, free there only because `C` is
FINITE. **Trace that instance to its single use.** In
`exists_frobEigenBasis_of_charFrob_map_eq` it enters through exactly one call to
`exists_matrix_eigenBasis_of_charpoly_map_eq`, whose own use of it is one
`HenselianRing.is_henselian` lifting a simple residual root. Everything after is
completeness-free.

So a leaf that reads as "descend this whole local condition" is really
*"Hensel for a closed subring"* — and in this development that is provable rather
than assumable, because `isUnit_of_isClosed_subring_of_notMem_maximalIdeal` makes
the Newton derivative a unit of the subring and a topological closure is closed.
**Do the instance-tracing before writing the leaf's docstring**; it is the
difference between a residue somebody can pick up and a residue that reads as a
chapter.

**A caution that applies to the whole family: do NOT assume the missing instance.**
`IsAdicComplete` for the trace subring is Carayol's Lemme 1, which this file
DERIVES from the conclusion of the very cluster the leaf sits in. Adding it as a
hypothesis makes the leaf unusable by its only consumer, silently — the consumer
supplies its arguments in the other order. Check the consumer's order before
strengthening a leaf's hypotheses.

