## AN AUDIT THAT FORBIDS *RECEIVING* AN OBJECT IS ABOUT WHO CHOOSES IT — AND THE CLAUSE IT FEARS MAY ALREADY BE A PROVEN `∀`-THEOREM
(2026-08-01, `flt-lean-285`, `HilbertModularity.lean`.) A mature leaf here often carries a
CONTROL-MAP-style audit of the shape *"object `X` must be PRODUCED by this leaf, never
RECEIVED: its specification is a bare `∃` that admits a FAMILY, so a received `X` would make
the leaf assert `P X` for every member of it — an unvouched generalisation."* Those audits
are usually CORRECT, and they read as a prohibition on the SHAPE. They are not. They are a
statement about the STRENGTHENING that receiving `X` incurs — and the strengthening may
already be discharged, in which case receiving `X` costs exactly nothing.
`exists_hilbertAuxHeckeDiamondModuleData` had such an audit against receiving the control
map `toRuniv`, correct in every clause. But the two conclusions that quantifying over
`toRuniv` would strengthen — `ker toRuniv = 𝔫.map diamond` and `𝔟_ex ≤ ker diamond` — are
**the exact conclusion of `exists_hilbertAuxDiamondQuotient_of_exponents`, which is PROVEN
and is itself stated for an ARBITRARY `toRuniv` carrying the same specification.** So the
`∀`-form is already a theorem in the tree, the sub-leaf that receives `toRuniv` gets both
clauses in ONE LINE, and the residual is strictly smaller.
**The check is one `exact` in a scratch module and it takes ten seconds:** state the feared
clause with the object RECEIVED, and try to close it from the candidate theorem. If it
elaborates, the audit's objection is discharged rather than incurred — say so in the
docstring, quote the application, and note it was machine-checked. If it does not, the audit
stands and the object must be produced.
Three riders, each of which cost something here:
* **`topologicalClosure = ⊤` DOES NOT PIN A BARE `RingHom`.** The audit itself suggested its
  objection would be repaired by a trace-generation hypothesis ("it would, if the charpoly
  coefficients topologically generated `𝒟Q.R`"). That is FALSE as stated: the equaliser of
  two ring homs is a subring, and it is CLOSED only if both maps are continuous — and
  `𝒟Q.R →+* 𝒟.R` carries no continuity anywhere in this development. Whenever an audit says
  a density/generation hypothesis would pin a map, check whether the map is continuous
  before believing it; here `IsTraceGenerated` earns its place for a different reason (it is
  what the proven theorem above needs), and saying so in the docstring is what stops the next
  reader re-deriving the wrong justification.
* **A "produce it, don't receive it" audit does not forbid PASSING IT DOWN FROM GLUE.** The
  repair that satisfies it exactly is: let the CONSUMER choose the object and hand it to the
  sub-leaf as a hypothesis. The sub-leaf then never quantifies over the family — the
  requirement is met by construction rather than by existential packaging — and the item the
  audit called "not arithmetic and three copyable lines" is genuinely deleted from the leaf.
* **The hypothesis the cut needs is often already OBTAINED at the top of the chain.**
  CLAUDE.md's rule is to grep the top before threading anything up; here it paid off in the
  positive direction — `exists_hilbertTaylorWilesAuxLevelData` already did
  `obtain ⟨𝒟Q, h𝒟Q, h𝒟Qt⟩` and already passed `h𝒟Qt` to the RING half, so adding it to the
  HECKE half was one argument at two call sites and no producer anywhere pays for it.
**And do NOT let the same reasoning talk you into receiving the OTHER object.** The same file
refutes receiving `diamond` (§5: a `diamond` killing every variable satisfies both clauses
whenever `ker toRuniv = 0`, while the coordinate clause forces `ker diamond ≤ 𝔟_ex`), and no
proven `∀`-theorem discharges that one. The test is per-object, not per-shape: for each
object you propose to receive, name the theorem that already proves the strengthened clause,
or keep it produced.
Accounting, in the shape the RECUT rule asks for: **1 → 1, and the receipt is
`git diff HEAD -- <file> | grep -E '^[+-] *sorry *$'` showing exactly one `-` and one `+`.**
What got smaller is the leaf, not the count.
