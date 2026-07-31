---
name: flt-identification-pinned-geometrically-not-modularly
description: A datum's fibre identification can be pinned by geometry (an open immersion) and by nothing modular, which silently blocks every leaf that has to compose a moduli pin across the two fibres
metadata:
  type: project
---

`IsX0JNeronDatum` (X0.lean) carries `genY : RelPoint strY g ≃ RelPoint ystr g₀`
identifying `Y_0(N)_ℚ` with the generic fibre of the integral model. Every field
pinning it is GEOMETRIC — `genX_j` ties it to `genX` through the open immersion
into `X`, and `genX` is tied to nothing modular. So post-composing `genY` and
`genX` with one automorphism of `X` preserving `Y` (`w_N` itself will do)
satisfies **every** field while permuting which moduli point is which.

**Why:** the consequence is not "the datum is slightly weak". It is that any leaf
whose statement composes a pin taken on the `ℚ` side (`hc.classify`) with a
construction on the integral side (`model.coarse.universal`) is UNPROVABLE from
the datum — the two agree only up to an unknown endomorphism `u` of `Y`, and the
conclusion typically demands `u = 𝟙`. `exists_extend_atkinLehnerModel_of_jNeronDatum`
died on exactly this (2026-07-31): its third conclusion clause is the statement
that the discrepancy is trivial. No frontier instrument shows this — the leaf
looks like an ordinary open node with a plausible docstring.

**How to apply:** when a leaf has to move a pin between two fibres of one model,
first ask what pins the IDENTIFICATION, field by field. If the answer is only
"an open immersion" or "an isomorphism of schemes", the moduli/arithmetic
compatibility is missing and must be added as a FIELD, not stated as a leaf over
the datum — a leaf over the datum would be FALSE, since the twist is a witness.
Charge the field to the theorem that CHOOSES the model (here
`exists_x0CurveModel_of_base_moduli`), never to one that takes it as given:
X0.lean had already performed this exact repair for `(ι, hι)` on 2026-07-27 and
for `hgi`, both times recording "an automorphism twist of `X` that the hypotheses
could not see". Check for the discarded evidence before writing a new leaf —
`exists_iso_of_isCoarseModuliY0` already PROVES the classify comparison in its
body (`hu₂`) and throws it away, and `genericFibreClassify` is *definitionally*
the integral `classify`, so the repair is bookkeeping rather than mathematics.
See [[flt-cut-leftovers-close-sibling-leaves]].
