---
name: modularity-subtree-approved
description: "Deyao 2026-07-23 — the modularity/eigenform vocabulary subtree is APPROVED as a build: top-down from the three deferred Family.lean atoms, scale (23k+ lines) explicitly accepted, ~/cs/FLT as structural reference, textbooks via Anna's Archive"
metadata:
  node_type: memory
  type: project
---

Deyao (2026-07-23): "build the subtree. i know it's a large scale work,
but build it correctly, as in still top down, if it takes 23k lines and
more then it's fine. also the reference might be useful to still look
at and do something similar. reference textbooks if you need to,
download them using anna's archive."

**Scope:** the missing modular-forms machinery (Hecke operators on the
pin's analytic modular forms → eigenforms/eigensystems → the attached
Galois representation → its local properties at ℓ and at 2), built to
discharge the three deferred automorphy statements in
`Fermat/FLT/GaloisRepresentation/HardlyRamified/Family.lean`:
`exists_hardlyRamified_ringOfIntegers_realizations`,
`exists_realization_at_two_generated`, and
`exists_finiteDimensional_trace_field_of_isIrreducible`.

**Method constraint (Deyao's words: "correctly, as in still top
down"):** the FIRST deliverable is the interface layer — carrier
definitions as real code plus sorried attachment/property theorems,
with the three atoms rewritten as PROVEN assemblies consuming them —
committed before any bottom-up theory. Decomposition proceeds downward
from there, leaf by leaf, under the normal fleet loop. ~/cs/FLT is a
structural reference (read-only, unvendorable — its interface closure
contains load-bearing sorries); Diamond–Shurman is the primary
textbook, fetched via the Anna's Archive MCP per CLAUDE.md's PDF
workflow.
