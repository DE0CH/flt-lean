---
name: flt-claude-md-fix-does-not-fix-the-docstring
description: "Correcting a refuted audit in CLAUDE.md does not correct the leaf's docstring, and task prompts are generated from the docstring — so the refuted claim gets re-issued as an instruction."
metadata: 
  node_type: memory
  type: project
  originSessionId: a3062ac7-79d1-4077-a9ad-6353cb70a69d
  modified: 2026-08-01T15:21:58.528Z
---

(2026-08-01, `flt-lean-142`, `exists_inertiaSet_geomPt` in `ModularCurve/X0.lean`.)

CLAUDE.md already carried a section refuting **this leaf's sibling's** MISSING
MACHINERY audit by name, saying the audit greps `Modularity/{AbelianScheme,
AbelianSchemeIsogeny}.lean` and misses `Fermat/FLT/Mathlib/AlgebraicGeometry/
NeronModel.lean`. That correction landed in CLAUDE.md and **the docstring was
never edited**. The loop generates task prompts FROM the docstring, so the
refuted paragraph was handed to me verbatim as the premise of the task.

**Why:** an audit lives in two places — the leaf's docstring (which the task
generator reads) and CLAUDE.md (which agents read at session start). Only the
first is upstream of dispatch.

**How to apply:** when you refute or correct an audit, edit the DOCSTRING in
place as well as CLAUDE.md. Conversely, when a task prompt hands you an
absence claim, check CLAUDE.md for an existing refutation of it before
believing it — the correction may already exist and simply not have reached
the leaf.

**Third failure of the same audit, worth its own check:** the machinery was in
the SAME FILE, ~20k–56k lines BELOW the leaf (`HasGoodAbelianModelAtBase`,
`SpecLoc`, `IsFibreIdent`, `exists_isReductionBase`). "Absent" and "declared
below me" give identical evidence from every tool except comparing line
numbers — and a scratch module `#check` SUCCEEDS in both cases, since a scratch
imports the whole file and sees every declaration regardless of order. So:
`grep -n` the concept in your own file and compare the line number with your
leaf's. See [[flt-leaf-blocked-by-declaration-order]] and
[[flt-inventory-audits-understate-what-exists]].

Deciding the repair was two commands: `./flt-hoistcheck.py --block A B --to L`
per block (4 blocks, ~170 lines, HITS 0), then
`python3 tools/merge/blockmove.py <file> A:B:L ...`, which applies several
moves in ORIGINAL coordinates and refuses to write unless the sorted line
multiset is unchanged. See [[flt-pure-move-receipt]].
