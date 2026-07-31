---
name: flt-relocation-collides-with-a-third-file
description: Moving a block between two files also renames it into a new namespace, where it can collide with a declaration in a THIRD file neither one imports
metadata:
  type: project
---

Relocating a block from `Modularity/Interface.lean` (namespace
`GaloisRepresentation.Modularity`) up into `ModularCurve/X0.lean` (namespace
`Fermat`) renames all 89 of its declarations. One of them, `residueFieldAlgebra`,
already existed as `Fermat.residueFieldAlgebra` — in
`Fermat/FLT/Mathlib/AlgebraicGeometry/CurveDimension.lean`, a **third** file that
neither the source nor the destination imports.

**Why:** the collision is not visible anywhere you would naturally look. A
block-vs-source-file scan is clean (the block never used it). A block-vs-
destination-file scan is clean (`X0.lean` does not import `CurveDimension`). Both
files compile. The error appears only in a *consumer* that imports both cones —
here `Interface.lean` itself, via `MazurTorsion` — as an "already declared" at
import time, i.e. in a module nobody was editing.

**How to apply:** before a namespace-changing move, grep the WHOLE tree for every
relocated declaration name — `grep -rlE "(^|[^A-Za-z0-9_.])<name>([^A-Za-z0-9_]|$)"`
over `Fermat/`, one pass per name — not just the two files involved. Match on the
FULL name and anchor both sides; matching on the last dotted component drowns you
in `.mul`/`.one`/`.pow` noise. Then rename the loser and say so in the docstring,
because the two statements are usually genuinely different and a reader will
otherwise assume one is a duplicate of the other. See
[[flt-verify-a-relocation-in-a-destination-scratch]] for the 10-second check that
confirms the rename landed, and [[mathlib-states-lemmas-twice]] for the sibling
trap where the twin is the one you want.
