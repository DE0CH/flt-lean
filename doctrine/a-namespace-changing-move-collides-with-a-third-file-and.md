## A NAMESPACE-CHANGING MOVE COLLIDES WITH A THIRD FILE, AND NOTHING YOU EDIT SHOWS IT

(2026-07-31, `flt-lean-376`, relocating the zeta chain out of `Modularity/Interface.lean`
and up into `ModularCurve/X0.lean`.)

A cross-file relocation is never only a move: the two files are in different namespaces —
here `GaloisRepresentation.Modularity` and `Fermat` — so the block's 89 declarations are
all **renamed**. One of them, `residueFieldAlgebra`, already existed as
`Fermat.residueFieldAlgebra`, in `Fermat/FLT/Mathlib/AlgebraicGeometry/CurveDimension.lean`
— **a third file that neither the source nor the destination imports.**

Every check you would naturally run is clean:

* block against the SOURCE file — clean, the block never used the name;
* block against the DESTINATION file — clean, `X0.lean` does not import `CurveDimension`;
* both files compile, separately and completely.

The error surfaces only in a **consumer of both cones** — here `Interface.lean` itself,
which reaches `CurveDimension` through `MazurTorsion` — as an already-declared at IMPORT
time, in a module nobody was editing, about a name nobody moved. It is the same shape as
the class-4 unreachable-module trap: a defect that exists only in an environment no single
file's source describes.

**So the pre-flight for a relocation is a WHOLE-TREE scan of every relocated name**, not a
two-file one:

    grep -rlE "(^|[^A-Za-z0-9_.])<name>([^A-Za-z0-9_]|$)" --include=*.lean Fermat/

one pass per declaration, matching the FULL name with both sides anchored. Matching on the
last dotted component instead drowns the result — `EulerLowOne.mul`, `.one`, `.pow`,
`.prod` matched 40 files apiece and hid the one real hit. 89 names, one real collision.

Rename the loser rather than merging the two: they are usually different statements (this
one carries no `Field` instance where the incumbent requires one), and a docstring line
saying which is which is what stops the next reader from "deduplicating" them.

**The verification that makes this cheap is a scratch carrying the DESTINATION's own
imports.** Copy `X0.lean`'s `module` / `public import` / `@[expose] public section` /
`universe` / `open` / `namespace` preamble verbatim, paste the block, and
`lake env lean` it: **10 seconds**, against 310 s for a real `lake build` of X0 and far
more for `Interface.lean`. This is not the "clean scratch proves nothing" case the
doctrine warns about — that is about a scratch declaring its own convenient imports. A
scratch declaring the DESTINATION's imports is exactly as strict as the destination, so
green really does mean the block compiles there; it settled "does `X0` need any of the 84
Mathlib modules `Interface.lean` has and it does not?" (no) with zero rebuilds. Include
X0's NON-public imports too — they are visible in its body and not to an importer — and
import the suspected third file, which is how the collision above shows up in seconds.
