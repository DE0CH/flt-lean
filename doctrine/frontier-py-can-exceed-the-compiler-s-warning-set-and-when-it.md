## `frontier.py` CAN EXCEED THE COMPILER'S WARNING SET, AND WHEN IT DOES THAT IS THE FOURTH INVISIBILITY CLASS

(Same release.)  The standing validation for the frontier scan is that it agrees
with the build's `declaration uses 'sorry'` warning set.  At release 33 it did
not: **380 rows against 377 warnings**, and the discrepancy is not a scanner bug
and must not be "fixed".

All three extra rows are in
`Fermat/FLT/Mathlib/AlgebraicGeometry/CurveDivisorDegree.lean`, the ONE module
under `Fermat/` that is not in `Fermat.lean`'s import closure (401 of 402).  It
is never compiled, so it emits no warnings — and its three `sorry`s are
perfectly real.  A scan that agreed with the compiler here would be UNDER-
reporting the frontier by exactly the leaves nobody can see.

So the validation to run is the two-directional one, and read the two directions
differently:

* **in the warning set but not in the scan** — a scanner bug, always;
* **in the scan but not in the warning set** — check the file against the import
  closure BEFORE touching the scanner.  If the module is unreachable, the scan
  is right and the module is the defect.

