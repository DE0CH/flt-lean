---
name: flt-image-for-quotient-has-two-tests
description: The image-for-quotient substitution only applies when the divided-out subobject is positive-dimensional and the conclusion wants maps only OUT of the ambient
metadata:
  type: project
---

The move that closed `exists_involutionSignSplitting` — replace a docstring's
expensive QUOTIENT by an IMAGE already in the file — has exactly three
preconditions, and a sweep of the 13 remaining `X0.lean` leaves with a
"what proving it needs" paragraph (2026-07-31) found none that passes all
three, i.e. no further instance in that file.

1. **DIMENSION.** The subobject divided out must be positive-dimensional.
   `A/B` for an abelian subscheme is isogenous to a complementary abelian
   SUBscheme (Poincaré reducibility), which is an image of `A`. `E/C` for a
   FINITE `C` is not — same dimension, isogenous to no proper subobject —
   which is why `exists_isNIsogenyPair` is genuinely blocked.
2. **DIRECTION.** The conclusion must want maps only FROM the ambient; an
   image receives maps from `J`, never into it. (The known-negative on
   `exists_finiteKernelComplement_of_surjective_isAdditiveOn`.)
3. **AN AMBIENT MUST EXIST.** A conclusion of the form "this scheme exists"
   is never a candidate; one of the form "this map out of a scheme I already
   have exists" often is.

**Why:** the substitution reads as a general-purpose trick after it works
twice, and re-deriving each leaf against its conclusion is the expensive part.
These three tests are decidable from the conclusion alone in about a minute.

**How to apply:** before auditing a leaf for it, check the three tests; if any
fails, believe the docstring and record the audit ON THE LEAF so nobody repeats
it. Related: [[flt-inventory-audits-understate-what-exists]],
[[flt-leaf-cost-estimates-are-hypotheses]],
[[flt-missing-machinery-may-be-downstream]].

A separate finding from the same sweep, worth keeping because it is cheaper
than any of this: **a docstring's own prescribed refuting `grep` is usually
scoped too narrowly.** `exists_ramificationSet_geomPtField` names two files to
check for its missing Néron–Ogg–Shafarevich input; run wider, the verdict
survives but the ROUTE does not — the real home is
`Fermat/FLT/Mathlib/AlgebraicGeometry/NeronModel.lean`, which that docstring
never mentions.
