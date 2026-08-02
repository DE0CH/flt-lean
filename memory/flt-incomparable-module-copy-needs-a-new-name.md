---
name: flt-incomparable-module-copy-needs-a-new-name
description: Copying a helper from an INCOMPARABLE module must rename it — the check is how many modules import BOTH, and it is usually not zero.
metadata:
  type: project
---

(2026-08-02, `Deformation.lean` needing `Threeadic.lean`'s place classification.) The
standing rule is that a helper reachable only from an incomparable or downstream module
may be **copied deliberately**. What that rule does not say is that copying it under the
SAME name is a hard build error whenever some third module sees both files.

Here `exists_prime_eq_toHeightOneSpectrumRingOfIntegersRat` lives in
`HardlyRamified/Threeadic.lean`; `Threeadic` and `Deformation` are incomparable (neither
is in the other's import closure). But **ten modules import BOTH** —
`Modularity/{Interface, Patching, KhareWintenberger}`,
`HardlyRamified/{Lift, Family, Frey, Reducible}`, `FreyCurve/Mazur`, `Fermat.Basic`,
`Fermat.PrimeFive` — so a same-named copy in the same namespace is
`environment already contains …` in every one of them. That is the cross-file duplicate
`xdup.py` exists to catch, manufactured on purpose.

**The check, before you paste, and it is the same closure walk as the cycle check:**

    # for every module M under Fermat/, is BOTH the source and the destination in M's
    # transitive import closure?  ASSERT each visited file exists — a swallowed
    # FileNotFoundError truncates the walk and returns the answer you were hoping for.

Zero hits means the name is free; any hits mean rename. Then say in the new docstring
that it IS a duplicate, which copy should survive, and where a single copy belongs (for a
statement about `𝓞 ℚ` with no representation theory in it, `Fermat/FLT/Mathlib/NumberField/`),
and put the hoist in `to_merger` rather than doing a two-file edit inside an unrelated
commit.

Related and cheaper: **the same walk answers whether you may simply ADD the import
instead.** Adding `import Threeadic` to `Deformation` was rejected here not because of a
cycle but because it drags a large module into the cone of a 27 000-line file to reach one
30-line helper. Price both before choosing.
