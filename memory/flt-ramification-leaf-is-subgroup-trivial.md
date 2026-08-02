---
name: flt-ramification-leaf-is-subgroup-trivial
description: An "unramified" leaf over a Galois extension is a subgroup-is-trivial leaf, and the pin has that dictionary archimedean AND nonarchimedean
metadata:
  type: project
---

(2026-07-31, `flt-lean-38`, `NumberField/UnramifiedClassFieldExistence.lean`.) Mathlib turns
each ramification statement into "this subgroup of `Gal(M/K)` is trivial":

* archimedean — `NumberField.InfinitePlace.isUnramified_iff_stabilizer_eq_bot [IsGalois k K]`;
* nonarchimedean — `Ideal.card_inertia_eq_ramificationIdxIn` + `ramificationIdxIn_eq_ramificationIdx`
  + `Ideal.ramificationIdx_eq_one_iff`.

**Why:** the cost is decided entirely by two instances, and at this pin BOTH are found by
search — `IsGaloisGroup Gal(L/K) (𝓞 K) (𝓞 L)` (via `IsGaloisGroup.of_isFractionRing`) and
`PerfectField (Q.under (𝓞 K)).ResidueField`. Without them it is a development; with them a
compositum leaf is ~40 lines.

**How to apply:** before pricing such a leaf, run a two-line scratch
`example … := by infer_instance` on those two instances — that is the whole feasibility
study. Then re-read the leaf as a triviality statement about a subgroup. Two caveats paid
for in that run: the route forces `[IsGalois K Lᵢ]` (it restricts an element of `Gal(K̄/K)`),
which the leaf may not carry and the consumer usually does — adding an INSTANCE-IMPLICIT
hypothesis moves no call site; and on the ARCHIMEDEAN side the dictionary is not optimal —
the embedding argument over `NumberField.eqOn_sup_of_eqOn` proves the same thing with no
Galois hypothesis, and `merger` already had it. See
[[flt-merger-check-is-per-declaration]].
