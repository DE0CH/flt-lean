---
name: flt-constrain-the-replacements-values
description: A "hand back a DIFFERENT object with the same pin" leaf that got duplicated for an extra equivariance de-duplicates by constraining the replacement's VALUES, not by transporting the property
metadata:
  type: project
---

When a leaf reads *"given `v`, produce `u` satisfying the same PIN"*, and a sibling
leaf exists only because `u` must ALSO keep some property of `v` (equivariance under
`w_J`, commutation with something, …), the sibling is almost never new mathematics.
The two leaves collapse into one by adding a clause that constrains the
replacement's **values**:

    ∀ n, u n = v n ∨ u n = 𝟙 J

Every commutation property of `v` then transports for free — `v`'s own hypothesis in
the left disjunct, `Category.id_comp`/`comp_id` in the right.

**Why:** the sibling's docstring reasoning is correct and still misleading. It argues
that the property *cannot be transported across the replacement, because the
replacement shares only the PIN and the pin does not determine the object*. True — but
that is a statement about what the CONCLUSION says, not about what the intended
construction does. The intended construction is always "take `v` at the pinned
arities, `𝟙` elsewhere", which satisfies the value clause verbatim. So the clause is a
strengthening of the producer's obligation that costs the producer nothing and hands
every consumer the transport at once.

**How to apply:** before proving a `_atkinLehner` / `_equivariant` / `_commuting`
variant of a replacement leaf, check whether both leaves' own audits name the SAME
witness. If they do, cut one shared leaf carrying the value clause and prove both over
it. Done 2026-07-31 for `exists_commutingHeckeAlbaneseFamily` and
`exists_commutingHeckeAlbaneseFamily_atkinLehner` in `Fermat/FLT/ModularCurve/X0.lean`
(two leaves → one, `exists_commutingHeckeAlbaneseFamily_values`).

Two things that came free with it and generalise:

* **A vacuous-regime hypothesis is usually dischargeable at the CALL SITE.** These
  leaves' pin opens with `∀ d : Gamma0Datum N ℚ̄`. `by_cases` on `Nonempty` of that
  type proves the empty branch outright (`u := fun _ => 𝟙 J`), so the shared leaf can
  carry an explicit inhabitant as a hypothesis — which is exactly the non-vacuity
  witness CLAUDE.md demands of a generation-flavoured cut. Getting the witness for
  free is the normal case, not a lucky one.
* **`Nonempty` alone is NOT enough to make a bare `∀`-commutation true**, even though
  it kills the obviously vacuous regime. Here the pin is a `∀` over decomposition
  DATA, and data can fail to exist at an inhabited datum; if the reached set is not
  dense the morphisms are unconstrained. Keep the ∃-shape.

See [[flt-cut-leftovers-close-sibling-leaves]] and [[flt-two-leaves-may-be-one]].
