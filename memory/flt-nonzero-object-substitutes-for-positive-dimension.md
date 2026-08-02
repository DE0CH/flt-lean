---
name: flt-nonzero-object-substitutes-for-positive-dimension
description: "the object is nonzero" gives "the relative dimension is positive" via FINITE + DIVISIBLE, with no connectedness or étale-algebra structure theory
metadata:
  type: project
---

To exclude relative dimension `0` for an abelian scheme over a field, do NOT run
the classical argument (finite étale + connected source + a section ⟹ degree
one), which needs "a connected finite étale algebra over a field with a rational
point is the field".

Instead: a rel-dim-`0` abelian scheme has a FINITE geometric fibre, that fibre is
DIVISIBLE by every `M ≠ 0` (`exists_nsmul_eq_geomFibrePt`, no characteristic
hypothesis), and a finite divisible abelian group is trivial. Three lines.
Proven 2026-08-02 as `eq_zero_geomFibrePt_of_relativeDimension_zero` in
`Modularity/TateModule.lean`.

Two mechanics that make the finiteness step work:

* `card_fibrePt_eq_of_finrank_eq` gives `Nat.card = n`, which is **not**
  finiteness — `Nat.card` of an infinite type is `0`. What upgrades it is
  `Scheme.Hom.one_le_finrank_map f x : 1 ≤ f.finrank (f x)`, which needs only a
  POINT of the source (the zero section) and no surjectivity. Prefer it to
  `one_le_finrank_iff_surjective`.
* `Etale.iff_smoothOfRelativeDimension_zero` + this project's
  `locallyQuasiFinite_of_formallyUnramified` (in
  `Modularity/AbelianSchemeIsogeny.lean`) + `IsFinite.of_isProper_of_locallyQuasiFinite`
  is the whole chain from "proper, smooth of relative dimension 0" to `IsFinite`.

Related: [[flt-two-leaves-one-obstruction]], [[flt-degenerate-object-refutes-perfectness]].
