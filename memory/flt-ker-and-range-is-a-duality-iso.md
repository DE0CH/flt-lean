---
name: flt-ker-and-range-is-a-duality-iso
description: A leaf asking for a map with prescribed kernel-as-annihilator and range is EQUIVALENT to an isomorphism between the two subobjects — recut it to the citation's shape.
metadata:
  type: project
---

(2026-08-02, `poitouTateExactness_of_localTateDuality` in
`HardlyRamified/Deformation.lean`.) A leaf of the shape

    ∃ γ : Module.Dual K X →ₗ[K] H,  ker γ = W.dualAnnihilator  ∧  range γ = Z

for `W ≤ X` and `Z ≤ H` is **equivalent to `Nonempty (↥Z ≃ₗ[K] Module.Dual K ↥W)`**, over
any field, with **no finiteness anywhere**. Both directions are short:

* `⟸` (the one to write): `γ := Z.subtype ∘ₗ e.symm ∘ₗ W.dualRestrict`. Then
  `ker γ = ker dualRestrict = W.dualAnnihilator` because the other two factors are
  injective (`LinearMap.ker_comp`, `Submodule.comap_bot`,
  `Submodule.dualRestrict_ker_eq_dualAnnihilator`), and `range γ = range Z.subtype = Z`
  because the other two are surjective (`Subspace.dualRestrict_surjective` — note the
  `Subspace` namespace, `Submodule.dualRestrict_surjective` does not exist —
  `LinearMap.range_comp`, `Submodule.map_top`, `Submodule.range_subtype`). ~12 lines.
* `⟹`: the chain `Z ≅ range γ ≅ Dual X ⧸ ker γ = Dual X ⧸ ann W ≅ Dual W`, which is
  literally the `let e` inside `exists_nondegenerate_of_ker_eq_dualAnnihilator`.

**Why this is a recut worth making even though the count does not move.** The `∃ γ` form
is how the two exactness statements flanking one arrow of a long exact sequence read
(here NSW VIII.6.7); the iso form is the DUALITY THEOREM the literature actually states
and proves (NSW VIII.6.8). So the residue stops asking a prover to construct a map out of
the dual of a big space and verify two submodule equalities there, and starts asking for
the isomorphism a textbook hands over. Judge it by what is left in the leaf.

**The general tell:** a leaf whose conclusion pins BOTH `ker` and `range` of a map is not
really about the map — it is about the isomorphism `source ⧸ ker ≅ range` that they force.
Whenever the kernel is given as an ANNIHILATOR, that quotient is a dual, and the leaf is a
duality statement in disguise. See [[flt-recut-nonempty-iso-as-isiso-named-map]] for the
opposite move (a bare `Nonempty (A ≅ B)` recut as `IsIso` of a NAMED map): the two are
not in tension — name the map when the map is what a proof must construct, and delete it
when the map is bookkeeping over a duality the citation supplies.
