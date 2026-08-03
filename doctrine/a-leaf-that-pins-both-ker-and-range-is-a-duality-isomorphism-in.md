## A LEAF THAT PINS BOTH `ker` AND `range` IS A DUALITY ISOMORPHISM IN DISGUISE — recut it to the citation's shape
(2026-08-02, `flt-lean-254`, `poitouTateExactness_of_localTateDuality` in
`HardlyRamified/Deformation.lean`.) A leaf of the shape
    ∃ γ : Module.Dual K X →ₗ[K] H,  ker γ = W.dualAnnihilator ∧ range γ = Z
is how the two exactness statements FLANKING ONE ARROW of a long exact sequence read —
here NSW VIII.6.7's `P¹_S(M) → H¹(G_S, M*)^∨ → H²(G_S, M) → P²_S(M)`. It is **equivalent,
over any field and with NO finiteness, to `Nonempty (↥Z ≃ₗ[K] Module.Dual K ↥W)`** — which
for this instance is NSW **VIII.6.8**, the duality theorem the literature states and
proves. So the `∃ γ` form asks a prover to construct a map out of the dual of a big space
and check two submodule equalities there; the iso form asks for the isomorphism a textbook
hands over, and mentions neither ambient space, no `γ` and no annihilator.
**The direction you write is ~12 lines**: `γ := Z.subtype ∘ₗ e.symm ∘ₗ W.dualRestrict`,
whose kernel is `W.dualAnnihilator` because the other two factors are injective
(`LinearMap.ker_comp`, `Submodule.comap_bot`,
`Submodule.dualRestrict_ker_eq_dualAnnihilator`) and whose range is `Z` because the other
two are surjective (`LinearMap.range_comp`, `Submodule.map_top`,
`Submodule.range_subtype`). Note **`Subspace.dualRestrict_surjective`** — the `Submodule.`
spelling does not exist, and the error names the wrong thing. The reverse direction is the
`let e` already inside `exists_nondegenerate_of_ker_eq_dualAnnihilator`, so record it in
the docstring rather than writing it: as Lean it would have no consumer.
**The general tell: a conclusion that pins BOTH the kernel and the range of a map is not
about the map.** It is about the isomorphism `source ⧸ ker ≅ range` they force, and when
the kernel is given as an ANNIHILATOR that quotient is a dual. Check for it whenever a leaf
was cut out of a long exact sequence — two exactness statements at two spots is exactly
this shape, and the sequence is usually not what the reference proves directly.
Two riders from the same run, both about the SECOND half of that task, which was paying an
obligation the leaf's docstring named and did not discharge (*"`N_S` acts trivially on
`ad⁰` and on `ad⁰(1)`; that identification is not proven in this file"*).
* **A docstring sentence naming TWO inputs at once is usually one cheap and one hard.**
  Here the `ρbar` half closed outright — `N_S ≤ ker ρbar` is the exact CONVERSE of the
  file's own `isUnramifiedAt_of_ramificationKernel_le_ker`, and needs only that `ker` is
  normal (free) and CLOSED, the latter from `discreteTopology_moduleTopology` in
  `Chebotarev.lean` plus `Subgroup.{normalClosure_le_normal, topologicalClosure_minimal}`.
  The cyclotomic half is the discriminant of `ℚ(μ_ℓ)` and is genuinely absent. **Split
  before pricing**: one obligation became one leaf plus eleven theorems.
* **Reduce a `N_S`-shaped obligation to its LOCAL statement, because the closure argument
  is generic.** `N_S` is `closure (normalClosure (⋃_{v ∉ S} I_v))`, so *anything* of the
  form `N_S ≤ K` follows from `I_v ≤ K` for `v ∉ S` as soon as `K` is normal and closed —
  and for `K` = "fixes `μ_m`" both are cheap (normal because Galois permutes `μ_m`, closed
  because it is OPEN by the already-proven `isOpen_setOf_fixes_rootsOfUnity`, and an open
  subgroup is closed). So the residue becomes *"`ℚ(μ_ℓ)/ℚ` is unramified outside `ℓ`"*, a
  named citation with no `ramificationKernel` in it. Do this whenever a leaf's statement
  mentions `ramificationKernel`: the topology is yours and the local statement is theirs.
