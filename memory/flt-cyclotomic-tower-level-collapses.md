---
name: flt-cyclotomic-tower-level-collapses
description: A leaf quantified over a level n of a cyclotomic tower is stronger than its citation; the abelian action on roots of unity collapses it to n = 1 for free.
metadata: 
  node_type: memory
  type: project
  originSessionId: 584f13b9-f495-48ab-b761-22fb23f35415
  modified: 2026-08-02T20:30:07.939Z
---

A leaf stated at every level `n` of a tower (`Fix(μ_{p^n})`, level-`ℓ^n` congruence
data) is STRICTLY STRONGER than the classical theorem it cites, which is almost always
about `n = 1`. The extra strength is invisible in the statement and nobody prices it.

When the level enters through roots of unity the collapse is cheap, because `Γ` acts on
`μ_m` through `Aut(ℤ/m) = (ℤ/m)ˣ`, which is ABELIAN — so `[Γ, Fix(μ_p)] ≤ Fix(μ_{p^n})`.
For a cocycle `z` vanishing on `N = ker ρbar ∩ Fix(μ_{p^n})` and `h ∈ N₁ = ker ρbar ∩
Fix(μ_p)`: the commutator lies in `N`, so `z (g h g⁻¹) = z h`; and `ρ (g h g⁻¹) = 1`
kills the correction term of `ContinuousCohomology.eval₁_conj`, so
`z (g h g⁻¹) = ρ g (z h)`. Hence `z h ∈ M^Γ`, and `H⁰ = 0` finishes.

**The Lean tool is `modularCyclotomicCharacter'` — the PRIMED one.** The unprimed one
demands `Nat.card (rootsOfUnity n L) = n`; the primed lands in `(ZMod d)ˣ` for the actual
`d` and needs no hypothesis at all. Commutative target ⟹ commutators map to `1`, and
`modularCyclotomicCharacter'.spec'` reads that back as `ζ ↦ ζ`. ~20 lines, no
`IsCyclotomicExtension`, no primitive root. Feed it `AlgEquiv.toRingEquiv` as a
`MonoidHom` (`map_one'`/`map_mul'` are `rfl`) and `rootsOfUnity.mkOfPowEq` to turn
`ζ ^ m = 1` into a member.

**How to apply:** when a leaf quantifies over a level and its citation does not, ask what
the tower's Galois group is a quotient of. Abelian ⟹ the levels above the first are a
central extension and collapse against `H⁰ = 0`. Landed in `Patching.lean` as
`fixes_rootsOfUnity_commutator` (2026-08-02). Related:
[[flt-circularity-guard-check-module-order]].
