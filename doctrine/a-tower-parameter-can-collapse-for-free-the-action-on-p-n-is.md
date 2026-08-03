## A TOWER PARAMETER CAN COLLAPSE FOR FREE — the action on `μ_{p^n}` is ABELIAN
(Same task, and it is what removed `n` from the leaf.)  A leaf quantified over a
LEVEL — `Fix(μ_{p^n})`, `ker ρ mod ℓ^n`, a congruence subgroup at level `n` — is
routinely stated at every `n` because the consumer needs every `n`, while the
classical theorem it cites is about `n = 1`.  For `n ≥ 2` the stated leaf is then
STRICTLY STRONGER than its own citation, and nobody notices because the extra strength
is invisible in the statement.
The collapse is cheap whenever the level enters through roots of unity, because
`Γ` acts on `μ_m` through `Aut(ℤ/m) = (ℤ/m)ˣ`, which is **abelian**:
* `[Γ, Fix(μ_p)] ≤ Fix(μ_{p^n})` — a commutator acts trivially on every `μ_m`;
* so for `h ∈ N₁ = ker ρbar ∩ Fix(μ_p)`, the commutator `g h g⁻¹ h⁻¹` lies in
  `N = ker ρbar ∩ Fix(μ_{p^n})`, giving `z (g h g⁻¹) = z h` for a cocycle vanishing
  on `N`;
* while `ρ (g h g⁻¹) = 1` kills the correction term of
  `ContinuousCohomology.eval₁_conj`, giving `z (g h g⁻¹) = ρ g (z h)`;
* hence `z h ∈ M^Γ`, and `H⁰ = 0` finishes.
**The Lean tool is `modularCyclotomicCharacter'` — the PRIMED one.**
`modularCyclotomicCharacter` (unprimed) demands `Nat.card (rootsOfUnity n L) = n`, a
real hypothesis; the primed version lands in `(ZMod d)ˣ` for `d` the actual number of
roots of unity and needs NOTHING.  Since the target is commutative, a commutator maps
to `1`, and `modularCyclotomicCharacter'.spec'` reads that back as `ζ ↦ ζ`.  Twenty
lines, no `IsCyclotomicExtension`, no primitive root.  Feed it
`AlgEquiv.toRingEquiv` packaged as a `MonoidHom` (`map_one'` and `map_mul'` are both
`rfl`), and `rootsOfUnity.mkOfPowEq` to turn `ζ ^ m = 1` into a member.
**Generalisable check, one careful read of the leaf's citation:** if the literature
proves the statement at one level and your leaf quantifies over all of them, ask what
the tower's Galois group is a quotient of.  When it is abelian — cyclotomic towers,
Kummer towers, anything landing in `(ℤ/m)ˣ` — the levels above the first are a
CENTRAL extension and collapse against `H⁰ = 0`.
