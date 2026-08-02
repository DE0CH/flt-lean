---
name: flt-identity-component-step-is-formal
description: "A morphism preserves the identity component" is 3 formal lines when the component is an idempotent — cut the leaf so it owes only the EXTENSION
metadata:
  type: project
---

(2026-08-01, `flt-lean-331`, `connected_locus_smul_of_hopf_package` in
`HardlyRamified/Threeadic.lean`.) Routes that say *"extend by Raynaud, then use that a
morphism of group schemes preserves the connected component of the identity"* read as
two pieces of geometry. **The second piece is formal.** With the component cut out by a
minimal counit-one idempotent `e₀`, and any algebra endomorphism `u` with `ε ∘ u = ε`:

* `u e₀` is idempotent, so minimality (`mul_eq_zero_or_mul_eq_of_minimal`,
  `GroupScheme/ConnectedEtale.lean`) gives `u e₀ · e₀ ∈ {0, e₀}`;
* the counit is an ALGEBRA map (`Bialgebra.counitAlgHom`), so
  `ε (u e₀ · e₀) = 1 ≠ 0` kills the zero branch;
* so `u e₀ · e₀ = e₀`, and applying a point `φ` turns `φ (1 ⊗ e₀) = 1` into
  `φ (1 ⊗ u e₀) = 1`.

So cut the leaf to owe only the EXTENSION — Raynaud fullness, stated coefficient-free.
Here that dropped `R`, `V`, `ρ`, the congruence level, `e₀` and four idempotent
hypotheses from the leaf; count `1 → 1`.

**General check: when a route says a canonical sub-object is preserved by a morphism, ask
how the sub-object is CUT OUT.** If it is the value of a point at a distinguished
element, preservation is a consequence of the structure maps being algebra maps, and the
only content is that the morphism exists. Ask for the morphism.

See also [[flt-ask-for-the-subobject-not-the-structure]],
[[flt-route-residue-is-the-cheap-route]], [[flt-galoisrep-space-has-no-module-instance]].
