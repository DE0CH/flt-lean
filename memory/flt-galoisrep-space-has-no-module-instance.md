---
name: flt-galoisrep-space-has-no-module-instance
description: GaloisRep.Space carries AddCommGroup and the Γ-action but NO Module instance — name the scalar action as an opaque LinearMap on the underlying module
metadata: 
  node_type: memory
  type: reference
  originSessionId: dccabb9c-27a2-4f67-afe6-a46b78da8df0
  modified: 2026-08-01T18:25:21.680Z
---

(2026-08-01, `flt-lean-331`.) `GaloisRep.Space ρ` is a `def` synonym for the module `M`
with `AddCommGroup` (via `inferInstanceAs`) and a `DistribMulAction (Γ K)` whose `smul g v`
is `ρ g v`. It has **no `Module A` instance**. So for
`fG : … →+[Γ Kᵥ] (ρ.toLocal v).Space`, writing `a • fG φ` fails with

    failed to synthesize   HSMul A ((ρ.baseChange A).toLocal v).Space ?m

even under `set_option backward.isDefEq.respectTransparency false` — that option governs
DEFEQ checks, not instance SEARCH. A type ascription does not help.

Cure: name the action on the underlying module and let application cross the synonym by
defeq, with `obtain` so the map stays opaque:

    obtain ⟨La, hLa⟩ : ∃ La : (Q ⊗[R] V) →ₗ[Q] (Q ⊗[R] V),
        ∀ z, La z = (algebraMap R Q r) • z :=
      ⟨(algebraMap R Q r) • LinearMap.id, fun z => rfl⟩

`La (fG φ)` then elaborates; `map_add La` is free; equivariance is `map_smul` of
`(ρ.baseChange Q).toLocal v σ : Module.End Q _`. Same `obtain ⟨f, hf⟩ : ∃ f, ∀ x, f x = …`
idiom for any conjugated map — `set` leaves a let-bound local that later `rw`s
zeta-unfold. `σ • z` on `.Space` is defeq to `(ρ.toLocal v) σ z`, so `show` and `exact`
cross it while `rw` may not.

See also [[flt-identity-component-step-is-formal]].
