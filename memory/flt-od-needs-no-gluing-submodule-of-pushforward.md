---
name: flt-od-needs-no-gluing-submodule-of-pushforward
description: "Mathlib has no SheafOfModules gluing at this pin, but O(D) is a PresheafOfModules.Submodule of the pushforward j_*O_U — so a \"glue an invertible sheaf\" route note has mispriced the leaf"
metadata: 
  node_type: memory
  type: reference
  originSessionId: 29cb3fe7-f236-4bc9-887f-9ad78994eb0c
  modified: 2026-08-01T17:35:53.961Z
---

(2026-08-01, `flt-lean-289`, surveyed rather than recalled.) `Mathlib/Algebra/Category/
ModuleCat/Sheaf/` at this pin is `Abelian`, `ChangeOfRings`, `Colimits`, `Free`,
`Generators`, `Limits`, `Localization`, `LocallyFree`, `Pullback*`, `Pushforward*`,
`Quasicoherent` — **no descent, no gluing**. There is also no `𝒪(D)`, no Cartier divisor,
no `Ample` anywhere under `Mathlib/AlgebraicGeometry/`; the divisor-adjacent material is
`AlgebraicCycle/Basic.lean` and `OrderOfVanishing.lean` only.

**Why it matters:** a route note saying "glue `𝒪_{V i}` along the transition units" has
priced a theory build, not a construction.

**How to apply:** build `𝒪(D)` as a SUBOBJECT instead. Both halves are in the pin:

* `(Scheme.Modules.pushforward U.ι).obj (modUnit ↥U)` — i.e. `j_* 𝒪_U`, sections over `W`
  being `Γ(U ⊓ W, 𝒪)`; already used in `Fermat/FLT/Modularity/AmpleSheaf.lean`;
* `PresheafOfModules.Submodule` (`Mathlib/Algebra/Category/ModuleCat/Presheaf/
  Submodule.lean`) — `toPresheafOfModules`, `ι`, `Mono ι`, `CompleteLattice`.

Take the sections over `W` to be the `g` with `(f i) · g` extending to `V i ⊓ W` for all
`i`; multiplication by `f i` trivializes on `V i` and sends the canonical `s := 1` to
`f i`, which is what `nonvanishingAt_iff_trivializedSection` consumes. Same move works for
`I_Z` and for fractional ideals.

Related: [[flt-theory-absence-claims-need-a-directory]].
