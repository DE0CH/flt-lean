---
name: flt-morphism-hypotheses-buy-elementary-facts
description: "A leaf carrying IsProper/Smooth/GeometricallyConnected is not at its citation's generality — derive the 4-5 elementary facts in the assembly and restate the leaf over them"
metadata: 
  node_type: memory
  type: project
  originSessionId: 29cb3fe7-f236-4bc9-887f-9ad78994eb0c
  modified: 2026-08-01T17:35:38.573Z
---

(2026-08-01, `flt-lean-289`.) A leaf whose binders are *morphism properties over a base*
is almost never stated at the generality its citation has. Hartshorne II Ex. 3.5 asks for
noetherian + integral + separated; II 6.11 adds regular. None is a morphism property, none
mentions a field. The heavy hypotheses are there because the CALL SITE has them, and each
is spent in one place producing an elementary fact.

**Why:** restating the leaf over the elementary facts is `1 → 1` on the count and deletes
the entire unpacking step from the prover's job — the residue becomes the textbook
statement, dispatchable to someone who never opened the file.

**How to apply:** derive them in the assembly. Over `fK : X ⟶ Spec (CommRingCat.of K)`,
with `haveI := hproper` in context (Lean's instance search DOES use local hypotheses of
class type, so no destructuring):

    haveI : IsLocallyNoetherian (Spec (CommRingCat.of K)) := inferInstance   -- REQUIRED first
    haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian fK
    haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace fK
    haveI : X.IsSeparated := by constructor; rw [← terminal.comp_from fK]; infer_instance

`IsSeparated fK`, `QuasiCompact fK`, `LocallyOfFiniteType fK` come from `IsProper fK` by
bare `infer_instance`. Integrality: `Fermat.isIntegral_of_smooth_of_geometricallyConnected`
(`AbelianSchemeIsogeny.lean`) — see [[flt-relative-dimension-unused-in-integrality]].

Related: [[flt-cut-at-the-missing-object]], [[flt-leaf-cost-estimates-are-hypotheses]].
