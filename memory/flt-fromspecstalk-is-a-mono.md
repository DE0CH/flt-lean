---
name: flt-fromspecstalk-is-a-mono
description: "X.fromSpecStalk x is a mono, so two ring maps out of a stalk agreeing after Spec-and-compose are equal in two lines — no IsLocalRing, no SpecToEquivOfLocalRing"
metadata: 
  node_type: memory
  type: reference
  originSessionId: 364d16d0-8a36-4e4b-af0c-b33f7a0a2b39
  modified: 2026-08-01T19:23:43.356Z
---

Mathlib registers `instance (priority := 900) [IsPreimmersion f] : Mono f`
(`Morphisms/Preimmersion.lean`) and `instance : IsPreimmersion (X.fromSpecStalk x)`
(`AlgebraicGeometry/Stalk.lean`). So from
`Spec.map a ≫ X.fromSpecStalk y = Spec.map b ≫ X.fromSpecStalk y` one gets
`a = b` by `Spec.map_injective ((cancel_mono _).mp h)`.

**Why:** the obvious tool, `AlgebraicGeometry.SpecToEquivOfLocalRing`, demands
`IsLocalRing` on the source ring and `IsLocalHom` on the map — real side
conditions for a square-zero extension, and entirely unnecessary here.

**How to apply:** whenever a scheme-level argument has to be pushed back to an
equality of ring homomorphisms out of a stalk. Used to close
`kaehler_stalkMap_mulByNat_prime_eq_zero`
([[flt-omega-of-group-scheme-is-the-tangent-space]]). The companion lemma for
moving through a morphism is `Scheme.SpecMap_stalkMap_fromSpecStalk`, and
`Spec.fromSpecStalk_eq` computes `fromSpecStalk` on an affine.
