---
name: flt-eliminate-the-map-to-transport
description: To re-run a domain-only proof over R/I, restate it about the ELEMENTS it consumes instead of building the induced morphism; IsReduced is usually the real hypothesis
metadata:
  type: project
---

To extend a domain-only argument to a general base by quotienting by every prime, do
NOT build the induced morphism over `R ⧸ I` (the `AdjoinRoot.lift` recipe). Read the
proof and list what it actually consumes: a theorem stated about a map `Φ` is usually a
theorem about the images of two or three generators plus one relation between them.
Delete `Φ` from the statement, take those elements as parameters, and the base change
becomes free — mathlib ships element-level transport
(`WeierstrassCurve.Affine.CoordinateRing.map`, `map_mk`, `map_smul`) and nothing else is
needed.

Done on 2026-07-31 for `WeierstrassPoleOrder.linearShape_of_surjective` in
`Fermat/FLT/ModularCurve/X0.lean`: the ~200-line domain proof used `Φ` in exactly two
places, so `shape_of_relation` (stated about `P = Φ x`, `Q = Φ y`) is the same proof by
mechanical substitution and transports for free.

**Why:** the prescribed transport route was priced at a real chunk of instance plumbing;
eliminating the morphism cost one mechanical refactor and bought base change, the reduced
case, and reuse at maps nobody has constructed.

**How to apply:** (1) before transporting anything, grep the proof body for the morphism
and see how few times it appears; (2) once element-level, the prime sweep upgrades
`IsDomain` to `IsReduced` in about 20 lines — check whether the reduced case is free
before pricing the general one; (3) state the surviving residue as a HYPOTHESIS on the
remaining leaf (here `IsNilLinearShape`), discharged at the call site, rather than as a
docstring paragraph — a hypothesis is compiler-checked and makes the leaf strictly
weaker. See [[flt-two-leaves-may-be-one]] and [[flt-reduce-to-an-open-leaf-not-a-proof]].
