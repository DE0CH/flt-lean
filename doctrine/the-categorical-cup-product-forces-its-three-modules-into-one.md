## THE CATEGORICAL CUP PRODUCT FORCES ITS THREE MODULES INTO ONE UNIVERSE
(2026-07-31, discovered while vendoring `~/cs/FLT`'s continuous-cohomology cup product.)
`ContinuousCohomology.cup` produces a morphism `A ⟶ TopModuleCat.linHom B C`. A category has
morphisms only between objects of ITS OWN universe, so that arrow forces `A`, `B` and `C` — hence
the three coefficient modules — into one universe. The reference file states this as
`{M1 M2 M3 : Type v}` with `{G : Type v}`, which additionally ties them to the GROUP's universe;
that half is an accident and is removed by writing `Type (max v w)`, which is what the port here
does. **The three-modules-agree half is NOT removable**: `homOfBilinear {A B C} : A ⟶ linHom B C`
needs `A`'s universe to be `max B C`, and no amount of generalisation changes that.
Why this bites in practice: in `HardlyRamified/Deformation.lean` the coefficient field is
`k : Type u` and the module is `V : Type v`, INDEPENDENT universe variables, so `AdZero k V` and
the dualising module `k(1)` are in different universes and cannot be cup-multiplied as they stand.
`max u v = v` is not derivable, and no clever choice of a `Type v` copy of `k` avoids it (the
copies one can build — `span {1} ⊆ End k V`, `End k V ⧸ ad⁰` — carry the wrong action or need
`V ≠ 0`). **The fix is `ULift`, on all three modules at once, into `Type (max u v)`**: `ad⁰` and
`ad⁰(1)` by `ULift.{u}`, `k(1)` by `ULift.{v}`. When every carrier is DISCRETE — as here — the
transport is free: `contRepULift` (in `Deformation.lean`) moves the action, and continuity is
`continuous_of_discreteTopology` throughout.
One wart it leaves: a definition whose carrier is `ULift.{v} k` mentions `v` but not `V`, so its
universe is a free parameter and use sites can leave it ambiguous. Give such a definition an
explicit `(V : Type v)` argument as a UNIVERSE MARKER; it is ugly and it makes every use site
unambiguous, which is worth more.
