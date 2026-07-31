---
name: flt-rat-algebra-diamond-decomphom-vs-tolocal
description: "Deformation.lean's decompHom and GaloisRep.toLocal use DIFFERENT Algebra ℚ (adicCompletion ℚ v) instances, so ker-membership at inertia does not transfer by `exact`; congr 3 + RingHom.ext_rat fixes it"
metadata:
  type: project
---

`GaloisRepresentation.decompHom v` (`HardlyRamified/Deformation.lean`) is
`Field.absoluteGaloisGroup.map (algebraMap ℚ (HeightOneSpectrum.adicCompletion ℚ v))`
and, because the base is the concrete `ℚ`, instance search resolves that
`algebraMap` through **`DivisionRing.toRatAlgebra`**. `GaloisRep.toLocal v` is
`ρ.map (algebraMap _ _)` over a *variable* base field, so it resolves through
**`HeightOneSpectrum.instAlgebraAdicCompletion`**.

The two are propositionally but not syntactically equal, so anything proved about
`globalInertia`/`ramificationKernel` (built from `decompHom`) does **not** hand
over to `GaloisRep.IsUnramifiedAt` (built from `toLocal`) by `exact`. The failure
prints as a type mismatch between two terms that differ only inside the elided
instance argument, which reads like a defeq bug rather than a diamond.

The fix is three lines and no `letI`:

```lean
show ρ.toLocal v σ = 1
rw [GaloisRep.toLocal_apply]
refine Eq.trans ?_ h3          -- h3 : ρ (decompHom v σ) = 1
congr 3
exact RingHom.ext_rat _ _      -- any two ring homs out of ℚ agree
```

`RingHom.ext_rat` is the cheap universal solvent here: it needs no `Subsingleton
(Algebra ℚ ·)` juggling and no local instance attribute, because the diamond is
only ever *between ring homomorphisms out of `ℚ`*.

This is the same family as the doctrine's `Algebra ℚ (AlgebraicClosure ℚ)` entry,
but a different joint, and the doctrine's three prescribed fixes (variable base
field / `Subsingleton.elim` transport / local instance priority) are all more
expensive than `RingHom.ext_rat` when the mismatch is between two `ℚ →+* K`.

Used in `isUnramifiedAt_of_ramificationKernel_le_ker`.
