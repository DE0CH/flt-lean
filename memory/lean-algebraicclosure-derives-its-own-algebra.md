---
name: lean-algebraicclosure-derives-its-own-algebra
description: Never hand-install `Algebra R (AlgebraicClosure k)` — supplying `Algebra R k` derives it, the scalar tower and `CharP`; a hand-installed one is a second non-defeq SMul.
metadata:
  type: reference
---

`AlgebraicClosure.instAlgebra {R} [CommSemiring R] [Algebra R k] : Algebra R (AlgebraicClosure k)`
is an INSTANCE, and so are `IsScalarTower R S (AlgebraicClosure k)` (given the tower on `k`)
and `CharP (AlgebraicClosure k) p` (given `CharP k p`). So supply `Algebra R k` and stop.

A `letI : Algebra R (AlgebraicClosure k) := (ZMod.castHom …).toAlgebra` beside it is a
SECOND, non-defeq `SMul`, and `IsScalarTower.of_algebraMap_eq'` then fails to typecheck
against `AlgebraicClosure.instSMulOfIsScalarTower` — the error prints two `IsScalarTower`
applications differing only in their `SMul` arguments plus a "definition is not exposed:
`OreLocalization.instAdd`" note, which reads as a universe or module-system problem and is
neither.

**How to apply:** if you find yourself writing `letI : Algebra _ (AlgebraicClosure _)`,
delete it and install the algebra on the BASE instead; then delete the `IsScalarTower` and
`CharP` `haveI`s too, because they are inferred. Measured 2026-08-02 (flt-lean-332): three
deleted `haveI`s were the entire fix. Same family as
[[flt-rat-algebra-diamond-use-minpoly]] — two live instances of one class, distinguished
only by an error message that names neither.
