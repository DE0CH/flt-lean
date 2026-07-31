---
name: flt-rat-algebra-diamond-use-minpoly
description: IsCyclotomicExtension.finrank on ℚ⟮ζ⟯ does not typecheck AT THE BASE ℚ (module'/Rat.semiring vs Algebra.toModule); go through minpoly instead
metadata:
  type: reference
---

`IsCyclotomicExtension.finrank` applied to `IntermediateField.adjoin ℚ {ζ}`
fails to unify at the concrete base `ℚ`, even though the identical proof works
verbatim over a field VARIABLE `K`. The mismatch is on two instances at once:

```
expected : @Module.finrank ℚ ↥ℚ⟮ζ⟯ Rat.semiring Field.toSemifield… ℚ⟮ζ⟯.module'
produced : @Module.finrank ℚ ?F  Field.toSemifield… CommRing.toCommSemiring… Algebra.toModule
```

This is a fresh instance of the recurring ℚ-algebra diamond already recorded on
`IsResidueCyclotomic` in `X0.lean`; the pattern used by
`isCyclotomicExtension_of_isPrimitiveRoot_of_finrank` right above it works only
because its base is a variable.

**How to apply:** to bound `[K : ℚ]` below by `φ(n)` from a primitive `n`-th
root of unity `ζ ∈ K`, never form the intermediate field. Use

```lean
have hmin : Polynomial.cyclotomic n ℚ = minpoly ℚ ζ :=
  hζ.minpoly_eq_cyclotomic_of_irreducible
    (Polynomial.cyclotomic.irreducible_rat (Nat.pos_of_ne_zero hn))
have h2 : (minpoly ℚ ζ).natDegree ≤ Module.finrank ℚ K := minpoly.natDegree_le ζ
rw [← hmin, Polynomial.natDegree_cyclotomic] at h2
```

needing only `[FiniteDimensional ℚ K]` and `NeZero n`. Verified 2026-07-31 in
`residueQDegree_eq_totient_of_le`, axiom-audited
`[propext, Classical.choice, Quot.sound]`.

Used by [[flt-overdetermined-degree-conjunct]].
