## DESCENT FROM `ℚ̄`-POINTS TO A `ℚ`-BASE IS `IsSchemeTheoreticallyDominant` + `IsClosedImmersion.lift` — AND FLATNESS OVER A FIELD IS FREE
(Same task.  The whole descent is 15 lines and it is the thing every "same geometric
points ⟹ same closed subscheme" leaf over `Spec ℚ` in this tree needs.)
`Scheme.Hom.ker_comp : (f ≫ g).ker = f.ker.map g` plus
`IdealSheafData.map_bot : (⊥).map g = g.ker` give, for `q.ker = ⊥`,
    (q ≫ a).ker = a.ker
so `j.ker ≤ (z ≫ j).ker = (q ≫ a).ker = a.ker` and `IsClosedImmersion.lift` produces the
factorisation on the base.  **A factorisation through a closed immersion descends along a
scheme-theoretically dominant morphism**, with no finiteness, no reducedness and no
hypothesis on any of the four schemes.
The dominant morphism to use is the BASE CHANGE `Z ×_k k̄ ⟶ Z`, and mathlib's
`IsSchemeTheoreticallyDominant.pullbackFst (f) (g)` needs `[dominant g] [QuasiCompact g]
[Flat f]` — where `f` is the structure map `Z ⟶ Spec k`.  **That flatness is free**:
`Mathlib/AlgebraicGeometry/Morphisms/Flat.lean:110` registers
`instance [Subsingleton Y] [IsIntegral Y] : Flat f`, and `Spec` of a field satisfies both.
So the only inputs are that `Spec k̄ ⟶ Spec k` is dominant (`.of_isDominant`, the target
being reduced; `IsDominant (Spec.map φ)` for a field map is already an instance) and
quasi-compact (affine).
Over `k̄` the remaining half is the decomposition of a finite reduced scheme into a finite
disjoint union of copies of the base, which this tree already proves.  Assembled:
`AlgebraicGeometry.exists_factor_of_geomPoints_of_isFinite`
(`Fermat/FLT/Mathlib/AlgebraicGeometry/GeomPointDescent.lean`, new, sorry-free) — `Z`
finite over `Spec k` with REDUCED GEOMETRIC FIBRE, `a : Z ⟶ X` whose every `k̄`-point
factors through a closed immersion `j`, factors through `j`.  **State the reducedness on
the GEOMETRIC FIBRE, not on `Z`**: that is the form the producers have
(`CyclicSubgroupOfOrder.isReduced_geomFibre_of_specQBase`), and it is the honest
hypothesis — over `k = 𝔽_p(t)` the reduced `Spec k[x]/(xᵖ−t)` has one `k̄`-point and a
non-reduced geometric fibre, and the conclusion fails for it.
**And the generic half belongs in a NEW UPSTREAM MODULE, not in a hoist.**  The three
algebraically-closed-base lemmas this needs are PROVEN in `MazurTorsion.lean` — ~18 000
lines BELOW the consumer, so unusable from it.  Hoisting them inside a 70 000-line file
with a dozen concurrent editors is the worst shape for a merge; copying them into a
mathlib-only module under a DIFFERENT NAMESPACE (`AlgebraicGeometry.foo'` against
`MazurIsogenyPrimeJ.foo`) costs one import line, cannot collide, and puts them where they
belong.  Say in the module docstring which copy should survive and put the deletion in
`to_merger` — `semmerge.py` propagates additions and never deletions, so a deletion done
now would silently come back.
