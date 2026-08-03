## A "THIS CONJUNCT CANNOT BE DERIVED" CLAUSE NAMES AN ARGUMENT — GREP FOR IT, INCLUDING BELOW YOUR LEAF

(2026-07-31, `flt-lean-7`, recutting `exists_relSchemeEnd_geomEquiv_of_weierstrassModel`
in `FreyCurve/MazurTorsion.lean`.)  A mature leaf's docstring often explains why a
particular conjunct is ASKED FOR rather than derived, and the explanation names the
missing argument.  That sentence is the most checkable thing in the docstring and
almost nobody checks it, because it reads as a design note rather than as a claim.

This one said the tautological-point conjunct "is asked for here rather than derived
downstream because … recovering it from `hint` alone would need *a morphism out of
`d.E` is determined by its `ℚ̄`-points*, which is a further reducedness/density
argument."  **That argument is `relPointEndo_ext`, PROVEN in the SAME FILE the
previous day** — over `AlgebraicGeometry.ext_of_apply_eq`, which mathlib has — and the
only thing between it and the leaf was **Lean's declaration order**: it sat ~3 400
lines below.

**The check is one `grep` and it must NOT stop at your own line number.**  A `sorry`
leaf cannot cite anything below it, so its author, reasoning locally, writes "this
needs X" about an X that exists and is merely mispositioned.  The commonest shapes of
X in this tree are all provable and all live low in their files: *a morphism is
determined by its `ℚ̄`-points* (`relPointEndo_ext`), *a natural family is
precomposition with one morphism* (`relPointEndo_apply_eq_comp`), *a morphism fixing
the zero section is additive* (`isAdditiveOn_of_post_zero`).

**Two riders, both of which turned a conjunct into a theorem in the same run.**

* **A RIGIDITY LEMMA'S BASE POINT IS WHAT DECIDES WHETHER IT IS FREE.**
  `isAdditiveOn_of_post_zero` (`X0.lean`) asks only for
  `RelPoint.post u hu (abA.zero (𝟙 S)) = abB.zero (𝟙 S)` — at the base point `𝟙`,
  not at every base point.  So ANY leaf that already pins its morphism on the
  `ℚ̄`-points, at `𝟙`, gets `IsAdditiveOn` for nothing: instantiate the point-level
  clause at `0` and use that `ε` and `φ` are additive.  **Before asking a geometry
  leaf for `IsAdditiveOn`, check whether one of its own clauses already fixes the
  zero section**; here it did, and the conjunct came out of the leaf.
* **A CARTESIAN SQUARE MAKES `RelPoint.along` AN EQUIVALENCE, so asking a leaf for
  BOTH point identifications of a base change is asking for one thing twice.**
  `X0.lean` carries `IsBaseChangeOf.toRelPoint` with `toRelPoint_injective`,
  `_add`, `_zero`, `_nsmul` — everything except SURJECTIVITY, which is the LIFT half
  of the same universal property and is three lines
  (`isPullback.lift (𝟙 _) y.1 y.2.symm`, then `lift_fst`/`lift_snd`).  With it, a
  leaf concluding about `RelPoint d.f (𝟙 (Spec ℚ̄))` alone delivers the
  `GeomFibrePt d₀.f (𝟙 SpecQ)` half and the link between them for free.  Note
  `𝟙 (Spec ℚ̄) ≫ specAlgClos ℚ` and `specAlgClos ℚ ≫ 𝟙 SpecQ` are **defeq** in
  `Scheme`, so no `RelPoint.pre` transport is needed across that seam — check this
  with a one-line `rfl` probe before writing any.

**Where the Galois clause is NOT free, and why it must stay coupled.**  The same
recut could not separate the `≃+` from the morphism: composing a geometric `ε` with
an automorphism `α` of the abstract group `E(ℚ̄)` replaces `φ` by `α φ α⁻¹`, which
need not be algebraic, and `E(ℚ̄)` — divisible of infinite rank — has many such `α`;
requiring `α` to commute with Galois does not obviously kill them, `E(ℚ̄)/tors` being
a `ℚ[Γ_ℚ]`-module of continuum dimension.  So a leaf of the form *"for ANY additive
`ε`, some `Ψ` intertwines `φ`"* is FALSE, and `ε` has to be produced by the same
proof that produces `Ψ`.  **State that in the docstring when you find it** — it is
the first cut a successor will try.

**And report a recut that moves in BOTH directions as two separate claims.**  This
one is WEAKER in its conclusion (four conjuncts became theorems, so the old falsity
analysis transfers verbatim — every counterexample to the new leaf is one to the old)
and STRONGER in its hypotheses (`n` and `hsq` are gone, so it now quantifies over all
of `End(E⁄ℚ̄)` rather than over the roots of one quadratic).  Only the second
direction owes a fresh audit, and here it is one line: `hsq` was consumed ONLY by the
conjunct that is now derived.  The count is `1 → 1`; say so, or a reader will score
the cycle at zero.

