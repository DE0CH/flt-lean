## A LEAF THAT NEEDS A WHOLE CHAPTER IS STILL WORTH A SESSION — MOVE THE BOUNDARY, IN CODE
(2026-08-01, `flt-lean-134`, on `exists_rationalCuspSectionsX1_field` in
`ModularCurve/X1.lean`.)  Some leaves genuinely require constructing an object
this development does not have — here, `Y_1(N)` itself, since the leaf's cusps
exist only because `coarse` pins `Y` as the affine modular curve, and pinning it
means exhibiting it.  No cut closes that, and no session finishes it.
**The deliverable is then not a proof and not a survey: it is the LARGEST PREFIX
of the route written as Lean, with the residue restated in the sentence the
literature proves.**  Concretely here: properness of `X` turns a `K⸨q⸩`-point
into a `K⟦q⟧`-point, evaluation at `q = 0` turns that into a `K`-rational
section, and `IsCusp` of that section reduces to *the family does not extend
inside `Y`*.  All of it is scheme theory with no moduli input, all of it is now
proven, and the leaf that remains says only *the Tate family degenerates to
`φ(N)/2` distinct cusps* — which is Deligne–Rapoport VI.5 and nothing else.
Count unchanged `1 → 1`; what changed is what is LEFT in the leaf, which is the
measure this file already prescribes for a recut.
The three checks that make such a recut safe, all cheap:
* **the residue must be TRUE**, and the fastest way to be sure is to check the
  parent IMPLIES it, or that a witness you can name does.  Here the Tate family
  witnesses it for every `K`;
* **say plainly if the residue is STRICTLY STRONGER than the parent.**  Mine is:
  it demands the cusps come from `Γ₁(N)`-data over `K⸨q⸩` rather than from
  anywhere.  That is the route the leaf's own docstring had prescribed for a day,
  and committing to it in code rather than in prose is the point — but it is a
  commitment, and the docstring must invite a successor to restate rather than
  work around it;
* **the prefix must be CONSUMED.**  A valuative-criterion lemma parked beside an
  untouched `sorry` is free-floating and will be swept.  Making the residue's
  STATEMENT mention the constructions (`laurentCuspPoint`, and the non-extension
  clause) is what puts them in the cone.
### The reusable move: a NEGATIVE predicate about points of `X` becomes NON-EXTENSION over the disc
`IsCusp x` is `¬ ∃ y : RelPoint strY (𝟙 S), sectionAlong jY h.comm y = x` — a
negative statement about an open immersion `jY : Y ⟶ X`, and negative statements
are what a prover cannot attack.  When the point is produced as the LIMIT of a
family over a DVR `R`, it converts, because **`Spec R` has exactly two points**:
if the limit were in the image of `jY`, then both the closed point (the limit)
and the generic point (the family, which was given as a point OF `Y`) map into
the open, hence `Set.range l.base ⊆ Set.range jY.base`, hence
`IsOpenImmersion.lift` factors the whole lift through `Y` — which is an extension
of the family over the disc inside `Y`.
So `IsCusp (limit) ⟸ the generic point does not extend to an R-point of Y`, and
the right-hand side mentions neither `X` nor properness.  **Look for this
whenever a leaf's hard clause is "not in the image of the open part" and the
route is a degeneration.**  The formal cost is the two-point classification
(`p.asIdeal = ⊥ ∨ p.asIdeal = 𝔪`, from `Ideal.IsPrime.isMaximal` at a PID) plus
identifying each point as the image of `Spec (Frac R)` and of `Spec (R/𝔪)`; about
sixty lines, once, for any DVR.
### The valuative criterion over a FIELD base is not `bijective_pre_generic_of_isProper`
That theorem (`X0.lean`) is for a scheme over `Spec R` and answers "does a
`Frac R`-point extend".  A degeneration argument needs the other shape: the
scheme is over `Spec K` and the DVR is the PARAMETER, so the square is
`Spec F ⟶ X`, `Spec R ⟶ Spec K`, and the lift is an `R`-point of `X` over `K`.
Both are three lines over `IsProper.eq_valuativeCriterion`; they are not the same
statement and neither follows from the other.  `Fermat.exists_lift_of_isProper_of_valuationRing`
is the field-base one, with `lift_unique_of_isProper_of_valuationRing` beside it —
and the uniqueness half is not optional, because it is what lets a
`Classical.choose`-defined limit be identified with any lift a prover can name.
### `K ⊆ K⟦q⟧ ⊆ K⸨q⸩` IS NOT A REGISTERED TOWER
Measured 2026-08-01: `Algebra K K⟦q⟧` (`MvPowerSeries.instAlgebra`),
`Algebra K⟦q⟧ K⸨q⸩` (`HahnSeries.ofPowerSeries`) and `Algebra K K⸨q⸩`
(`HahnSeries.instAlgebra`) all synthesize, and **`IsScalarTower K (PowerSeries K)
K⸨X⸩` does not** — three unrelated construction routes and no tower instance
between them.  Any lemma that needs the compatibility must take it as an
EQUATION of ring maps; the equation itself is two lines
(`ext x; simp [LaurentSeries.coe_algebraMap, LaurentSeries.algebraMap_apply]`).
Everything else one wants there is present for a bare `(K : Type) [Field K]`:
`IsDiscreteValuationRing K⟦q⟧`, `ValuationRing K⟦q⟧`, `IsFractionRing K⟦q⟧ K⸨q⸩`,
`CompleteSpace K⸨q⸩`, and `WeierstrassCurve.tateCurve q : WeierstrassCurve K⸨q⸩`
with no characteristic hypothesis.
### VERIFY BY EXTRACTING THE INSERTED RANGE — the stale olean is the point
The standing trick is to develop in a scratch that `public import`s the target
module.  Its sharpest form applies AFTER the edit: `lake build` has not run, so
the target's olean is the PRE-EDIT one — which contains exactly the declarations
your new text depends on and none of the ones it defines.  So
    A=<first line of your block>; B=<last>
    { echo module; echo "public import <the target>"; <the target's own opens>;
      sed -n "${A},${B}p" <the target>; } > /tmp/Scratch.lean
    lake env lean /tmp/Scratch.lean
compiles **the very characters you are committing**, in 9 seconds against a
15-minute build.  Rename any declaration whose name already exists in the olean
(here just the parent, whose body changed) and expect exactly the `sorry`
warnings you intend.  This beats keeping a hand-typed parallel copy, which is the
usual way the scratch and the committed text drift apart.
