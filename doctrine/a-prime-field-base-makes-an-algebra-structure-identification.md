## A PRIME-FIELD BASE MAKES AN "ALGEBRA STRUCTURE" IDENTIFICATION FREE — `RingHom.ext_zmod` + `Algebra.algebra_ext`
(2026-08-01, `flt-lean-66`, closing `eulerCount_eq_effectiveDivisorCount` in
`Modularity/Interface.lean`.)  That leaf's docstring priced itself at "two identifications,
and neither is `rfl`", and it was right about both; what it could not know is that one of
them costs **three lines** because of the BASE.
Two different `ZMod q`-algebra structures on one residue field were in play — this file's
(through `Spec.preimage` of `fromSpecResidueField ≫ strX`) and `CurveDimension.lean`'s
(through `ΓSpecIso.inv ≫ appTop ≫ Γevaluation`).  Comparing them looks like an `appTop`
naturality computation.  It is not:
    Algebra.algebra_ext _ _ fun r => congrArg (fun h => h r) (RingHom.ext_zmod _ _)
**`ZMod q` is a quotient of `ℤ`, so `ZMod q →+* A` is a SUBSINGLETON, so `Algebra (ZMod q) A`
is one too.**  Every `ZMod q`-algebra structure on a ring is *the* one, and any two
constructions of it are equal without looking at either.  The same holds verbatim for `ℤ`,
`ℚ` (`RingHom.ext_rat`), and any prime field.
**So before writing a naturality square to compare two structure maps, check what the BASE
is.**  In this development that is `ZMod q`, `ℚ` or `ℤ` far more often than not, and the
comparison is then free.  The mirror of the already-recorded rule that
`Subsingleton (Z ⟶ S)` at `SpecQ`/`SpecF` pins a classifying morphism — same phenomenon, one
level down, on ring maps instead of scheme maps.
### `κ(pt) = K` for `Spec K` is a ONE-SIDED INVERSE, not a `FractionRing` computation
The second identification wanted "the residue field of `Spec K` at its unique point IS `K`",
i.e. bijectivity of `γ := Spec.preimage ((Spec (of K)).fromSpecResidueField y)`.  The obvious
route is `Spec.residueFieldIso` down to `Ideal.ResidueField ⊥ = FractionRing (K ⧸ ⊥)` and then
`IsFractionRing.self_iff_surjective`.  Much cheaper:
* `Scheme.SpecToEquivOfField K (Spec (of K))` applied to `𝟙` gives, by `symm_apply_apply`, a
  `δ` with `Spec.map δ ≫ fromSpecResidueField pt = 𝟙`; `Spec.map_injective` turns that into
  `γ ≫ δ = 𝟙` in `CommRingCat`;
* `δ` is a ring map out of a FIELD, hence injective, and `δ (γ (δ b)) = δ b` then gives
  `γ (δ b) = b` — so `γ` is surjective, and injective for the same field reason.
**A one-sided inverse plus injectivity of the OTHER map is a full bijection whenever both are
field homomorphisms**, and in this development almost everything in sight is.  Reach for that
before any localisation computation.
Two mechanical notes from the same proof, both about the point of `Spec K`:
* to move a statement from an arbitrary point `y` to the canonical one, `obtain` the canonical
  data as an `∃` FIRST so that its point is a genuine local variable, then
  `obtain rfl : pt = y := Subsingleton.elim _ _`.  `subst` eliminates one of the two names and
  it is not always the one you expect — after it, refer to whichever survives (the error is
  `Unknown identifier`, at the first later use, and it is the whole diagnosis);
* `Subsingleton (Spec (CommRingCat.of K))` is `inferInstanceAs (Subsingleton (PrimeSpectrum K))`.
### `Specializes` coerces to `≤`, and then `lt_of_le_of_ne` reads the FILTER order
The points of a scheme carry a `Preorder` (this file already records that `PartialOrder` is
absent).  The new half: `hspec : z ⤳ y` IS `y ≤ z`, but passing `hspec` directly to
`lt_of_le_of_ne` makes Lean unify against `Specializes`'s own definition `nhds z ≤ nhds y` and
demand `nhds z ≠ nhds y`.  **Bind it first** — `have hle : y ≤ z := hspec` — and then use the
PREORDER form, since `lt_of_le_of_ne` needs a `PartialOrder` that does not exist here:
    have hlt : y < z := lt_of_le_not_ge hle fun h => hne ((hspec.antisymm h).eq).symm
`Specializes.antisymm … .eq` is the `T0` step, exactly as the standing note says.
### `#print axioms` FROM AN IMPORTER worked here, and it is 20 s against an 18-minute rebuild
The standing rule is that `#print axioms` must be appended to the file that DECLARES the name,
because the module system elides imported proof bodies.  Measured on `Interface.lean`
(83 000 lines, `@[expose] public section`): a two-line scratch that `public import`s it and
`#print axioms`es four of its declarations returned
`[propext, Classical.choice, Quot.sound]` for all four, in about twenty seconds.  **Try the
importer first** — if it comes back with a real axiom list it has answered the question, and
only if it comes back empty do you owe the in-file version and its full re-elaboration.
### And the accounting that makes a closure checkable rather than asserted
A leaf closed with no new leaf should be reported as a DECLARATION-NAME diff of the two
`sorry` sets, not as a count:
    git show HEAD:<file> > /tmp/old.lean
    # for each bare `sorry` line, walk BACKWARDS to the nearest declaration header, in both
    # files, and diff the two name lists
    # here: removed [eulerCount_eq_effectiveDivisorCount], added []
A count of `16 → 15` is consistent with "one closed" and also with "one closed and one opened
somewhere else"; the name diff is not.
