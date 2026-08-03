## `Algebra.FormallySmooth` IS A CONJUNCTION AT THIS PIN — a formal-smoothness leaf splits with `refine ⟨?_, ?_⟩`
(Same task, and it is what turned a leaf priced as "build a theory" into two named
citations in an afternoon.)  It is natural to think of formal smoothness as the
LIFTING property, and to conclude that a descent statement about it needs a
lifting/torsor/obstruction argument.  At this pin that is backwards:
    class Algebra.FormallySmooth : Prop where
      projective_kaehlerDifferential : Module.Projective A Ω[A⁄R]
      subsingleton_h1Cotangent       : Subsingleton (H1Cotangent R A)
(`Mathlib/RingTheory/Smooth/Basic.lean`; `iff_comp_surjective` is a THEOREM about it,
not the definition).  So **any leaf whose conclusion is `FormallySmooth` splits along
that conjunction with nothing left over**, and in practice the two halves descend by
completely different mechanisms — which is what makes the split worth taking even
when it raises the leaf count.
`Fermat.formallySmooth_of_comp_of_faithfullyFlat` (`R → S → T`, `S → T` faithfully
flat and formally smooth, `R → T` formally smooth ⟹ `R → S` formally smooth) went
`1 → 2` this way and both residues became literature citations:
* the `H¹` half is the LEFT END of Jacobi–Zariski.  Mathlib proves exactness at the
  middle term only — `Algebra.H1Cotangent.exact_liftBaseChange_map_of_flat`, Stacks
  `00S2` — because the NAIVE cotangent complex has no `H₂` to continue with, and the
  file's own header says so.  `FormallySmooth S T` is precisely what makes
  `H₂(L_{T/S}) = 0`;
* the `Ω` half is proven outright here: `H¹(L_{T/S}) = 0` makes
  `KaehlerDifferential.mapBaseChange` injective by
  `Algebra.H1Cotangent.exact_δ_mapBaseChange`; `Ω[T⁄S]` projective gives a section of
  `Ω[T⁄R] ↠ Ω[T⁄S]`; `Function.Exact.split_tfae` converts that section into a
  RETRACTION; `Module.Projective.of_split` then makes `T ⊗_S Ω[S⁄R]` projective over
  `T`.  The residue is descent of projectivity along `S → T`, i.e. Raynaud–Gruson /
  Stacks `058B` — the same statement mathlib names as the obstruction to its own
  `proof_wanted` in `Mathlib/RingTheory/Etale/Descent.lean`.
**The reusable toolkit, since none of it is obvious from the class name**:
`Algebra.H1Cotangent.exact_δ_mapBaseChange`,
`KaehlerDifferential.exact_mapBaseChange_map`, `KaehlerDifferential.map_surjective`,
`Function.Exact.split_tfae` (section ⟺ retraction ⟺ direct-sum splitting),
`Module.Projective.of_split`, `Module.projective_lifting_property`,
`Module.FaithfullyFlat.lTensor_reflects_triviality` (`Subsingleton (T ⊗ M) ⟹
Subsingleton M`), `Module.Flat.projective_of_finitePresentation`.  The whole
decomposition above compiled on the FIRST attempt in a 100-line module that
elaborates in four seconds.
**What is NOT at this pin, measured rather than assumed** — three absences that
between them decide which descent statements are reachable:
* **Serre's criterion, in either direction.**  `grep -rn IsRegularLocalRing
  .lake/packages/mathlib/Mathlib` returns only `RegularLocalRing/{Defs,Polynomial}`;
  `RingTheory/Regular/ProjectiveDimension.lean` has `projectiveDimension_quotient_eq_length`
  for a regular *sequence* and nothing else; there is no `Auslander`, no `Buchsbaum`.
  So *"`A → B` flat local of Noetherian local rings, `B` regular ⟹ `A` regular"*
  (Matsumura 23.7, Stacks `00OJ`) is out of reach, and with it the FLAT case of
  Stacks `02VL`.  **Adding `PerfectField`/`CharZero` does not help** — the regularity
  descent is needed over the residue field whatever its characteristic, which is the
  trap in the natural reading of `Algebra.IsSmoothAt.of_formallySmooth_fiber`.
* **Raynaud–Gruson** (projectivity descends along faithfully flat) — absent, and
  recorded as such by mathlib itself.
* **Flat descent along a faithfully flat map** — also absent, which matters because it
  is the cheap escape from the previous item: for a FINITELY PRESENTED module
  projectivity is flatness (`Module.Flat.projective_of_finitePresentation`), so a
  successor who threads `[Module.FinitePresentation S Ω[S⁄R]]` needs only the ideal
  criterion for flatness plus `Module.FaithfullyFlat.lTensor_injective_iff_injective`.
Corollary about `Algebra.IsSmoothAt.of_formallySmooth_fiber`
(`Mathlib/RingTheory/Smooth/Fiber.lean`), because it is the route every audit of this
node reaches for first: it is real and it is proven, but its fibre clause asks for
formal smoothness of `𝓀[R] ⊗_R S` over `𝓀[R]`, and over a perfect field that is
regularity of a LOCAL ring — so it converts a smoothness-descent problem into a
regularity-descent problem, i.e. into the first absence above.  It is the right tool
for ASCENT and the wrong one for descent along the source.
