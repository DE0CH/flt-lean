## A `∀`-SHAPED GEOMETRIC LEAF IS A UNIQUENESS THEOREM PLUS AN `∃`-SHAPED CITATION
(2026-08-02, `flt-lean-49`, `exists_isX0Compactification_sexticThirtySeven` in
`FreyCurve/MazurTorsion.lean`.)  This tree states citation leaves over an ARBITRARY
object carrying a geometric property, because that is what the consumer has:
    (h : IsSmoothCompactification (planeCurveStrQ F) strX uX) :
      ∃ Y strY jY, Nonempty (IsX0Compactification 37 strX strY jY)
— *"given ANY smooth compactification `X` of the affine sextic, `X` is `X_0(37)`"*.
The `∀` is right for the consumer and wrong for the prover: no book proves anything
about every such `X`, they build ONE model and read the property off it.  So the
leaf silently owes the whole comparison theory on top of the mathematics.
**The decomposition is always the same three pieces**, and only the middle one is a
leaf:
1. **UNIQUENESS of the arbitrary object** — general algebraic geometry, provable,
   and reusable by every later leaf of the same shape;
2. the citation, restated **existentially over ONE object** — what the literature
   supplies;
3. **TRANSPORT** of the conclusion along the isomorphism (1) produces.
Here (1) is `exists_inverse_of_isSmoothCompactification` (two smooth
compactifications of one integral scheme over a field are isomorphic over it,
compatibly with the immersions — ~40 lines, three applications of one theorem), (2)
is `exists_openImmersion_x0ThirtySeven` (*the affine sextic is an open subscheme of
SOME `X_0(37)`*), and (3) was **already PROVEN**: `IsX0Compactification.ofInverse`
in `X0.lean`, written months earlier for the `𝔽_ℓ` uniqueness argument.  **Grep for
the transport before writing one** — a structure that has ever been compared with
itself over another base already has it.
**Report it as a RECUT: the count does not move, `1 → 1`.**  What changes is that
the residue asks for ONE MORPHISM and mentions no properness, no smoothness, no
density, no finiteness of a complement, and no universal quantifier — and that the
uniqueness theorem is banked for good.  Judge it by what is LEFT in the leaf.
**Three riders, each of which decided something here.**
* **Prefer the `∃` form and say why.**  The `∀` form is EQUIVALENT (same uniqueness
  theorem, plus initiality of the coarse moduli space for the open part) and is
  strictly more to prove.  Write the equivalence into the docstring so the next
  reader does not "fix" the leaf into the stronger shape.
* **Do not ask the leaf for the PACKAGE.**  `IsSmoothCompactification` has six
  fields; four of them (`isProper`, `smooth`, `isDominant`, `finite_compl`) are
  free once the object is an `X_0(N)` — the first two are its own fields, and the
  other two are "a nonempty open of an irreducible space is dense" plus
  `finite_compl_range_of_topologicalKrullDim_le_one`.  Proving that once
  (`isSmoothCompactification_of_isX0Compactification`) is what lets the leaf ask
  for a bare open immersion.  A leaf that asks for a package is a leaf whose every
  future owner re-derives the same four clauses.
* **The packaged form of your uniqueness input may carry a hypothesis you cannot
  supply — use the theorem it was packaged FROM.**  `exists_unique_extension_of_`
  `isSmoothProperCurve` asks for `GeometricallyConnected strX`, which
  `IsSmoothCompactification` does not carry and which for the sextic would have
  meant proving `y² − f` geometrically irreducible over `ℚ̄`.  Its own proof spends
  that hypothesis on ONE line, to get `IsIntegral X`, and the inner
  `exists_unique_extension_of_valuationRing_stalk_of_isOpenImmersion` takes
  `[IsIntegral X]` directly — which is free from `IsIntegral U` plus
  `isReduced_of_smooth_over_field` plus `irreducibleSpace_of_denseRange`.  This is
  the standing "READ THE LEMMA THE COROLLARY CAME FROM" rule firing on a
  GEOMETRIC hypothesis; it is worth checking every time a hypothesis you cannot
  discharge appears in a theorem whose conclusion is exactly what you want.
