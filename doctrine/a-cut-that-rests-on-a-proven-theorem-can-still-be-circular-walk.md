## A CUT THAT RESTS ON A **PROVEN** THEOREM CAN STILL BE CIRCULAR — WALK ITS CALL GRAPH
(2026-08-02, `flt-lean-113`, `ModularCurve/X1.lean`. Frontier 24 → 23, no new leaves, no
mathematics.) The section further down — TWO RIVAL CUTS OF ONE CLUSTER, BOTH MERGED — covers
a cycle *manufactured by a merge* between two branches, one of which predated a re-cut. There
is a second way to get the identical defect, it needs **no merge, one agent and one branch**,
and none of the merge-damage scans can see it.
`exists_isFineGamma1Moduli` (X1.lean) was cut on 2026-07-31 into a leaf
(`exists_gamma1UniversalFamily_of_atlas`) plus an assembly, over the **PROVEN**
`exists_gamma1AffineModel`. The cutter's check — *is my input available?* — passed, correctly.
What nobody ran is the call graph of that proven input:
    exists_gamma1AffineModel -> exists_gamma1GITPresentation
      -> exists_gamma1Rigidification -> exists_gamma1RigidifiedModuli
      -> isAffine_of_gamma1RigidifiedModuliScheme
      -> exists_isAffine_gamma1RigidifiedModuliScheme
      -> exists_isAffine_gamma1ModuliScheme          <- an OPEN LEAF, 6600 lines above
So the new leaf existed only to re-derive Katz–Mazur 4.7.1 for `[Γ₁(N)]` from a chain that
already assumes it, and the file owed one citation **twice**.
**Every instrument reported two ordinary open leaves.** Both emitted an honest
`declaration uses` warning; both passed the three-part ownership test; `dupstmt.py` and
`xdup.py` are silent because the two statements share no identifier (one is
`∃ R : Gamma1ModuliScheme N (Spec K), IsAffine R.Y`, the other is
`∃ dY, ∀ g d, Nonempty (IsBaseChangeOfGamma1 (A.classify g d).1 d dY)`). The ONLY artefact
that shows it is the call graph, and nothing in the fleet computes one.
**So the check, and it is twenty lines of Python over comment-stripped source:** before
writing a cut, take every theorem your new proof will consume and ask whether its transitive
callees include an OPEN LEAF in the same file. Declare/use per declaration, attribute each use
to its enclosing declaration by walking backwards to the nearest header, BFS. **"Proven" is
not "independent": a proven input that bottoms out in your sibling IS your sibling.**
**Resolving one you find** — the rule is the existing one and it is decidable: keep the
arrangement whose root is IMPLIED by the rival's root, since that leaves the file owing
strictly less. Here `exists_isAffine_gamma1ModuliScheme` implies the whole atlas route's
conclusion in **eleven lines**, while the atlas route implies nothing without an atlas it can
only obtain from that same leaf. Route B was deleted; `−1` leaf for no mathematics.
Three riders, each of which decided something here:
* **Check the loser's UNIQUE hypotheses before deleting — one of them is usually why the
  deletion is free.** The deleted assembly needed `∀ Z, Subsingleton (Z ⟶ S)` and spent it in
  exactly ONE line, to get `m₁ ≫ str = m₂ ≫ str` for two rival classifying maps. The
  survivor's `∃!` ranges over morphisms satisfying `m ≫ strY = g`, so it carries that equation
  in its own predicate and the step is free. **A general-base statement can be cheaper than
  the special-base one it looks weaker than**, when the "over `S`" clause is inside the
  quantifier rather than imported from the base.
* **Check whether the cut could ever be non-circular, and say so.** An atlas here is not
  merely unavailable upstream — `Gamma1Atlas` carries the rigidified moduli scheme
  `𝔐([Γ₁(N)], [Γ(n)])` as a FIELD, so an atlas is strictly MORE than the leaf asks for and no
  reordering can help. Write that on the surviving leaf, or the same cut gets made again.
* **Record the cycle, the direction chosen, and `git show <sha>^` in the SURVIVOR's
  docstring.** A deleted leaf with a careful audit is unrecoverable in practice once nobody
  remembers it existed, and a deletion with no stated reason reads as the class-six dropped
  payload.
