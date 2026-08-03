## A STRUCTURE FIELD QUANTIFIED OVER THE WHOLE GALOIS GROUP IS ONE CHEBOTAREV STEP AWAY FROM ITS LOCAL FORM — WEAKEN THE FIELD, RE-DERIVE IT ABOVE THE LEAF
(2026-08-02, `flt-lean-81`, on `nonempty_hilbertHeckeAlgebraAtLevel_of_moretBaillySeed`
A leaf whose job is to PRODUCE a bundled structure is priced by its hardest FIELD, and
this development's arithmetic structures routinely carry one field that is a GLOBAL
statement — `∀ g : Γ F, …` — where the citation the leaf names proves only the LOCAL one,
at the unramified places. `HilbertHeckeAlgebraAtLevel.residT` was exactly that: Carayol
1986 §0.9 gives local–global compatibility at good `w`, and the field demanded the
identity at every element of the absolute Galois group. The gap is Chebotarev plus
Brauer–Nesbitt, and it is **nobody's citation** — it is a step the leaf's owner would
have had to notice and prove on the way past.
**The repair is to weaken the FIELD and re-derive the old form as a THEOREM above the
leaf.** Here `residT` became `residTgood : ∀ w ∉ bad, (ρT.charFrob w).map πT = …`, and
`HilbertHeckeAlgebraAtLevel.residT` is now a proven theorem of the same name taking the
three hypotheses the upgrade needs (`hℓ5`, `hdim`, `hirrF`). Count `1 → 1`; what left the
leaf is a density argument, and the residue is stated in the shape the literature states
it in.
**Four checks make it safe, and each is one command:**
* **Who READS the field.** `HilbertHeckeAlgebraAtLevel` occurs in exactly one section of
  one file, and both declarations that touch it are `sorry`, so no `H.residT` projection
  and no structure literal had to change. A field weakening is cheap exactly when the
  structure's only consumers are open leaves — and that is common for an intermediate
  object introduced by a recent cut.
* **Whether the DOWNSTREAM consumer is made harder.** Weakening a field makes the
  producer's job easier and the consumer's harder, so the derived theorem must be usable
  by the consumer. Diff its binder list against the derived theorem's arguments: `(LL)`
  here already carried `hℓ5`, `hdim`, `hirrF` and `[DiscreteTopology k]`, so it is not
  made harder by one character.
* **Whether the upgrade's ingredients are in YOUR import cone**, not merely in the tree.
  The `F`-level twin `forall_charpoly_map_eq_of_charFrob_map_eq_over_base` exists — in
  `Modularity/KhareWintenberger.lean`, which IMPORTS this module, so it is unusable here
  and a grep for it is actively misleading. Every ingredient of it, however, was already
  reachable: `framePushforward`/`charpoly_framePushforward` in this module,
  `GaloisRep.charFrob_eq_charpoly_globalFrob` from a `public import` of `Chebotarev.lean`,
  and `exists_conj_of_charFrob_eq_away_of_two_ne_zero` from a NON-public import of
  `BrauerNesbittConjugacy.lean`. **Grep for the INGREDIENTS, not for the twin.**
* **Whether the reduction map is CONTINUOUS**, because the upgrade needs to push the
  representation along it. It always is and it is never a field: `πT` is a surjection onto
  a field from a local ring, so `ker πT = 𝔪_T`, which `isAdic` makes open, and
  `continuous_of_isOpen_ker_of_discreteTopology` finishes. That four-line idiom is already
  used twice in this file for `HilbertDeformationDatum.π`; copy it rather than re-deriving.
**The generalisable tell:** read a structure's fields and ask, of each, *at what set is the
citation stated?* A field quantified over `Γ F`, over all ideals, over all test schemes, or
over all `n`, when the theorem behind it is about unramified places, principal ideals, affine
test schemes or one `n`, is a field whose global form the leaf is being asked to prove for
free. Those are the fields to weaken.
* **A non-public import reaches a theorem's proof body but NOT a scratch module that
  imports the file.** The first scratch failed with exactly one error — `Unknown identifier
  exists_conj_of_charFrob_eq_away_of_two_ne_zero` — which reads as "that lemma is not in the
  cone" and is not: it is in the target's cone, non-publicly. Add the target's non-`public`
  imports to the scratch explicitly (already recorded once, and it cost a round again here).
* **A scratch against the release snapshot's olean was 7 s per round against a 39 000-line
  module.** `git diff --stat $(cat ~/.flt-release-lake/sha) HEAD -- 'Fermat/**'` was EMPTY, so
  `rsync -a --delete ~/.flt-release-lake/build/ /scratch/chend-flt/flt-lean-N/.lake/build/`
  made every olean current and no build was needed before the final one. Run that diff first;
  when it is empty the whole scratch loop is free.
