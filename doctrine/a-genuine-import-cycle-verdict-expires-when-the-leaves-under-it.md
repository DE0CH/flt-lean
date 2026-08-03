## A "GENUINE IMPORT CYCLE" VERDICT EXPIRES WHEN THE LEAVES UNDER IT CLOSE
Same day, same task, and it is the more useful half. `flt-hoist-genusone.py` hoists only the
genus-one branch, and says why: `_thirtySeven` and `_classNumberOne` reach
`exists_endMinpoly_of_stable_cyclic_mazurLevel`, hence Mazur's isogeny-character descent, hence
`exists_goodReductionModel_of_surjective` / `exists_neronExtension` in
`Fermat/FLT/Mathlib/AlgebraicGeometry/NeronModel.lean`, whose line 8 is
`public import Fermat.FLT.ModularCurve.X0` — "a genuine import cycle, with no sorried link to
cut it at".
**That was true of the tree it was measured on and is not true of `merger`.** Ten of the
eighteen leaves in the two hoisted namespaces closed in the day between, and the proofs that
landed did not take the route the verdict assumed. A comment-stripped, isalnum-tokenised
transitive closure of the whole remaining `MazurIsogenyPrimeJ` tail on `merger`
(197 seed declarations, 224 in closure) needs **27 declarations outside it, all inside
`MazurTorsion.lean`, and none of them reaches `exists_abelianGoodReductionModel`** — hence none
reaches `NeronModel.lean`. The cited cycle is gone.
The general shape, and it is the mirror of the `sorryAx`-cone rule: **an open leaf's body
contributes no dependencies, so a cycle verdict taken while it was open is a claim about its
INTENDED proof, not its actual one.** Prose that says "there is no route" ages exactly as badly
as prose that says "still open, owned elsewhere", and for the same reason — it is a hypothesis
about a frontier that moved. Re-measure a cycle claim against the branch where the proofs
EXIST, never against the one where the leaves are open.
What actually blocks the tail now is smaller and nobody had looked: it references
`Fermat.IsBaseChangeOfGamma1.{refl, comp, along_injective}`, declared in `X1.lean`, which also
`public import`s `X0.lean`. Their downward closure inside `X1.lean` is **eleven declarations**
(`RelPoint.ofSection`, `PointOfExactOrder`, `Gamma1Datum`, `IsBaseChangeOfGamma1` and the
namespace block), roughly 270 lines. So the remaining two Mazur-Theorem-1 leaves are one
270-line relocation plus a replay away, not "no route exists".

### CORRECTION (2026-07-31, `flt-lean-247`): THE `X1` VERDICT IS ITSELF A FALSE POSITIVE, AND THE REAL BLOCKER IS A CYCLE THE SCANNER COULD NOT SEE

The paragraph immediately above is wrong twice, and both errors are instructive because
the section's own thesis — re-measure, do not inherit — is what catches them.

**1. `IsBaseChangeOfGamma1` is not referenced at all.** The token
`IsBaseChangeOfGamma1` occurs **zero** times in the 258-declaration closure.
`flt-cyclecheck.py` matched on the SHORT names `refl`, `comp`, `along_injective`, whose
real referents are `Equiv.refl`, `AlgHom.comp` and the block's **own**
`MazurIsogenyPrimeJ.IsEllipticIsoOf.along_injective`; the `Interface.lean` hit
`Modularity.val_neg` is `Units.val_neg`. Verified by instantiating each occurrence. So
"one 270-line relocation away" was an invitation to relocate something nothing needs.
That scanner now carries a PREFIX GUARD, and — this is the part worth copying — it
requires the **innermost** namespace component, not *some* component: this project puts
almost everything under `Fermat`, so an `any()` over the components passes on `Fermat`
alone and suppresses nothing. Suppressed hits are still printed, in their own list.

**2. THE BLOCKER IS A CYCLE THROUGH THE TARGET LEAF ITSELF, AND NO SCANNER IN THIS TREE
WAS LOOKING FOR ONE.** Every cycle check here — including this section — asks *does the
closure reach a module that IMPORTS the destination*. That is one half of the question,
and it is the half answerable by reading other files. The other half is *does the closure
reach the destination's OWN material declared BELOW where the block would land*, and the
worst case of it is that the closure reaches **the very leaf the hoist exists to close**.
Here it does, along a seven-link chain of genuine call sites:

    exists_jMap_classNumberOne → card_le_of_isogenyPrimeHigherGenus → card_y0Le_classNumberOne
      → nonempty_isCMByRamifiedMaximalOrder_of_classify_eq → …_of_isBaseChangeOf
      → …_of_isBaseChangeOf_of_endMinpoly → exists_relSchemeEnd_of_endMinpoly_of_weierstrassModel
      → exists_endMinpoly_of_stable_cyclic_isolatedJ
      → **`Fermat.mem_isolatedJInvariants_of_stable_classNumberOne`** (MazurTorsion.lean:41417)

`card_y0Le_classNumberOne`'s step **2** is literally commented *"Mazur: each of them is a
CM datum"*. So the ordering constraints are contradictory and **the hoist is impossible
under every arrangement of files** — it would survive merging the two modules into one.
`flt-cyclecheck.py` grew a section 4, DEST-SIDE FORWARD REFERENCES, which reports exactly
this; run it with `--at <the insertion line>`.

**The generalisable rules, and the second is the one this cost a day on:**

* **A "PROVEN" theorem next door is not independent evidence for the leaf it would close
  — check whether its proof CONSUMES that leaf.** `card_y0Le_classNumberOne` is proven
  *relative to* the node it is offered as a route to, so the whole cluster is
  `sorryAx`-tainted through it. This is the [[flt-a-leaf-can-contain-a-leaf]] trap in the
  direction nobody checks: not "my leaf secretly contains another", but "the theorem
  offered as my leaf's proof secretly contains my leaf".
* **A hoist has TWO cycle questions and the tooling only ever asked one.** Before pricing
  any relocation, grep the closure for the target's OWN name. It is one command and it is
  the difference between a three-hour measurement and a three-minute one.

**And the split verdict this produced, since a cost wall is a result:** the same
measurement shows `p = 37` IS free. `card_le_of_isogenyPrimeHigherGenus`'s `37` branch
calls only `card_y0Le_thirtySeven`, whose 47-declaration closure touches no leaf of
`X0.lean`; splitting that theorem by level gives `exists_jMap_thirtySeven` a closure of
**57 declarations / 3117 lines, all inside the tail, zero forward references**. So of the
two leaves this section promised, one is a bounded relocation and the other cannot be done
at all until `card_y0Le_classNumberOne` is cut back to a leaf — which is the honest cut
anyway, since `#Y_0(p)(ℚ) ≤ 1` at `p ∈ {43,67,163}` IS Mazur's Eisenstein-ideal descent.

**THE `p = 37` HALF WAS THEN DONE, SAME RUN, GREEN FIRST TRY** (`flt-hoist-thirtyseven.py`;
2906 lines, 56 declarations, four contiguous runs). `Fermat.mem_isolatedJInvariants_of_stable_thirtySeven`
— Mazur's Theorem 1 at `37` — is PROVEN. Frontier: X0 `101 → 104`, MazurTorsion `37 → 33`,
tree `138 → 137`. **Report a hoist's count as BOTH files plus the tree total**: `+3` in the
destination reads as a regression on its own, and it is four leaves arriving from next door
against one closing.

Two things made it green first try and are worth copying to any hoist:

* **assert the three properties in the SCRIPT, not in the report** — that each run is
  gap-free (no declaration inside a moved range is outside the closure), that the runs cover
  the closure, and that no forward reference into the destination exists. The script refuses
  to write otherwise, so a mis-specified range cannot reach a build;
* **the purity receipt is a line-multiset difference ACROSS the two files**:
  `Counter(pre_src) − Counter(post_src)` minus `Counter(post_dst) − Counter(pre_dst)` must be
  exactly your intended edits. Here it was two lines — the re-pointed call site and one
  `sorry` — against 2906 moved. That is far stronger than reading a 3000-line diff, and it
  catches a dropped or mangled line that `git diff --stat` cannot.
