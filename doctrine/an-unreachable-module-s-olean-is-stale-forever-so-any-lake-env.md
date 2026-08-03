## AN UNREACHABLE MODULE'S OLEAN IS STALE **FOREVER** — so any `lake env lean` test that loads it silently tests a tree that no longer exists
(2026-08-01, `flt-lean-263`. Nearly inverted the whole task in the first five minutes.)
The doctrine already says `lake env lean` does not rebuild imports, and that a
freshly repointed worktree has an inconsistent olean set. Both are about oleans
that are *temporarily* behind and that the next `lake build` fixes. There is a
case where the staleness is **permanent and self-renewing**, and it is exactly
the case in which you are most likely to run a co-import probe:
**`lake build` builds the ROOT'S IMPORT CLOSURE. A module outside that closure is
never built again — so whatever olean it has on disk is frozen at the last
release in which it *was* reachable, and no amount of building fixes it.**
Concretely: release 31 dropped `X0.lean`'s import of
`Mathlib/AlgebraicGeometry/CurveDivisorDegree.lean` because it collided with
`PrincipalDivisorDegree.lean`. That made `CurveDivisorDegree` the one module
under `Fermat/` outside the closure. Its olean stayed on disk, dated to the
release before the drop. A two-line probe —
    module
    public import …PrincipalDivisorDegree
    public import …CurveDivisorDegree
— then returned **`EXIT=0`, no output**, i.e. *"there is no collision"*. The
collision was real and is in the SOURCES; the probe had loaded the frozen olean,
which predates the duplicate pair. A green co-import probe is therefore **not
evidence that two modules co-import** unless you have first rebuilt both.
**The check that separates the two cases costs one command**, and it is worth
running before believing ANY probe involving a module you are not actively
building:
    # is the module in the root's closure?  (BFS the ^(public )?import Fermat…
    # edges from `Fermat`, and ASSERT each visited file exists)
    # if it is NOT, its olean is arbitrarily old — `lake build <that module>` first.
The tell that sent me back to check was structural rather than lucky: the
*sources* plainly declared `Scheme.ord_one` twice under the same namespace
(`namespace AlgebraicGeometry` → `namespace Scheme` in one file, `lemma
Scheme.ord_one` inside `namespace AlgebraicGeometry` in the other), so a passing
probe contradicted a fact I could read. **When a probe disagrees with the source,
the probe is testing a different tree.**
### The reconciliation itself: a "they collide, so the import is DELIBERATELY DROPPED" note is a claim to RE-MEASURE, and the collision is usually tiny
That import comment was 16 lines long, dated, careful, and correct about the
collision. What it never said is **how big the collision was**. A qualified
declaration-name intersection of the two files is
    AlgebraicGeometry.Scheme.ord_one    AlgebraicGeometry.Scheme.ord_inv
and **nothing else** — two lemmas, character-for-character identical on both
sides, `@[simp]` on `ord_one` on both sides. So the repair is: delete the two
from one file, have it `public import` the other (neither was in the other's
import closure, so no cycle), and restore the dropped edge. Fifteen lines, one
4-second module build.
The cost of not measuring it was a **leaf that could not be cut at all**:
`birationalOver_affineLine_of_relPicEquiv_sectionIdeal` in `X0.lean` splits into
a sheaf half and a divisor half, and the divisor half
(`birationalOver_affineLine_of_ord_eq_sub`) is PROVEN — in the module `X0.lean`
was not allowed to import. Restoring the edge turned that leaf into a 1 → 1 recut
whose assembly compiled first try.
**So: when a docstring says an import was dropped because two modules collide,
compute the intersection before accepting it.** Distinguish the QUALIFIED
intersection (Lean's actual condition, and the only one that is an error) from a
LAST-COMPONENT match — this tree has ~7000 of the latter and they are a review
list, not defects. And note the deletion is safe in exactly the case measured
here: both copies PROVEN and textually identical, so nothing is being chosen
between.
**Rider: restoring the edge puts the orphan back in the root closure, and that
RAISES the reported frontier — as disclosure, not regression.** `CurveDivisorDegree`
carries 3 `sorry`s that no build has counted since release 31. Release 33's
handover recorded `frontier.py` reporting 380 rows against 377 compiler warnings
and correctly diagnosed the three extras as this module; that discrepancy is now
gone, because the compiler can see them. **Say so in the commit, or a `+3` reads
as a regression.** With the edge restored, **every one of the 409 modules under
`Fermat/` is now in the root closure** — the fourth invisibility class is, for the
moment, empty.
### The closure scan itself has a trap, and it manufactures a PHANTOM ORPHAN
Measuring the above, my first scan reported
`Fermat/FLT/Mathlib/RingTheory/Localization/BaseChange.lean` as a second orphan.
It is not — it is imported by `Fermat/FLT/DedekindDomain/IntegralClosure.lean`,
whose import line reads
    public import Fermat.FLT.Mathlib.RingTheory.Localization.BaseChange -- removing this breaks a simp proof
and my regex was `^\s*(?:public\s+)?import\s+(Fermat[\w.]*)\s*$` — **anchored at
end of line, so a trailing comment silently drops the edge**. This tree annotates
imports constantly (the whole point of the `CurveDivisorDegree` note above is an
import comment), so an end-anchored import regex will under-report the closure and
invent orphans. **Strip `--` comments before matching, and do not anchor at `$`.**
The failure is silent and it errs toward the answer you were looking for, which is
the same shape as the standing rule that a closure BFS must ASSERT each visited
file exists rather than swallowing a `FileNotFoundError`.
