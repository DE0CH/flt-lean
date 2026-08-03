## CORRECTING CLAUDE.md DOES NOT CORRECT THE DOCSTRING — AND THE DOCSTRING IS WHAT GENERATES TASK PROMPTS
(2026-08-01, `flt-lean-142`, on `exists_inertiaSet_geomPt` in `ModularCurve/X0.lean`.)
This file already carries a section — *"AN ABSENCE AUDIT THAT GREPS THE PIN AND NAMES
*ONE* PROJECT MODULE READS AS A PROJECT-WIDE CHECK"* — whose worked example is **this
exact leaf's sibling**, and which says in as many words that the leaf's audit sends
readers to `Modularity/{AbelianScheme,AbelianSchemeIsogeny}.lean` and that *"the actual
home, `Fermat/FLT/Mathlib/AlgebraicGeometry/NeronModel.lean` … is named nowhere in that
docstring"*. That correction landed in CLAUDE.md. **The docstring was never edited.** So
the wrong audit was still sitting on the leaf, the loop generated a task prompt FROM the
docstring, and the prompt handed me the refuted paragraph verbatim — capital letters,
`grep` results and all — as the premise of the task.
**A lesson recorded only in CLAUDE.md does not reach the next agent working that leaf,
because the prompt is built from the leaf, not from CLAUDE.md.** So when you correct an
audit, correct it IN THE DOCSTRING as well, in place. That is the only copy the task
generator reads. Doing one and not the other is how a refuted claim gets re-issued as an
instruction, and it cost this task its entire stated premise.
### And the same audit was wrong a THIRD way: the machinery was in the SAME FILE, BELOW
The corrected verdict ("it's in `NeronModel.lean`, which is downstream, hence unusable")
is also not the whole story. `X0.lean` contains its own copy — `HasGoodAbelianModelAtBase`
(the good-reduction predicate, with the additivity clause that pins the group law), plus
`SpecLoc`, `SpecLoc.generic`, `IsFibreIdent` and a PROVEN `exists_isReductionBase` — all
of them declared **twenty to fifty-six thousand lines BELOW the leaf that needs them.**
That is invisible to every phrasing of the question an auditor naturally asks:
* `grep` for the concept in the consumer's vocabulary ("Néron", "good reduction", "model
  over `ℤ_q`") finds prose, because the predicate is named for its CLAUSE, not its use;
* `#check` from a scratch module SUCCEEDS, because a scratch imports the whole file and
  sees every declaration regardless of order — **the one thing a scratch structurally
  cannot check**;
* and the leaf's own docstring said the object *"cannot even be STATED"*, which is true
  at line 48166 and false at line 104281.
**So add one line to the standing absence checklist: `grep -n` the concept in YOUR OWN
FILE and compare the LINE NUMBER against your leaf's.** "Absent" and "declared below me"
produce identical evidence from every tool except that comparison.
### Deciding hoist-vs-rewrite is two commands, and it beat the estimate by two orders of magnitude
The task was budgeted as a subtree build ("expect to DESIGN AND STATE new nodes", a model
over `Spec ℤ_q` from scratch). What it actually needed:
    ./flt-hoistcheck.py <file> --block A B --to L      # per block: does it use anything it jumps over?
    python3 tools/merge/blockmove.py <file> A:B:L ...  # atomic, ORIGINAL coordinates, permutation-checked
Four blocks, ~170 lines total, `HITS: 0` for three of them and for the fourth only the
other three. `blockmove.py` applies them all in original coordinates — so the specs cannot
invalidate each other's line numbers — and refuses to write unless the sorted line
multiset is unchanged, which is the exact receipt for a pure move. The alternative side of
the move (relocating the leaf and its consumer chain past line 104281) was thousands of
lines. **Measure both sides before believing either; the machinery side is usually much
smaller than it looks, because a predicate is small and its consumers are not.**
Two things `hoistcheck` cannot see and that must be eyeballed, both of which mattered here:
the destination's SCOPE (two of the four blocks came out of `section`s carrying
`open _root_.CategoryTheory.Limits`, which neither block uses — check by reading the block,
not by trusting the section), and anonymous `instance :` declarations in the jumped region
(all five here were `AbEnd` arithmetic, irrelevant to a base and a fibre predicate).
**Leave a breadcrumb at BOTH ends.** Four source positions now say where their block went
and why; the destination says where the four came from, that the move was verified, and
that relocating UPWARDS cannot break a consumer.
