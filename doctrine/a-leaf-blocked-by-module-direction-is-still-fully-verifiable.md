## A LEAF BLOCKED BY MODULE DIRECTION IS STILL FULLY VERIFIABLE — DOWNSTREAM OF THE BLOCKER
(2026-07-31, `flt-lean-148`, on `exists_frickeSlash_eq_smul_of_isNewEigenformAt`.)
Some leaves are blocked not by missing mathematics but by the import graph: the theory
they need is PROVEN, in a module that `public import`s the leaf's own file, so it cannot
be named there. The standing repair is a hoist, and hoists are expensive — the one here
is 193 declarations and 8 267 non-comment lines out of the 80 k-line `Interface.lean`.
The trap is that such a leaf looks like an ordinary open leaf to every frontier
instrument, so agents keep getting dispatched at it, and each one can only re-discover
the blockage. Task prompts then acquire a PRECONDITION ("blocked until the hoist lands;
report the state and stop"), and an agent that obeys it produces nothing at all.
**There is a third option, and it is usually the right one: prove the theorem the leaf
will BECOME, in a scratch module that imports the DOWNSTREAM file.** That module sees
both sides — the leaf's own vocabulary (it is upstream) and the blocked theory (it is the
downstream file's) — so the whole route compiles, today, with no hoist. What you cannot
do is *land* it; what you can do is hand the hoist a verified block to paste.
This converts an unbounded hoist ("move 8 000 lines and hope the route closes") into a
bounded one ("move 8 000 lines and paste in this compiled 557 lines"), and it separates
the two risks — the mathematics and the relocation — so that they are never being
debugged at the same time. It also finds the residue EXACTLY. Here the route was four
steps plus a carrier bridge that nobody had costed; compiling it showed that three of
the four steps and *half the bridge* go through unchanged, and reduced the leaf to ONE
named `sorry` (Atkin–Lehner Thm 1). The blocked leaf became a checked `−1 +1`, and the
surviving leaf is real mathematics rather than a module-direction artefact.
Concretely, when you are sent at a leaf and find its precondition unmet:
1. confirm the direction (`grep '^public import'` both files) rather than assuming it;
2. write the scratch against the downstream module and compile the ENTIRE route, ending
   at the leaf's conclusion over whatever carrier the downstream theory uses;
3. commit the compiled text as a root-level `HANDOFF-*.md` — a `.lean` file under
   `Fermat/` that nothing imports is invisible to the build (fourth invisibility class),
   and a note in `to_merger` is for one merge only;
4. queue the hoist with the handoff named in it, and queue the residue separately.
Related, and worth checking before dispatching any hoist: **the reverse move may be
impossible for a reason nobody has written down.** Here, "move the blocked cluster
downstream instead" fails because a THIRD module sits between the two and consumes the
cluster's consumers — `Interface → ModThree → MazurTorsion → X0`, and `MazurTorsion.lean`
uses `X0.lean`'s `y0HasNoRationalPoint_*` **32 times in non-comment source**. It is the
cheaper question, so ask it first.
But ask it with a **transitive** scan and against the RIGHT name. The naive check —
"does the downstream-of-me module mention my cluster?" — said NO here: `kenkuLevels`,
`cuspPeriod`, `frickeSlash` and `isFrickeEigenform` each occur **zero** times in
`MazurTorsion.lean`'s code (all 18 textual hits are docstring). What `MazurTorsion`
consumes is the far end of a 14-link chain inside `X0.lean`
(`exists_frickeSlash_eq_smul_of_isNewEigenformAt → isFrickeEigenform_of_… →
cuspPeriod_ne_zero_of_… → cuspPeriod_ne_zero_of_kenkuLevel → lFunction_apply_one_ne_zero_of_… →
isTorsion_jacobian_of_… → finite_jacobian_of_… → hasRankZeroJacobian_of_… → the twelve
`y0HasNoRationalPoint_*`). Every link occurs exactly TWICE in comment-stripped source —
its own declaration plus its single consumer — so the thread is invisible to any check
that stops at one hop, and a one-hop check would have licensed a move that breaks the
build twelve times over.
