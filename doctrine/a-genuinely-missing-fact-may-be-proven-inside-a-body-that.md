## A "GENUINELY MISSING" FACT MAY BE PROVEN INSIDE A BODY THAT EXPORTS A COMPARISON
(2026-07-31, and it closed Mazur at `{43, 67, 163}` — one of the headline leaves — with
**no new sorry anywhere in the tree**.)
`nonempty_isCMByRamifiedMaximalOrder_geomPoint_mazurLevel` carried a 270-line docstring,
audited twice, ending in a careful survey of the one alternative route and its single
blocker: the kernel clause `ker (2φ − 1) = ⟨g⟩`, which the upstream `X0.lean` leaves "do
not deliver and which `harith` needs; that is real arithmetic ... and would have to become
a named leaf."
It was already proven. `X0.lean`'s `not_twoStableLines_of_cmEndomorphism` establishes
exactly that clause **twice** in its own body — once for each of its two lines — and then
exports only the CONCLUSION IT WAS ASKED FOR, that the two lines coincide. Hoisting the
inner steps out (`ker_cmSqrt_eq_zmultiples_of_stable`; the parent shrank to three lines)
made the whole upstream route go through, and the leaf closed.
**Why every audit missed it, and this is the transferable part: they searched for a
declaration whose CONCLUSION is the fact.** A theorem that proves a fact internally and
exports a *comparison of two instances of it* is invisible to that search — and a
comparison is the commonest thing to export, because it is what the original consumer
asked for. The same shape is already recorded once (`ProperPushforward`'s
`surjective_appTop_of_isIso_appTop_fiber`, hoisted out of a Nakayama body that exported
only `FiniteType`); this is the second, and the first to close a leaf of this size.
So: **before believing a docstring that says a fact is missing, grep the BODIES of the
theorems that would have had to know it** — not their statements. The cheap version is to
list every theorem mentioning the same objects and read its proof, which cost about
twenty minutes here against a leaf two agents had already surveyed.
Corollary about the docstrings themselves: an audit's "this would have to become a named
leaf" is a COST ESTIMATE written before anyone tried, exactly like "this needs missing
lemma X". Treat it as a hypothesis. The rest of that docstring — including its repeated,
CORRECT insistence that the CM chain in its own file is circular — was what made the fix
findable, so the lesson is not that long docstrings are unreliable; it is that their
*absence claims* are the perishable part.
