## `classical` IS A BOILERPLATE ANCHOR — a scripted slice must assert on its SOURCE, not only its DESTINATION
(2026-08-02, `flt-lean-367`, one wasted edit.)  CLAUDE.md already forbids keying a
scripted edit on a boilerplate LINE and names `omit … in`, `set_option … in`,
`open scoped … in`.  Add the tactic `classical`, and note the twist that made the existing
rule not fire: my script asserted `s.count(anchor) == 1` on the DESTINATION and took the
source slice with `next(i for i,l in enumerate(scratch) if l == '  classical')` — which
matched the FIRST helper lemma, not the main theorem, and spliced 200 lines of already-
inserted declarations into the proof body a second time.
**Both ends of a cut-and-paste need the assertion.**  The destination check says "I am
writing in the right place"; it says nothing about "I am writing the right text".  When
slicing out of a file, anchor on a line that is unique BY CONSTRUCTION — the declaration
header — and assert its uniqueness too.  The symptom here was cheap to spot (`grep -n` for
the declaration name showed a primed copy that should not exist in the target file); it
would not have been if the duplicated text had happened to elaborate.
