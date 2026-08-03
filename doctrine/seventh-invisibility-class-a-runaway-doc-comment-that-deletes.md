## SEVENTH invisibility class: a RUNAWAY DOC COMMENT that deletes 50 declarations while the file still parses
(2026-07-31, `flt-lean-391`, found in `Modularity/Patching.lean` at release 27.) A `/--`
whose terminator a declaration-level merge drops does **not** produce a parse error. Lean's
block comments NEST, so some stray terminator further down — typically the one belonging to
an orphaned *rival* docstring the same merge left behind — closes it. The file parses. Every
declaration in between is silently a comment. Here that was **~1980 lines**, including
`IsCohenCoefficients`, `existsUnique_ringHom_wittVector_of_isNilpotent`,
`surjective_of_span_range_sup_map_eq_maximalIdeal` and `taylorWilesCoordModel`.
**Nothing points at the opening line.** The wound reports itself hundreds of lines away as
`Unknown identifier`, `Function expected at`, and — the unmistakable tell —
`invalid use of explicit universe parameters, X is a local variable`. That last one is what a
*swallowed* name becomes once `autoImplicit` binds it, and it cannot arise any other way,
because nobody writes `X.{u,v}` for a name they did not define. Seeing it, do NOT hunt for a
missing import: run a comment-depth scan (walk the text counting `/-` and `-/`, skipping `--`
lines at depth 0) and report every top-level block longer than ~400 lines. This file has
genuine 600-line docstrings, so length alone is not the signal — depth balance is.
Two traps in the repair itself. **A comment-open or comment-close token spelled inside
block-comment PROSE still nests**, so writing the note that records the wound can reopen it —
re-run the depth scan after editing, every time. And the matching stray terminator downstream
is usually attached to a rival declaration, so fixing only the opener flips the remainder of
the file into a comment instead.
Same release, same file, two more wounds of the same family worth naming: a statement whose
body was replaced by an orphaned rival body, giving `theorem foo : T := <term> := by …` (a
parse error, and one that truncates everything below it — so every error count on a wounded
file is a LOWER BOUND until the parse errors are gone); and a stray conclusion fragment
dropped INTO a tactic block. **Corollary for the merge worker: "every module except X builds"
is only true of modules the build REACHED.** X0 is upstream of `Patching.lean`, so the release
build stopped before it, and `Patching.lean`'s 50 errors were invisible — release 27's handover
called X0 "the only thing between this tree and a release" on exactly that basis. Elaborate a
suspected-unreached module directly with `lake env lean` against the previous release's oleans
before believing a whole-build claim about it.
