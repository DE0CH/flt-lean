## A DECLARATION INSERTED BETWEEN A DOCSTRING AND ITS THEOREM REPORTS AT THE DOCSTRING

(2026-07-31, `X0.lean`.) The commonest way a hand-inserted declaration breaks a huge file,
and the error names neither the inserted block nor the broken declaration:

    X0.lean:57339:67: unexpected token '/--'; expected 'lemma'

Line 57339 is the **closing `-/` of the PRECEDING docstring**, ~40 lines above the edit.
What happened is that a new `/-- … -/ def …` was placed *after* a theorem's docstring and
*before* the theorem, so the docstring is followed by a second docstring rather than by a
declaration. Same reported shape as the reserved-token truncation already recorded above,
different cause — so do not stop at "must be a token clash".

**It is worse than an ordinary error because a parse failure TRUNCATES the file**, so it
hides every later error in a module that takes half an hour to elaborate. Two checks, both
free, and worth running after any hand insertion into a big file:

    # a docstring whose next non-blank line opens another docstring or a /-! block
    awk 'prev ~ /-\/[[:space:]]*$/ && /^\/--/ {print NR": orphaned docstring above"} {prev=$0}' F.lean

Fix by hoisting the new block ABOVE the victim's docstring (check its own dependencies are
still earlier), not by re-indenting or by deleting the docstring.

