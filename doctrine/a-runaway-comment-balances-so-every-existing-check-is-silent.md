## A RUNAWAY COMMENT BALANCES, SO EVERY EXISTING CHECK IS SILENT — `tools/merge/longcomment.py`
(2026-07-31, `flt-lean-361`.  This was the release-27 blocker, and four more instances
were found in one pass once the check existed.)
`flt-comment-balance.py` finds a comment that never CLOSES (`depth > 0` at EOF,
`unterminated comment`). The commoner and worse defect balances:
> a merge splices a duplicated `/-- …` header into the middle of an existing docstring.
> The extra OPENER runs the comment far past its intended end; a stray terminator
> elsewhere in the file — itself the residue of a *different* orphaned block — closes it
> again. Total depth is `0`.
In `X0.lean` one such splice (six lines, byte-identical to a docstring 500 lines above)
ran a comment **1214 lines** and put **45 top-level declarations** inside it: the whole
`addPairHom`/`shearHom`/`pairSquareMap` group machinery. In `Interface.lean` another ran
**41 621 lines** over **644 declarations**. Nothing reported either: depth balances, so
`flt-comment-balance.py` is silent; the declarations are still in the SOURCE, so
`grep '^theorem'` and every duplicate scan are unchanged; `scopecheck.py` is unchanged.
The only symptom is a shower of `Unknown identifier` and `Function expected at` for names
that are visibly present in the file, which reads as a rename, a merge-side removal or a
missing import — and CLAUDE.md's own advice sends you to `git log -m -S` instead of to the
comment 1200 lines above.
**The signal that works is BLUNT: a 1200-line comment in a Lean file is never
intentional.** `tools/merge/longcomment.py` reports every block over `--min` lines
together with the number of doc-comment openers at column 0 inside it, plus stray
terminators separately. Run it before the release build; it costs seconds.
    python3 tools/merge/longcomment.py Fermat --damage-only
Three things about reading it, each learned by getting it wrong first:
* **Do not count "declaration-looking lines" as the damage signal.** This tree's
  docstrings quote Lean constantly and sentences begin `theorem …`, `lemma …`, `class …`
  at column 0; that heuristic flagged every long docstring in the project. A NESTED
  DOC-OPENER is the reliable tell, because it is what the splice leaves behind.
* **A long block with no nested opener is a genuine docstring** — `X0.lean` has one of
  1147 lines. One eyeball per hit; `--damage-only` suppresses them.
* **Fix the runaway FIRST, then re-run.** Closing one un-consumes the stray terminator
  that used to balance it, so a fresh stray appears elsewhere and names the next orphan.
  The repairs arrive in layers, for the same reason the release build takes three rounds.
**The repairs are syntax, and they must STAY syntax.** Demote a stale `/--` to `/-`,
reopen an orphaned prose block as a PLAIN comment (not a docstring — the text usually
documents a declaration other than the one that follows), comment out a truncated binder
fragment. Delete nothing: a merge that drops a declaration also drops the only copy of its
prose. Say in the note which choice you left to an author.
**AND THE TRAP THAT COST A ROUND: do not write a literal comment delimiter inside the note
explaining the repair.** `"a stray `-/` stood here"` CLOSES the comment and recreates
exactly the defect being fixed — two fresh strays appeared that way and were caught only
by re-running the scan. Write "terminator" / "delimiter" in prose.
**Know when to stop.** One `X0.lean` runaway was left unrepaired on purpose: the region it
hides contains a SECOND declaration of a name already declared outside it, so reopening it
converts a silent error into `has already been declared`, and choosing which copy survives
is an author's decision. A passer-by fixes the syntax and publishes the diagnosis; an
interface reconciliation is not theirs. Write the diagnosis down completely — the dropped
declaration, its source commit, the prescribed one-line derivation, the duplicate — so the
decision is all that is left.
