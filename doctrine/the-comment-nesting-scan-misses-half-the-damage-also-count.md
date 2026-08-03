## THE COMMENT-NESTING SCAN MISSES HALF THE DAMAGE — ALSO COUNT STRAY `-/` AT DEPTH ZERO

(2026-07-31, `flt-lean-330`, measured on `merger`.) The release-24 note prescribes
"block-comment nesting depth returns to zero in every file". That check is real and it
found one file here. **It is blind to the mirror case, which was three times as common
in the same sweep**: the merge keeps ONE side's `-/` while the other side's paragraph
lands after it, so the depth balances perfectly and English is parsed as Lean.

Both shapes come out of one 20-line scanner if you also record every `-/` seen while
depth is ZERO. That list is the second half of the check and it is never legitimate:

    depth 0, see `/-`  -> depth 1        depth 0, see `--`  -> rest of line is a comment
    depth>0, see `/-`  -> depth+1        depth>0, see `-/`  -> depth-1
    depth 0, see `-/`  -> RECORD IT      end of file, depth /= 0 -> RECORD THE OPENER

On `merger` at `965d2b54` this found, in seconds and with no build: `EllipticScheme.lean`
(unterminated, at EOF, 2 400 lines from the damage), `X0.lean` (two strays), and two
orphaned docstring OPENERS whose bodies had been dropped — a third shape, which shows up
as `unexpected token '/--'; expected 'lemma'` and is caught by "a `/--` block whose close
is immediately followed by another `/--`".

**Why it is worth running before anything else you do in a worktree: ONE parse error
hides every later error in the file.** `X0.lean` reported `maximum number of errors
(100; from option maxErrors) reached` and stopped at line 76148. Fixing the two syntax
wounds — five minutes, no mathematics — took it to **22** real errors, all beyond that
cap and none of them previously visible to anybody. The frontier classes in this file are
about work you cannot SEE; this is the cheapest instance of the phenomenon and the only
one whose whole cost is a `python3 -` heredoc.

And the corollary that decides what to do next: **a parse error is a passer-by's to fix;
an interface reconciliation is not.** The 22 that remained in `X0.lean` are dropped
binders whose call sites still pass them, a pre-rename name still cited once, and four
duplicate declarations whose two copies carry *different docstrings* (`difflib` ratio
0.34 — same theorems, rival prose). Deleting either copy discards an author's writing, so
that choice belongs to an author. Fix the syntax, publish the list, stop.

