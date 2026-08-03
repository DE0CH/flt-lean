## `flt-hoistcheck.py` ANSWERS THE WRONG QUESTION FOR A **DOWN** MOVE — and reports `HITS: 0`
(2026-08-01, `flt-lean-235`, closing `exists_qExpansion_gamma0AtlasOver_zmod`.) The tool's
own docstring says *"does the block use any name declared in the region it would jump
over?"* and then *"Both directions are handled"*. The first sentence is the truth and the
second is misleading: that question is the right one for **hoisting UP** (where the moved
code can lose its own inputs) and the **wrong one for moving DOWN**, where the moved code
keeps every input it had and the only hazard is that *the jumped region consumed the
block*.
Measured: `--block 42904 43125 --to 43670` on `X0.lean` reported **`HITS: 0`**, and line
43468 — squarely inside the jumped region — calls
`isAlgebraic_globalSections_of_gamma0AtlasOver_zmod`, which is declared inside the moved
block. The move as reported would have broken the build. It was safe only because a second
block containing 43468 was moved along with it, which the tool never asked about.
**So for a DOWN move, run the reverse scan yourself.** It is ten lines and it is the whole
safety argument:
    names_moved = {declarations inside the moved blocks}
    for each line in (span from block start to destination) not itself moved:
        if any token of that line (comment-stripped) is in names_moved:  UNSAFE
Tokenise with `isalnum() or c in "_'."` — never a `\w` regex and never a `À-￿` class, for
the reasons already recorded — and also check the reverse-direction extras the tool does
flag and that stay relevant: anonymous `instance :` declarations in the region, and
`namespace`/`section`/`variable`/`open`/`attribute`/`set_option` lines inside the moved
blocks.
**And compute block boundaries DOCSTRING-TO-DOCSTRING, not from the `theorem` line.** A
declaration's block starts at the first line of its doc comment (walking up over
`attribute … in`, `set_option … in`, `@[…]`). Taking the `theorem` line instead attributes
each docstring to the PREVIOUS declaration, which silently shifts every block by its
neighbour's docstring — here that was 67 lines on one block and 170 on another, enough to
turn a correct plan into a stranded docstring plus a stray terminator. Both off-by-one ends
are already recorded in this file; the boundary computation is what prevents them.
Two riders from the same move, both cheap and both worth doing every time:
* **The receipt for a pure relocation is `Counter(before) == Counter(after)` on the LINE
  MULTISET, plus an unchanged line count.** `git diff --numstat` is NOT a receipt: git
  realigned this 256-line move as `395 insertions / 279 deletions` because its LCS chose a
  different alignment, so the stat looks like a rewrite. Do the move programmatically in
  ORIGINAL coordinates (so several blocks cannot invalidate each other's line numbers) and
  assert the multiset.
* **Measure both directions before choosing.** Down was 256 lines in 2 blocks, up was 443
  in 2 blocks. Down is also the intrinsically safer direction. But the sizes only compare
  once the boundaries are docstring-aware — with `theorem`-line boundaries the two came out
  the other way round.
