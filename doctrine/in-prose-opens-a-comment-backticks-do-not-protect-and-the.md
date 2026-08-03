## `` `/-!` `` IN PROSE OPENS A COMMENT — BACKTICKS DO NOT PROTECT, AND THE BALANCE CAN COME OUT ZERO
(Same run, caught by re-scanning, and it is the sharpening the existing rule needs.)
Writing the note that RECORDS a comment-level repair is the likeliest place to cause
one — this file already says so.  Two things it does not say, both measured here:
* **Backticks are not protection.**  Lean's lexer knows nothing about code spans, so
  `` `/-!` `` inside a docstring is an opener exactly as a bare `/-!` is.  Write
  "module-comment note", "the doc-comment opener", "the closing delimiter" in words.
* **The total depth can come out ZERO and still be wrong.**  Three such openers in
  `X0.lean` swallowed three later `-/` and the file scanned as `depth 0, no strays`
  — the runaway-that-balances shape — while a fourth in `RelativePicard.lean` left
  `depth 1` and was obvious.  So the scan that decides is **depth AND strays AND the
  line of every unclosed opener**, run after EVERY docstring edit, not once at the end.
  `tools/merge/parsecheck.py <file>` is the project's version and takes seconds.
