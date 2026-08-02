---
name: flt-error-count-recipe-returns-zero
description: "`': error(\\(|:)'` counts zero errors on a lake build log — the two tools put the error prefix on opposite sides of the source location"
metadata: 
  node_type: memory
  type: project
  originSessionId: 60ba0bb4-3044-477d-ab03-d0378b13c9c2
  modified: 2026-08-02T02:28:25.730Z
---

`lake env lean` and `lake build` write diagnostics with the prefix on OPPOSITE
sides of the source location, so a grep tuned to one scores `0` on the other:

    lake env lean   ->   <path>:<line>:<col>: error(lean.unknownIdentifier): …
    lake build      ->   error: <path>:<line>:<col>: …
                    +    error: Lean exited with code 1        <- not a diagnostic
                    +    error: build failed                   <- not a diagnostic

So `': error(\(|:)'` returns **0** on a `lake build` log for a module with 33
errors — while that log plainly ends in `error: build failed`. Count with both
spellings and filter to lines naming a source file, or the two summary lines
inflate a raw count by exactly two:

    grep -E ': error(\(|:)|^error: ' <log> | grep -c '\.lean:'

Measured at `flt-lean-282` commit `f1801b15`: the same `X0.lean` commit gave
`33` under `lake env lean`, `0` under the old pattern on `lake build`, and `33`
under this recipe on both. **That commit is NOT an ancestor of `main`** — it sits
on the unmerged `flt-lean-282-x0-repair` branch, so `main` carried no
error-counting recipe at all until it was re-landed 2026-08-02.

**Why:** exactly the same defect as [[flt-sorry-grep-returns-zero]], on the same
axis, in the same file — an empty count from a failing build reads as success.

**How to apply:** never read a count as a verdict. The `EXIT=` line you appended
yourself is a statement about the process; a grep is a summary of a log. Require
`EXIT=0` plus `Build completed successfully (NNNN jobs)` for a MODULE build —
but note the ROOT target is different, since `#assert_no_sorry` makes a green
release build end `EXIT=1` and never print that line.
