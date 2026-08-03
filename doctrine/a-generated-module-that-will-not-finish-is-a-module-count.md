## A GENERATED MODULE THAT WILL NOT FINISH IS A MODULE-COUNT PROBLEM, NOT A TACTIC PROBLEM
(2026-07-31, `flt-lean-132`, closing the last four leaves of
`EllipticCurve/MazurNonCMCertificate.lean` — the `p = 17` rows of Mazur's non-CM table.)
The standing note above records that a GENERATED certificate is thousands of mutually
independent theorems and so parallelises almost perfectly *within* a file. That is true and
it has a ceiling, and the ceiling is what stops these files: measured here, one 14 200-line
generated module ran ~50 minutes at ~10 GB resident using **at most ~11 of 128 cores**, while
the same content split into four sibling modules ran **all four concurrently**, because
`lake` schedules independent MODULES across the whole machine and Lean's in-file parallelism
does not. The predecessor had stopped the monolith at 60 minutes and 47 GB and recorded the
row as blocked; nothing about the mathematics or the tactics changed.
**So when a generated module will not finish, the first question is not "which tactic is
slow" but "what is the coarsest independent partition of this file".** For a certificate that
reassembles a product from per-factor chains the partition is written on the statement: the
`k` chains share nothing but the factor definitions, so `k` modules plus a parent holding
exactly what mentions more than one factor. Here that was `SeventeenA/Factor{1..4}.lean` at
~3 540 lines each plus a 240-line `SeventeenA.lean` (product identity, six Bézout
coprimalities, `xpow_mul` assembly, coprimality leaf).
Three things that decide whether the split is legal, and all three are read off the generator
rather than guessed:
* **what must stay together** — a factor's TWO chains (the `q ^ m` one and the `q ^ 2` one for
  the coprimality leaf) share their `XPow f 1 X` base, so they cannot be separated; and each
  chain step's `simp only [f…]` unfolds the factor's `def`, so the `def` travels with them;
* **what must go up** — everything naming two factors. Nothing else in the row refers into a
  factor module except the final step of each chain and the factor's own definition;
* **the interface is free** — the factor modules are `public import`ed by the parent and
  everything is in one namespace, so no statement anywhere changes and the four sorried
  theorems in the consumer are DELETED rather than re-pointed.
**THE REFACTOR'S SAFETY NET IS A BYTE-IDENTICAL ROUND TRIP ON THE ROWS YOU ARE NOT
CHANGING.** Splitting meant restructuring `gen_factored.generate_row` into emitters
(`_emit_def`, `_emit_chains`, `_emit_factor_thm`, `_emit_coprime`, `_emit_assembly`,
`_emit_coprime_leaf`) so a second composer `generate_row_split` could route them to different
files. The check that the restructuring changed nothing is that regenerating the PROVEN
`ElevenA.lean`, `ElevenB.lean` and `MazurNonCMFrobenius.lean` reproduces them byte for byte —
which it does, and which is a far stronger statement than any build could make in the time.
Get that green before generating the new files.
### A GENERATOR WHOSE INPUT LIVES IN `/tmp` IS NOT A GENERATOR
`gen_modules.py` was documented as regenerating all five modules in seconds. It could not run
at all: `gen_row.factors` reads `/tmp/fac-<tag>.txt`, the PARI factorisation of each `H`,
produced by hand in a `gp` session and never committed. `/tmp` had been cleared. The round-trip
claim in the docstring was therefore unfalsifiable, and the one check that would have caught
the whole class was unavailable.
`gen_factors.py` (added here) regenerates them. **When a generator reads a file, the thing that
produces that file is part of the generator** — and note the factorisation is only a SEARCH, so
this is the CAS doctrine's untrusted-searcher shape: `gen_factored._prepare` asserts the factors
multiply back to `H`, and the Lean compiler re-derives the product identity, so a wrong
factorisation cannot survive either check.
One PARI trap met on the way, because it fails silently: **a `for(...)` spanning several lines
does not survive being fed to `gp` on stdin** — each newline ends a statement, so the loop body
is lost and the script exits `0` having printed nothing. Put the loop on one physical line, and
assert on the number of records you got back rather than on the exit code.
### THE SCALING LAW, so the `p = 37` row is priced rather than merely forbidden
The same measurement prices the row that CLAUDE.md already tells you not to dispatch a plain
computation at, and it is worth having the number rather than the prohibition. Two factors move
independently, and both are read off the statement before any Lean is written:
* **steps** `≈ 1.5 · log₂(q ^ m)` — square-and-multiply, one squaring per bit and a multiply on
  about half of them;
* **the degree of the identity handed to `ring_nf`**, which is `< 2 · deg f` whatever the
  exponent — that is the whole point of square-and-multiply, and it is why `deg f`, not `m`,
  is what has to be kept small.
At `p = 17` (`q = 67`, `m = 34`, `deg f = 34`): ~310 steps at degree `< 68`, measured at ~50 min
and 794 MB of `.olean.private` for one factor module. At `p = 37` (`q = 397`, `m = 222`,
`H = 222³`, so three factors of degree `222`): ~2 875 steps at degree `< 444` — **9.3× the steps
and 6.5× the degree**, i.e. **61× if `ring_nf` were linear in the degree and ~400× if it is
quadratic, so 2 to 14 DAYS per factor module and tens of GB of olean apiece.** Splitting per
factor does not rescue it: a degree-`222` irreducible cannot be split further, which is exactly
the ceiling lever 1 of the certificate note runs into.
**So the `p = 37` row needs a different route, and the number says which knob is worth turning:
`deg f`, quadratically, not `m`.** Anything that replaces the `ring_nf` identity by a
cheaper-per-step check — a `decide` over an explicit coefficient vector, `Nat`-level arithmetic,
or a reflection tactic — attacks the `6.5×` and leaves the `9.3×`, and is the only direction with
enough headroom.
