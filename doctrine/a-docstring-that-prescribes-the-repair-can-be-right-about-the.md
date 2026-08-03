## A DOCSTRING THAT PRESCRIBES THE REPAIR CAN BE RIGHT ABOUT THE MATHEMATICS AND WRONG ABOUT WHERE IT GOES
(Same task, and it is why the leaf sat open.) `exists_cuspLocus_atkinLehnerSwap`
carried an unusually good docstring: it named the repair ("carry the
Atkin–Lehner action as a further conjunct of `exists_cuspResidueIndexing` …
closed that way this leaf disappears instead of being paid for twice"), named
what would go wrong otherwise (the file would owe Deligne–Rapoport twice), and
was RIGHT. Two things it did not check, each of which alone blocks the repair:
* **Declaration order.** The conjunct mentions `IsAtkinLehner`, declared 41 000
  lines BELOW the cusp indexing it was to be attached to. Not statable. The
  repair is a hoist, and the hoist has to be measured before the mathematics
  matters at all — `flt-hoistcheck.py` on the three declarations involved
  (`RelPoint.post`, `IsNIsogenyPair`, `IsAtkinLehner`) reported HITS 0/1/2 with
  every hit inside the moving set, i.e. dependency-closed, in seconds.
* **Which declaration is the LEAF.** `exists_cuspResidueIndexing` — the one the
  docstring names — is PROVEN, over `exists_cuspAboveDivisor` and a counting
  leaf; and `exists_cuspAboveDivisor` is proven over `_root`, which is proven
  over `_neron`, which is the `sorry`. Adding a conjunct to the named theorem
  would have meant adding a `sorry` to a proven theorem. The conjunct belongs
  three levels down, on `exists_cuspAboveDivisor_neron`, and is then threaded UP
  through the three proven wrappers, each of which forwards it unread.
**So the standing check on any prescribed repair is two `grep -n`s: the line
number of every name the new statement mentions, against the line number of the
declaration it is to be attached to; and the body of that declaration, to see
whether it is the leaf or a wrapper over one.** Both are cheaper than reading the
mathematics, and either one can turn a "one conjunct" repair into a different
task.
Corollary, and it is what makes the trade worth taking: closing the leaf this
way is a genuine **−1**, because the conjunct rides on a leaf the file was
already paying for. Closing it as a free-standing construction would have been
`1 → 1` with Deligne–Rapoport owed twice — which is what the docstring was
warning against, and it was right.
