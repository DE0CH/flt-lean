## `exists_localDenom_chart`-STYLE THEOREMS ARE UNIQUENESS THEOREMS — the right-hand side does not mention the place
(Same task.)  `PlaceData.exists_localDenom_chart` says *"every `z` with `ord_v z ≥ 0` is a
chart fraction whose denominator does not vanish AT THE POINT"*.  It was written, and is
documented, for the residue-field computation (`finrank_residue_pt_eq_one`).  Its conclusion
mentions the place `v` **nowhere**, so it is also, for free, the statement that `O_v` is
determined by the chart data — and therefore that **two places with the same chart data are
EQUAL**:
    z ∈ O_v  ⟹  z = num/den with den not vanishing at the point
             ⟹  at v', num ∈ O_{v'} (chart_mem_valRing) and ord_{v'} den = 0
                 (ord_chart_eq_zero_iff)  ⟹  z ∈ O_{v'}
and then `PlaceClassify.isPlaceFun_eq_of_le` (a normalised place is determined by its
valuation ring) plus `ord_injective`.  Twelve lines over machinery that had been sitting there
since 2026-07-30.
**Generalisable, and it is the standing rule in a new suit** ([[flt-consumerless-theorem-may-discharge-a-live-leaf]],
"THAT THEOREM HANDS BACK X is a claim about its CONCLUSION"): *when a leaf asks for UNIQUENESS
of an object, look for a theorem whose CONCLUSION characterises that object by data the object
does not appear in.*  A "the local ring is such-and-such a localisation" theorem is always of
that shape, and it is always filed under something else.
Two riders from the same run:
* **The existing theorem was stated at `v = pt (Sum.inr s)` and its proof never used that.**
  Re-stating it with the two PROPERTIES of `v` that the proof consumes (`ord x = −1` and the
  branch congruence) is a copy-paste, and it is what turns it from a computation at a named
  place into a uniqueness statement.  Before generalising a proof, check whether the special
  hypothesis is spent at all — here it was spent only to obtain those two properties, in the
  first three lines.
* **THE SCRATCH CANNOT SEE DECLARATION ORDER, AND THIS IS WHERE IT BITES.**  The block was
  developed in a scratch that `public import`s the whole module, so `PlaceData.toFunctionFieldData`
  resolved fine; in the file it is declared 140 lines BELOW the insertion point, and four uses
  of `PlaceClassify.yy_ne_zero D.toFunctionFieldData` were hard errors on the first real
  elaboration.  The repair was to repeat the two-line proof as `PlaceData.yy_ne_zero` rather
  than hoist anything — **in a file with concurrent editors, a duplicated two-line proof is
  cheaper than a relocation**, and the docstring says which it is and why.
**And the differential receipt for a leaf closure, which costs one extra elaboration of a file
you were going to elaborate anyway**: elaborate `git show HEAD:<path>` at a real module path
too, map each `declaration uses 'sorry'` warning to its enclosing declaration NAME in each
file, and diff the two NAME sets.  Here that printed `CLOSED: ['pt_infinite_of_ord_xx_neg']`,
`NEW: []` — which is a statement no line-number comparison can make, because every later line
shifts.
