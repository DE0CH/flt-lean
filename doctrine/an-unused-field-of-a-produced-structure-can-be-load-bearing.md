## AN "UNUSED" FIELD OF A *PRODUCED* STRUCTURE CAN BE LOAD-BEARING THROUGH A SIBLING FIELD

(2026-07-31.) The cheapest-looking way to close a leaf is to show nobody needs it. For a datum
structure that the leaf PRODUCES, the natural check is to grep the consumers of the field the leaf
supplies — and that check can give a confident wrong answer.

`X0.lean`'s `card_compl_range_le_card_divisors` exists only to supply the `⊇` half of
`IsX0Compactification.CuspLocus.cover`, and no consumer of `cover` reads that half: the one
derivation that touches it, `nonempty_cuspIndexing_of_cuspLocus`, uses `⊆` only, and both
docstrings say so. The leaf still cannot be dropped. The surjectivity is spent in the PRODUCER,
`nonempty_cuspLocus_of_residueIndexing`, proving a DIFFERENT field of the same structure —
`ratPoint`, which is obtained by transporting a free theorem along `e.symm` and so needs `e` onto.
`ratPoint` then has a live reader two files away.

So the ownership question for a produced datum is not "who reads this field" but **"what else in
the producer's proof is spent on it"**. Read the producer, not only the consumers.

