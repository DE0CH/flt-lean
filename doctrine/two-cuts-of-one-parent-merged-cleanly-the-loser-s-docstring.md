## TWO CUTS OF ONE PARENT, MERGED CLEANLY: THE LOSER'S DOCSTRING SAYS IT WON, AND SO DOES THE PARENT'S — ONLY THE `by` BLOCK KNOWS
(2026-07-31, `flt-lean-296`, on `exists_pointwiseCommutingHeckeAlbaneseFamily` in
`ModularCurve/X0.lean`.)  Two agents cut the SAME parent leaf on the SAME DAY along two
different seams, and release 29 merged both — no conflict, because each landed its new
declaration in a region the other never touched.  The parent kept ONE proof, so one cut
became live and the other became an orphaned `sorry` that no proof term in the project
reaches.  The task prompt I was handed named the orphan, described it as "the consumer is
PROVEN over it", and was quoting the orphan's own docstring accurately.
**What makes this sharper than the orphan classes already recorded above: BOTH DOCSTRINGS
NAMED THE LOSER.**  The orphan's docstring opens *"`exists_commutingHeckeAlbaneseFamily`
below is PROVEN over this and nothing else"*; the PARENT's docstring says *"PROVEN over
`exists_pointwiseCommutingHeckeAlbaneseFamily` immediately above"* — twice, in bold — and
the parent's actual `by` block calls `exists_commutingHeckeAlbaneseFamily_values`, a
different leaf 19 700 lines away.  So the existing rule *"read the PROOF of the theorem the
prompt says your leaf unblocks"* is not merely good practice here: **the proof body is the
ONLY artefact in the file that is not lying**, and it is lying in both directions at once
(the parent's docstring even says "immediately above" about a declaration far below it,
which is a free extra tell — a stale DIRECTION word).
Three checks, in the order that costs least:
* **`grep -n '<your target>' <the file>` and classify every hit.**  Own declaration plus
  docstrings only ⇒ orphaned.  Four hits here, three of them prose.
* **Read the parent's `by` block, never its docstring.**  If your target's name is not in
  it, you are on the losing cut whatever the prose says.
* **A "immediately above/below" in a docstring is an ORDER ASSERTION — check the line
  numbers.**  A merge that lands a relocation as an insertion elsewhere falsifies it
  silently, and it is the cheapest signal that two cuts collided.
**THE RESOLUTION, and it is decidable rather than a matter of taste.**  Compare the two
cuts' STRENGTH and their POSITION.  Here the winner (`_values`, morphism-level commutation
at every pair of arities plus a value clause) is strictly stronger than the orphan
(points-level, pinned primes only) and sits ABOVE it — so the orphan is a fifteen-line
corollary of the winner, and closing it that way takes the cluster from two open leaves to
one with a diff of one theorem body.  **Prefer that to the "better" repair** — hoisting the
orphan above the winner, strengthening it, and proving the winner over it — whenever the
file is contended: the good repair was ~150 lines of movement in the most-edited file in the
repository, and the presentational gain does not buy a merge conflict.  Say in `to_merger`
that you took the cheap one and what the expensive one would have been; that is a decision
recorded, which the merge worker can reverse, rather than a question nobody will answer.
**And do not read "closed the leaf" as "did mathematics".**  Deriving an orphan from a
strictly stronger sorry adds no theorem; what it removes is a phantom frontier slot that
will otherwise keep drawing dispatches — this one had already drawn mine.  Report it as
merge repair, with the count delta stated (`2 → 1`), or the next reader will believe a
theory gap closed.

