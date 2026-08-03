## A RECUT THAT PLACES ITS NEW LEAF **ABOVE** THE OLD CUT'S MACHINERY DOUBLES THE FRONTIER AND ORPHANS FOUR PROVEN DECLARATIONS
(2026-07-31, `flt-lean-163`, `Modularity/MoretBailly.lean`.  Closed
`exists_anticyclotomicCyclicChar` with **no mathematics whatever** — the repair is a
line-range move.)
The rival-cut sections above are all about two cuts made on two BRANCHES.  This is the
same damage made by ONE agent in ONE file, and it needs no merge to happen:
* on 2026-07-30 the node was cut as *prime-power class field theory* +
  *compositum*, and the compositum half was PROVEN — `RingClassArtinData.{ofDvd,
  imageSubgroup,lcm}` and `nonempty_ringClassArtinData_of_primePow`, ~150 lines;
* on 2026-07-31 the parent `nonempty_ringClassArtinData_anticyclotomic` was RE-cut a
  second way, along a different seam (replace the abstract group by
  `Multiplicative (ZMod K)`), and the new leaf `exists_anticyclotomicCyclicChar` was
  placed **immediately above the parent** — i.e. 300 lines ABOVE the prime-power leaf
  and the compositum machinery it would have had to consume.
Both cuts are individually sound and the second one's docstring argues its case
correctly.  Together, and only because of the POSITION, the file was left carrying
**two open leaves for one piece of mathematics** and **five declarations with no
consumer anywhere in the tree** (the four proven ones plus the prime-power leaf) —
free-floating code, which this project forbids.
**Nothing sees it.**  Both `sorry`s are honest and both emit their warning; the
frontier count went UP by one and read as ordinary disclosure; `own.py` and
`leafstat.py` correctly report both leaves unowned and open; there is no duplicate
NAME, no duplicate STATEMENT (the two leaves differ in shape — structure-valued at
`l ^ k` versus `ZMod`-valued at `K`), no scope wound, no comment wound, and the
build is green.  `dupstmt.py` cannot pair them and `xdup.py` has nothing to say.
**THE CHECK IS ONE LINE AND IT BELONGS IN EVERY RECUT: after cutting a new leaf out
of a parent, grep the parent's OLD sub-leaves for consumers.**
    grep -n '<each declaration the old proof consumed>' <the file>   # comment-stripped
Own declaration line plus docstrings only ⇒ you have just orphaned it.  Equivalently,
and cheaper to remember: **a new leaf must be placed BELOW everything the parent's
previous proof consumed**, because Lean's linear order is what decides whether the
two cuts can be composed instead of competing.
**THE REPAIR IS A RELOCATION, NOT A PROOF, and it is the good kind of −1.** Moving
`exists_anticyclotomicCyclicChar` (docstring through `sorry`, 63 lines) down below the
prime-power leaf made it provable in **19 lines** over three declarations that already
existed — the prime-power leaf, the compositum, and `exists_zmodChar_of_dvd_exponent`
— and every orphan became consumed again.  MoretBailly went 20 `sorry`s → 19 with no
mathematics done and no statement changed.  Verify the move the standard way (sorted
line multiset identical before and after; `git diff --stat` reporting equal insertions
and deletions) and say in the commit that the closure is merge repair rather than a
theorem, or the delta reads as CFT progress that did not happen.
**Two riders.**
* **The round trip that results is usually worth keeping.**  The chain now runs
  *prime-power data → general-`K` data → character → back into general-`K` data*.
  Collapsing it (prove the parent directly from the compositum and delete the
  character) removes ~20 lines and also deletes a statement downstream docstrings and
  queued tasks name — and would make the character declaration consumerless, which is
  the very defect being repaired.  Keep it, and say in the docstring that collapsing
  is available and what it costs.
* **A parent's docstring can go on describing the PREVIOUS route after a recut, and
  that is the cheapest tell there is.**  Here `nonempty_ringClassArtinData_anticyclotomic`
  still said "two inputs: the prime-power leaf and the compositum" while its body called
  the new character leaf — the same *docstring names a different leaf from the proof
  body* signal already recorded above, arising from a recut instead of from a merge.
  It is worth grepping for on its own: read the body, then read the docstring.
**THE CHECK PAID TWICE MORE IN THE SAME FILE, IMMEDIATELY.** Running it over
`MoretBailly.lean`'s other 18 leaves (comment-stripped tree-wide count of each leaf's
short name; `1` means its own declaration line and nothing else) found two further
orphans of exactly this shape, both with the same tell — *the parent's docstring names
a different leaf from the one its proof body calls*:
* `exists_stepanovJetSpanningFinset` (`:17525`). `exists_stepanovJetLinearForms`'s
  docstring says it is "PROVEN 2026-07-30 over the single smaller leaf
  `exists_stepanovJetSpanningFinset` above"; its body calls
  `exists_stepanovJetLinearForms_of_frobeniusSplit` (`:17169`) instead. Two open
  leaves, one piece of mathematics;
* `exists_hypEvalData_of_birationalNormalForm` (`:29099`).
  `exists_ratMembershipData_of_birationalNormalForm`'s docstring says it is "PROVEN
  over `exists_hypEvalData_of_birationalNormalForm` immediately above"; its body does
  not mention it.
And one that is NOT damage and must not be lumped in with them:
`det_nTorsion_eq_cyclotomicExponent` (`:57050`) is consumerless **on purpose**, and
its neighbour's docstring says so in as many words ("this theorem is derivable from
that leaf in a few lines … it has deliberately NOT been"). So the sweep's output is
a list of CANDIDATES, and the discriminator is one read of the neighbouring
docstring: a leaf whose prose says a consumer *is* proven over it, where the consumer
is not, is damage; a leaf whose prose says a consumer *could be* proven over it is a
pending decision.
**So the sweep is worth running on any file a recut has touched, and it is ten lines
of Python.** Strip comments, list the file's `sorry` leaves from the build's warning
line numbers, and count each short name across `Fermat/`. A count of `1` is the whole
signal.
