## AN ORDERING OBSTRUCTION MUST NAME THE DECLARATION THAT PINS IT
(2026-07-31, `flt-lean-322`.) A leaf can be blocked by Lean's DECLARATION ORDER rather than by
mathematics: every declaration its documented route spends sits BELOW it in the file. That is a
one-commit block move, not a proof effort — and the cheapest large win available, because the
route is already written down.
The trap is in how such an obstruction gets recorded. A careful audit had certified
`exists_framedGaloisRep_descent_hilbertTraceSubring_of_isWeaklyUniversal` as unmovable: *"they
cannot be moved below the cluster: the retraction consumes the consumer, so relocating the pair
below the cluster puts the retraction below its own input."* Every clause is true, and the
conclusion is false. **"Below the cluster" is not a location.** The retraction is ONE declaration,
it is the LAST of the cluster, and the destination that works is immediately ABOVE it — where the
route's five machinery declarations are all in scope and the retraction still sees every input it
had. The audit had reasoned about a region when only a single declaration pinned anything.
So: an ordering claim of the form "X cannot move past Y" is only usable if `Y` is a NAME. If it
names a block, a cluster or a section, re-derive it — the real constraint is almost always one
declaration, and the legal destination is the line just before that one.
Doing the move as its OWN commit, touching nothing else, is what makes it auditable: assert the
line multiset is preserved, and check the three things that make a move pure —
* comment-stripped grep for every moved name over the range crossed (docstring mentions do not
  count, and this file's docstrings mention everything);
* the moved block's upstream all stays above, its downstream all stays below;
* no `section` / `namespace` / `variable` boundary between source and destination, and no
  `open … in` / `set_option … in` modifier attached to the first declaration moved.
The move cost ~50 min of elaboration to verify and converted a leaf that three prior agents had
recorded as ATOMIC into a fifteen-line assembly over one much narrower leaf.
