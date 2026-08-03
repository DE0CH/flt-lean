## A DECLARATION-ORDER TANGLE IS RECOVERABLE — FROM THE DEPENDENCY GRAPH, NOT FROM THE TEXT

(2026-07-31, release 32, the `Gamma0GITPresentationOver` cluster in `X0.lean`.)

Release 31 declined this cluster with an honest reason: *"the region 38750–43000
has ~24 interleaved declarations and the intended order is not recoverable from
the text alone; `git log -m -S` each name and re-apply the relocation."*  The
`git log -m -S` route is a dead end here — every hit is a merge commit — and the
intended order does not have to be recovered, because **the order is FORCED by
the constraint graph, and the graph is one comment-stripped decl/use scan.**

The method, and it is mechanical:

1. scan each name for `DECL` and `USES` over comment-masked source, so a
   docstring mention never counts as a use;
2. write the edges `decl(X) must precede every use(X)`;
3. **find the block that CANNOT move** — run `flt-hoistcheck.py` on each
   candidate and keep the one with nonzero HITS.  Here it was
   `exists_gamma0GITPresentationOver_zmod`, pinned by three real dependencies;
4. everything else is then forced: dependencies rise to just above the pinned
   block, consumers sink to just below it, in graph order.

That gave five blocks and one arrangement.  `tools/merge/blockmove.py` (new)
applies several moves ATOMICALLY in ORIGINAL coordinates — so the specs cannot
invalidate each other's line numbers — and refuses to write unless the sorted
line multiset is unchanged, which is the exact receipt for a pure permutation.

**The one thing the graph does not tell you is SCOPE**, and it is the half that
bites.  Two of the five blocks were inside a `section` whose only content was
`open CategoryTheory.Limits`, and they left it.  Check by grepping the moved
text for names from that `open` — in code, not in docstrings, where the false
positive lives — and if it needs it, carry `open _root_.X in` on the moved
declaration.  Also check for depth-0 `variable` lines in the jumped region; a
scope-aware walk answers that in ten lines and a plain grep does not.

