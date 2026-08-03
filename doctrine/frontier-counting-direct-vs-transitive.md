## frontier counting direct vs transitive

(Cut verbatim out of CLAUDE.md's `THE GOAL: fully formalize Fermat's Last Theorem, no sorry, n` section at the 2026-08-03 doctrine split; nothing reworded.)

**Counting the frontier: DIRECT vs TRANSITIVE sorries, and the comment
trap (2026-07-25 — both of these caused phantom dispatches).**

Two different numbers are both called "the frontier" and they are not
interchangeable:

- *Direct*: the declaration's own body contains `sorry`. This is what
  Lean's `declaration uses 'sorry'` warning reports, and it is the set of
  leaves that can be WORKED ON. **234 across 26 modules** as of `60313518`
  (release 4, 2026-07-27) — up from 175 at `0a976e16` earlier the same day.
- *Transitive*: the declaration's proof term reaches `sorryAx`, i.e. it is
  sorried **or consumes something sorried**. This is what
  `ProgressCensus.lean`'s census reports.

**A RISING count is not a regression — it is usually disclosure.** The jump to
234 is mostly the Cartier-duality island becoming visible: five `HopfAlgebra`
modules that nothing imported, hence never compiled, hence invisible to the
warning set *and* to the census. Wiring them in (`1492cecb`) made their sorries
countable for the first time. Decomposition does the same thing at smaller scale
— a node that closes over three named sub-leaves nets +2 while being real
progress. Read the delta alongside what closed, never alone.

**Do not trust a frontier number in this file — regenerate it.** The figures
above were 85/86 for a single day and were wrong by a factor of two by the next
morning: the tree grows leaves faster than prose records them, and six releases
landed during one bookkeeping run (the frontier moved 138 → 156 → 157 → 174 →
175 *while it was being counted*). Any count is stamped to a commit and stale
immediately. `flt-frontier.py`'s source scan **is** validated against the
compiler — at `a18c5c4d` it matched the build's `declaration uses 'sorry'`
warning set exactly, 157 = 157, zero difference in both directions — so run it
rather than quoting a number.

A consumer of a sorried leaf is transitively sorried but has NOTHING to
prove — dispatching an agent at it wastes a worker. Two whole clusters were
dispatched this way (`Chebotarev.lean`, and three leaves in `Flat.lean`)
before agents reported back that their targets were already proven. **Build
task lists from the DIRECT set; use the transitive set only for judging
whether a subtree still blocks the root.**

