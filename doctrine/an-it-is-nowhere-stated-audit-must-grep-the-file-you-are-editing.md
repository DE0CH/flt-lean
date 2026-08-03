## AN "IT IS NOWHERE STATED" AUDIT MUST GREP THE FILE YOU ARE EDITING

(2026-07-31, `flt-lean-108`.) `Deformation.lean`'s obstruction leaf carried a machinery audit
saying `CompactSpace D.R` "is nowhere stated", with the refuting evidence spelled out: a grep of
`ProfiniteLocalNoetherian.lean` showing it takes `[CompactSpace R]` as a HYPOTHESIS throughout,
i.e. proves the converse direction. Every clause of that was TRUE about that file, and the
conclusion was false. `compactSpace_of_isAdic_of_pi` — exactly the wanted direction — sits **6800
lines above the audit IN THE SAME FILE**, and a proven theorem 4000 lines above it already contains
the one-line instantiation `compactSpace_of_isAdic_of_pi D.isAdic D.π D.π_surjective`.

An agent then proved a `HardlyRamifiedDeformation.compactSpace` wrapper against that audit and
verified it green before the original was found. It was a **duplicate of a one-liner, consumed by
nothing, hence free-floating**, and it had to be deleted rather than committed. Note both checks
that normally catch this were silent: it is not a duplicate NAME, so CLAUDE.md's class-7
duplicate-declaration scan does not see it, and it compiles perfectly.

Two rules, and the second is the one that generalises past this leaf.

- **Grep for the CONCLUSION, not for the file the machinery ought to live in.** Here that is
  `CompactSpace` applied to a deformation ring, across the whole tree. Grepping the plausible file
  and reporting what it contains is evidence about that file only.
- **Include the file you are editing.** These modules are 15–80k lines; "not in this module" is
  not something an author knows by having read it, and the audit that made this mistake was
  *written into* the file that refuted it. Search your own file first — it is the cheapest grep you
  will run and the one most likely to hit, because a leaf's machinery tends to have been built for
  its neighbours already.

Corollary for BUILD ORDERS in leaf docstrings: they are hypotheses, not facts, and a stale one
costs a whole dispatch. This one listed four bricks; the first did not exist as work at all. Price
each brick against the tree before dispatching an owner at it, and when a brick evaporates, say so
in the docstring **in place** — the deleted-wrapper story is why the audit was rewritten rather
than silently corrected.

