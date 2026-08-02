---
name: flt-docstring-count-claims-are-checkable
description: "A module docstring asserting \"X is the file's only remaining sorry\" is machine-checkable; a wrong count usually means a duplicate cut a merge left behind."
metadata: 
  node_type: memory
  type: project
  originSessionId: 959b60e8-5444-4622-8b9f-e732617e5e6d
  modified: 2026-08-01T12:37:48.255Z
---

Module docstrings in flt-lean routinely assert a COUNT — "X is now the file's only
remaining `sorry`", "the seventeen banked rows". A count is the one kind of prose the
compiler can refute, and checking it is free:

    grep -c "declaration uses \`sorry\`" <build log>    # vs the docstring's claim

**Why:** an off-by-one count in a file that has been merged more than once is a
DUPLICATE CUT until proven otherwise. The author's accounting described the tree they
cut; a merge then added a second copy of one leaf that nobody counted.

Confirmed 2026-08-01 in `Mathlib/AlgebraicGeometry/CurveAffineComplement.lean`: the
docstring claimed one `sorry`, the build reported two, and the extra one was a
character-for-character duplicate of a PROVEN theorem 106 lines above it, with zero
consumers.

**How to apply:**
- Run the count check on any file whose docstring states one, before doing anything else.
- The two names may share every WORD and no substring
  (`existence_valuativeCriterion_…` vs `valuativeCriterionExistence_of_…`), so name-prefix
  greps miss them — use `tools/merge/dupstmt.py`, or compare the word SETS.
- DELETE the unconsumed copy; do not prove it from the twin, which would leave a proven
  theorem nothing consumes (free-floating, forbidden here).
- Receipt = differential build: `cp` aside, `git checkout HEAD -- <path>`, build, `cp`
  back, `git add <path>` (the checkout stages the old version — without the `git add`,
  `git status` reads `MM`).

Related: [[flt-consumerless-leaf-is-dead-or-duplicate]],
[[flt-both-rival-cuts-landed]], [[flt-red-upstream-hides-downstream-damage]].
