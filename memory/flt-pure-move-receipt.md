---
name: flt-pure-move-receipt
description: Prove a hoist/relocation changed nothing by diffing the SORTED line multiset — `sort` old and new and diff; a one-command receipt the merge worker can re-run
metadata:
  type: feedback
---

A relocation commit ("hoist X above Y") is reviewed by reading a 230-line
`git diff` that is 50% `-` and 50% `+` and looks like a rewrite. There is a
one-command receipt that it is a **pure move** instead:

    git show HEAD:<path> | sort > /tmp/old.sorted
    sort <path>          > /tmp/new.sorted
    diff /tmp/old.sorted /tmp/new.sorted     # empty  =>  identical line multiset

Empty output plus an unchanged line count means every line still exists exactly
once and only the ORDER changed — so no content was silently edited inside the
moved block, which is the thing a reviewer cannot otherwise check without
reading all 230 lines. Run it BEFORE committing and quote the result in the
commit message.

**Why:** a hoist is the highest-conflict edit possible in a file with many
concurrent editors (X0.lean routinely has 4+), and [[flt-see-the-merge-before-the-merger]]
plus CLAUDE.md's SEVENTH invisibility class both say a merge can split an edit
across the conflict boundary. If the merger knows the commit is a pure move, it
can resolve a conflict by RE-APPLYING the move to the merged text rather than
merging the two versions textually — which is the only resolution that cannot
half-land.

**How to apply:** split the relocation into its OWN commit, separate from the
proof that consumes it, and state the old and new line ranges plus the parent
sha in the message. Then check what the move breaks that the compiler will not:
directional cross-references (`… above`, `… below`) in the moved docstrings and
in docstrings that cite the moved declarations. Grep them by name and audit each
direction word; in the X0 hoist of 2026-07-31 exactly two of about a dozen went
stale, and the compiler is silent about all of them.

Also audit the ORDER of the moved blocks against their own prose: placing
`relPicEquiv_sectionIdeal_of_aj_eq` first kept its "the shared first half of both
degree-1 Riemann–Roch leaves below" true, where the other order would have
falsified it for free.
