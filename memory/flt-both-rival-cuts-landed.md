---
name: flt-both-rival-cuts-landed
description: "When two rival cuts of one node both merge, the loser's leaves stay live and the winner's proven assembly goes free-floating — detect via a proven theorem with zero consumers"
metadata: 
  node_type: memory
  type: project
  originSessionId: 125ad7f3-192d-442f-a4e4-262382177ee3
  modified: 2026-08-01T11:19:35.250Z
---

Two branches cut one node into (2 leaves + assembly) each. Their regions were far
enough apart not to conflict, so the merge kept BOTH and resolved the single
shared line — the parent's proof body — to the older side. Result: four open
leaves where two suffice, and the winning cut's PROVEN assembly left with zero
consumers anywhere in the tree.

**Why:** every instrument reports this as healthy — green build, four honest
`declaration uses 'sorry'` warnings, ownership checks correctly saying all four
are unowned and open. Nothing keyed on names can pair the two cuts.

**How to apply:** run two detectors. (1) the docstring/body mismatch on the
parent ([[flt-parent-docstring-vs-body-duplicate-cut]] shape); (2) cheaper and
keyed on the winner — a PROVEN theorem whose only comment-stripped occurrence is
its own declaration is free-floating, and that is the receipt that its cut lost a
merge. To choose between cuts of equal leaf count, the standing tie-breakers do
not separate them and "already consumed" points at the LOSER; separate them by
what each leaf asks of its OWNER, and by whether the junk witness dies on the
leaf or only by appeal to how the object was constructed. Report the frontier
drop as merge repair, not as mathematics. See [[flt-consumerless-leaf-is-dead-or-duplicate]].

Instance: `RelativePicard.lean`, `exists_relPicZeroGroupScheme` (07-30 cut) vs
`exists_relPicIdentityComponent` (07-31 cut), resolved 2026-08-01 by keeping the
07-31 cut, writing the ~25-line group transport, and deleting the 07-30 block.
