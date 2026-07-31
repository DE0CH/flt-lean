---
name: flt-both-docstrings-name-the-loser
description: "When two cuts of one parent both merge, the orphaned loser AND the parent both claim in prose that the loser won — only the parent's `by` block is right."
metadata: 
  node_type: memory
  type: project
  originSessionId: 5cdefb04-098e-4399-89fd-5c845d36ec0e
  modified: 2026-07-31T13:13:48.899Z
---

Two agents cut the same leaf on the same day along different seams; release 29
merged both cleanly (each new declaration landed where the other never touched).
The parent kept ONE proof, so one cut went live and the other became a `sorry`
no proof term reaches. I was dispatched at the orphan.

The trap: **both** the orphan's docstring ("the consumer is PROVEN over this and
nothing else") and the **parent's** docstring ("PROVEN over `…pointwise…`
immediately above") named the loser, while the parent's `by` block called the
winner, 19 700 lines away. My task prompt quoted the orphan's docstring
faithfully.

Checks, cheapest first:
- `grep -n '<target>' <file>` — own declaration + docstrings only ⇒ orphaned.
- Read the parent's `by` block, never its docstring.
- "immediately above/below" is an ORDER assertion; check the line numbers. A
  merge falsifies it silently and it is the cheapest tell that two cuts collided.

Resolution: if the winner is strictly stronger and sits ABOVE, close the orphan
over it (~15 lines, frontier 2 → 1). Do NOT hoist-and-restrengthen in a contended
file for a presentational gain; record the alternative in `to_merger` instead.
Report it as merge repair with the count delta, not as mathematics.

See CLAUDE.md, "TWO CUTS OF ONE PARENT, MERGED CLEANLY". Related:
[[flt-delete-times-refactor-orphans-a-leaf]], [[flt-see-the-merge-before-the-merger]].
