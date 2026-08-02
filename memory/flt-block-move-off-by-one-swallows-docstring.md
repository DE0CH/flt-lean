---
name: flt-block-move-off-by-one-swallows-docstring
description: "A relocation whose block ends one line late eats the next declaration's `/--`, and the line-multiset receipt, parsecheck and commentscan all still pass"
metadata: 
  node_type: memory
  type: feedback
  originSessionId: aeae1001-6478-4e83-8e67-a1929727137f
  modified: 2026-08-02T14:43:00.274Z
---

A pure block move in a Lean file is verified by "the sorted multiset of lines is
unchanged". That receipt is exact for *did any line change* and blind to *did the
block end where the declaration ends*. One line too many at the end takes the
`/--` OPENER of the next declaration's docstring with it; the orphaned opener then
runs away to the next terminator at the DESTINATION, the orphaned body is absorbed
by the docstring above it at the SOURCE, comment depth still returns to zero, and
the file still parses — so `tools/merge/blockmove.py`, `sort`+`diff`,
`tools/merge/parsecheck.py` ("delimiters OK") and `tools/merge/commentscan.py`
(silent) ALL agree it is fine while a whole declaration has become a comment.

**Why:** Do not conclude from a green receipt that a relocation is clean — the
receipts cover content, not boundaries, and the resulting damage is the
runaway-doc-comment defect this project already knows from merges, arrived at
from a new direction.

**How to apply:** Before moving, `sed` the FIRST and LAST line of every block and
the two lines straddling the destination, and require the last line to be the end
of the declaration body (or the blank after it), never "the line before the next
`/--`". After moving, run
`awk 'prev ~ /^\/--/ && /^\/--/ {print NR} {prev=$0}' F.lean` — a doc-comment
opener directly after another opener is the tell, and it is one command.

See [[flt-pure-move-receipt]], [[flt-runaway-doc-comment]],
[[flt-comment-wounds-are-layered]].
