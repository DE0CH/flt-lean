---
name: flt-progress-md-is-generated
description: "PROGRESS.md's tree is GENERATED — edit progress-entries.json and run progress-tree.py; never hand-edit the tree; proven leaves auto-hide"
metadata: 
  node_type: memory
  type: feedback
  originSessionId: 407dda52-29da-420e-82fd-64073bb43c54
---

In the FLT project (`fermat/`), the `## Tree` section of `PROGRESS.md` is
GENERATED: edit `fermat/progress-entries.json` (flat list of tracked Lean
declarations with name/fullname/module/text/wip) and run
`python3 progress-tree.py`, which compiles a scratch file, computes the
dependency tree over the listed names, and computes marks with the compiler:
❌ own source has `sorry`; ✅ source complete but cone still has a sorry;
✅✅ whole cone axiom-clean — and ✅✅ nodes are HIDDEN from the tree display
entirely (they stay in the entries file).

**Why:** Deyao corrected (2026-07-18) hand-added ✅·-marked childless entries
for fully-proven leaves: "a leaf that is proven is by definition a double tick
and should not appear in progress.md". Hand-editing the generated section also
gets silently overwritten on the next regeneration.

**How to apply:** each loop iteration, put new sorried/derived declarations
(with distilled descriptions) into `progress-entries.json`, delete entries for
removed declarations, and regenerate; never mark or describe nodes by editing
the tree text directly. This connects to [[flt-continuous-loop-directives]].
