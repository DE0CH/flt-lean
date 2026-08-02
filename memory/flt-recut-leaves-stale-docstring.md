---
name: flt-recut-leaves-stale-docstring
description: A recut copies its docstring onto the residue and leaves the original on the now-proven half, where the (sorry leaf) header draws phantom dispatches; sweep with tools/merge/stalelabel.py
metadata:
  type: project
---

When a leaf is RECUT, the geometric discussion is copied onto the residue leaf and the
ORIGINAL copy stays on the now-PROVEN half — still headed `(sorry leaf, <date>)`. Queue
entries are harvested from docstrings, so that header dispatches an agent at a
declaration with a complete `by` proof. `flt-lean-281` was exactly that; a sweep then
found **76 more** across the modules one X0 build reaches (65 in X0 alone).

Invisible to every instrument: no `sorry` token, no error, no duplicate name, green
build. Only the prose is wrong, and prose is what the queue is built from.

**Why:** the closing agent appends `SUPERSEDED / PROVEN` at the END of the docstring;
every harvester reads the BEGINNING. `IsRelPicZeroOf.eq_of_aj_eq` opens `(sorry node)`
and self-corrects 38 lines later.

**How to apply:** run `python3 tools/merge/stalelabel.py /tmp/build.log` — it takes the
sorried set from the build's `declaration uses 'sorry'` warning LINE NUMBERS (never a
source grep), attributes each to its enclosing declaration over comment-masked source,
and flags proven declarations whose FIRST THREE docstring lines still claim a leaf. It
rejects hits where a declaration or another comment terminator lies between the `/--`
and the declaration, and heads that also say `PROVEN`/`stale`. Files absent from the log
are SKIPPED, not treated as clean — an unbuilt module has no warnings.

Fix the HEADER at the top (two lines), not the body. If the body is a stale DUPLICATE of
the residue's docstring, delete it and point at the twin — after diffing to confirm the
twin carries it. The frontier does not move; say so, or the delta reads as nothing.

See [[flt-frozen-main-rots-the-queue]], [[flt-docstring-count-claims-are-checkable]].
