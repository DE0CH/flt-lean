## A ONE-LINE `def` IS ONE MERGE REGION — prose about a table merges, the table does not

(2026-07-31, `X0.lean`.) `x0HeckeCharpolyTable` is a `def` whose body is a single
bracketed list. Two branches each added a row to it and each wrote a long dated note
about that row into the surrounding docstring. **Both notes merged. Neither row did.**
Docstring paragraphs land in distinct regions of the file and merge cleanly side by
side; a bracketed list is ONE region, so concurrent editors serialise onto whichever
side the merge picks, and the losers vanish with no conflict marker.

What makes it worse than an ordinary dropped payload is where it surfaces. The table's
consumers were merged too, so on `merger`:

* `trace_heckeOpSq_x0OneSixtyNine` read as **fully proven** — a finished tactic proof,
  no `sorry` token, a docstring ending "PROVEN 2026-07-30 from the `169` row";
* `x0Genus_eq_of_mem_x0HeckeCharpolyTable` carried a `set_option maxRecDepth` bump
  whose own comment said it existed *for the `169` row alone*;
* and the row was not in the `def`, 31 000 lines above.

So the failure is a HARD ERROR at `(…) ∈ x0HeckeCharpolyTable := by decide`, reported
against a declaration that is not at fault, in a module that no frontier scan flags
(no `sorry`, no missing declaration, nothing unreachable). Third invisibility class,
reached by a new road.

**The detector is redundancy that already exists.** This file prints every banked row
in a prose table beside the `def`, precisely so rows can be eye-checked — and the prose
described both missing rows in full. So: **when a table-driven proof fails at a `decide`
on membership, suspect the table's `def` before the proof, and diff the `def` against
its own docstring.** Corollary for authors: a table whose prose duplicates its data is
not redundant, it is instrumented; keep writing them that way.

Two further habits this argues for:
* **Re-derive, do not copy back.** The dropped rows were recomputed from scratch in
  PARI/GP rather than lifted out of the prose, with an untouched row reproduced in the
  same session as a positive control. Prose that survived a merge its data did not is
  exactly the prose you cannot use as a source.
* **Count claims in docstrings rot silently.** This one said "the seventeen banked
  Hecke rows" while the `def` held twenty, and had said so across several merges.

