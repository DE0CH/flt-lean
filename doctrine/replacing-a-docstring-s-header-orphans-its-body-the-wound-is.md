## REPLACING A DOCSTRING'S HEADER ORPHANS ITS BODY — the wound is self-inflicted and silent
(Same task.) Editing a leaf into a theorem usually means rewriting its docstring. The
natural `Edit` replaces the opening paragraph — the part that says "sorry leaf, opened
…" — with a new opening plus, if you are also inserting a new leaf above, a whole new
declaration. **The old docstring's REMAINING BODY then sits below your closing `-/`, in
code position, ending in a `-/` that has become stray.** Sixty-two lines of prose, a stray
terminator, and a parse error whose location says nothing about the cause — i.e. exactly
the merge-damage shape `tools/merge/parsecheck.py` exists to find, manufactured by hand.
The tell is immediate if you look: after such an edit, the text between your new `-/` and
the `theorem` line should be EMPTY. Check it, or run `parsecheck.py` on the one file — it
is seconds and it named this instantly (`delimiters OK` once repaired).
**Prefer replacing the WHOLE docstring** (opener through its `-/`) in one `Edit` when you
are rewriting a leaf's header, rather than its first paragraph. If you must do it in
pieces, delete the orphan in the same turn and assert the seam:
    assert L[a-1] == '' and L[b-1].rstrip().endswith('-/') and L[b].startswith('theorem ')
