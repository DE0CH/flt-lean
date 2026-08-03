## Verifying a BLOCK MOVE inside a file: sort both versions and diff

Relocating a declaration to satisfy Lean's define-before-use order is a common repair, and a
hand-retyped 100-line block can be silently corrupted in a docstring where nothing will ever
catch it. The check costs two commands and is exact:

    git show HEAD:<file> | sort > /tmp/old.txt
    sort <file>          > /tmp/new.txt
    diff -q /tmp/old.txt /tmp/new.txt      # identical multiset => the move was byte-exact

Any output means content changed as well as moved, which for a *pure* relocation is a defect.
Do the move programmatically (slice the line list, reinsert) rather than by retyping; that is
the case the "prefer Write/Edit" rule exempts as capability rather than convenience, and this
diff is what makes it auditable. Watch the blank lines at both the source and destination
seams — the multiset check catches a doubled blank line too.

