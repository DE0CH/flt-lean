## A DUPLICATE CUT ACROSS A NAMESPACE BOUNDARY IS INVISIBLE TO EVERY DUPLICATE SCAN — AND THE SORRY COPY IS THE ONE THAT WINS
(2026-08-02, `flt-lean-90`.)  The duplicate-cut sections above are about two
statements of one theorem under DIFFERENT NAMES.  There is a sharper form that
defeats `xdup.py`, `dupstmt.py` and `check-dup` at once: **the same name, in two
namespaces, where one module `public import`s the other.**
`Fermat.exists_nonconstant_toAbelianScheme_of_baseChange_relPoint` (`X1.lean`,
`sorry`) and
`Fermat.WeilRestriction.exists_nonconstant_toAbelianScheme_of_baseChange_relPoint`
(`WeilRestriction.lean`, PROVEN over two named atoms) are CHARACTER-IDENTICAL
statements, and `X1.lean` imports `WeilRestriction.lean`.  Why nothing fires:
* it is not a `has already been declared` error, because the qualified names
  differ — so the build is green and the cross-file duplicate scan is silent;
* `dupstmt.py` compares SORRIED declarations, and one of the two is proven;
* the parent module's import comment says the theorem is *"Stated and PROVEN
  there"*, so a reader checking the docstrings concludes the wiring was done.
**And the resolution goes the wrong way by default.**  Inside `namespace Fermat`
an unqualified use resolves to `Fermat.foo` before anything in a sub-namespace
that is not `open`ed — so the live consumer took the LOCAL `sorry`, and the
proven copy plus BOTH of its atoms had zero consumers anywhere in the tree.  A
worker dispatched at either atom is working on dead code.
**The check is two commands and it belongs in the consumer-grep every prover
already runs:**
    grep -rn '<yourTargetsConsumer>' --include=*.lean Fermat/    # note EVERY file
    # then, for each hit, compute the enclosing namespace and ask whether the
    # use site would resolve to THAT declaration or to a same-named one nearer
Computing the namespace needs a comment-masked scan (this tree's docstrings are
full of the words `namespace`, `section` and `end`); a bare `grep '^namespace'`
gave the wrong stack here by three levels.
**The repair is a one-line delegation, not a deletion**, when the two statements
are identical: the `sorry` copy becomes `:= <the qualified proven name> <args>`.
That keeps every call site, is -1 on the frontier, puts the dead atoms on the
live path, and costs the merge worker nothing.  Deleting the duplicate is the
right END state and belongs in `to_merger`, not in a branch that also has
mathematics in it.
**Generalises to the shape rather than the instance: whenever a module docstring
or an import comment says a theorem was RELOCATED and is "PROVEN there", grep for
the old name in the old file.**  A relocation is two edits — add there, delegate
here — and the second one is the one that gets forgotten, because the first one
is what the author was interested in.
