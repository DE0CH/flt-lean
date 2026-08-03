## AN `Edit` THAT REPORTS TWO MATCHES HAS FOUND A DUPLICATE CUT

(Same release.)  `exists_addSurjectiveAbelianImage_of_isAdditiveOn` and
`…_of_isAdditiveOn_aux`, 1400 lines apart in `X0.lean`, are the SAME statement
with the SAME 90-line proof, name for name.  I did not find that by scanning for
it — I tried to repair one of them and the harness reported *"Found 2 matches of
the string to replace"*.

**Why no scan had it.**  `dupstmt.py`'s default scope is SORRIED declarations,
and these are proven; `xdup.py` is about cross-FILE name collisions and these
share no name; every frontier instrument was correct and silent.  A duplicate
whose two copies are both PROVEN costs nothing until one of them breaks — and
then it costs twice, because the same repair is owed in two places, which is
exactly how this pair surfaced (both carried the same broken call to a deleted
lemma).

So: **when an exact-string Edit matches more than once in a 100k-line file, stop
and diff the two neighbourhoods before disambiguating the edit.**  And when both
copies have live consumers, neither can simply be deleted: make the LATER one a
one-line delegation to the earlier.  That keeps both call sites, removes the
duplicated proof, and leaves one place to repair next time.

Corollary for `dupstmt.py`: run it with `--all`, not only over the frontier, on
any file that a merge has touched more than once.

