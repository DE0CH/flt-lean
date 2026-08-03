## A DELETION-ONLY BRANCH IS INVISIBLE TO `semmerge`, AND A GREEN BUILD PROVES NOTHING

(2026-07-31, `flt-lean-347`.) The corollary of the rule above, in its strongest form.
`semmerge.py` iterates over THEIRS' declarations and splices them into OURS; there is no
code path in it that removes a declaration from OURS. So a branch whose ENTIRE content is a
deletion merges to a **no-op** — and unlike a dropped proof, nothing downstream notices,
because the tree that keeps the deleted code still compiles. Deleting superseded code is
one of the few tasks where the merge silently reverting you leaves no trace at all.

Two things follow, and the first is for whoever writes the branch:

* **Say `to_merger` that the branch is a DELETION and must go in with plain `git merge`.**
  Name the files and the declaration blocks. If `semmerge` is used on those files the work
  evaporates and the report will say the merge was clean.
* **A superseded block costs only TIME, so nothing will ever flag it.** The one removed here
  — a hand-rolled `namespace F1` … `F5` Frobenius chain in `MazurNonCMFrobenius.lean` plus a
  whole sibling module `MazurNonCMFrobeniusB.lean`, 4 601 lines — had had no consumer since
  the generated `ElevenA.lean`/`ElevenB.lean` replaced it, and it built green every time.
  Measured on `cyclops`: the certificate cone went **944 s → 429 s**. Every frontier
  instrument in this file is blind to it: no `sorry`, no error, not unreachable, not
  free-floating in the census sense (it is not in the root cone either way).

And a third trap found in the same task: **the generator that wrote the superseded block is
still on disk, still documented as authoritative, and its `--out` still points at the module
you just rewrote.** `flt-frobenius-cert.py`'s docstring claimed "regenerating the committed
`MazurNonCMFrobenius.lean` reproduces it byte for byte", which stopped being true the moment
`gen_modules.py` took over. When you delete generated output, mark its generator SUPERSEDED
in the same commit and name the replacement, or the next agent regenerates the corpse over
the live file.

