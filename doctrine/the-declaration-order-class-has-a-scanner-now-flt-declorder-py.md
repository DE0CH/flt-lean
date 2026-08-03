## THE DECLARATION-ORDER CLASS HAS A SCANNER NOW — `flt-declorder.py`, and it is 21 s for the tree

(2026-08-01, `flt-lean-144`.)  The two sections below describe the breakage
`tools/merge/semmerge.py` produces by not reordering, and both prescribe finding it by
reading errors out of a build.  That is one twenty-minute elaboration per cluster, and
the clusters are SERIALISED behind each other because a file stops at its first failure.
They are all findable statically, in one pass, before any build:

    ./flt-declorder.py Fermat --sweep --rev $(cat ~/.flt-release-lake/sha)

It reports every declaration that USES a name declared LATER in the same file — which is
exactly Lean's own resolution rule, so the class cannot hide from it — clustered, with
each cluster's span ready to hand to `flt-hoistcheck.py`.

**Calibrated in both directions, because a scan that reports nothing is
indistinguishable from a scan that is broken:**

* RECALL — on `X0.lean` at `9a6f34ee^`, the last tree carrying the release-29 breakage:
  **12 pairs in 8 clusters**, which is every cluster release 29 found by hand, plus the
  two that release's handover listed as STILL OPEN, plus one nobody had listed.
* PRECISION — on the green tree at `280981f1` (402 files): **0** with `--rev`.

**Two false-positive sources cost most of the build, and both are worth knowing because
any future scanner over Lean source will hit them:**

* **an `@[...]` attribute attaches to the declaration BELOW it and may span several
  lines, with a nested docstring inside** (`@[to_additive foo /-- … -/]`).  A body span
  that ends at the next `theorem` line therefore swallows the successor's attribute list
  and reads the successor's OWN name as a forward reference.  Bracket depth has to be
  carried across lines; a line-shaped test is not enough;
* **a dotted token is either a QUALIFIED name or DOT NOTATION, and only the second refers
  to this file's short name.**  `Rat.HeightOneSpectrum.adicCompletion.padicEquiv_bijOn`
  matched a local `padicEquiv_bijOn` on its last component and was pure noise.  The two
  are told apart by the CASE OF THE HEAD — namespaces are capitalised here, term
  variables are not.

**The residue is one class the scanner cannot decide and should not try to: a short name
that also exists in the import closure** (`mk_embedding`, `map_surjective`) resolves to
mathlib's and is not a forward reference at all.  Those are STABLE — they are in the
green tree too — so `--rev` differencing removes them exactly.  That is the same
discipline `xdup.py` and `scopecheck.py` already need, and the same warning applies:
**a bare run's output is a work list, not an error list.**

**And the meta-lesson, which is what this task actually was.**  The task named five
relocations to perform and two more as still open.  All seven were already landed on
`main`; the worktree was **1518 commits stale** and the dispatch fast-forward had simply
not happened, so `grep` found none of the named declarations and every one of them read
as a phantom.  `git rev-list --count HEAD..main` is the whole check and it is the first
command of any task.  **When a repair task turns out to be already done, the durable
deliverable is the CHECK that would have found the breakage — not the repairs.**  A
repair is worth one release; a calibrated scanner is worth every release after it, and
CLAUDE.md's own standing rule says so: a check worth running every release should be a
script with a name, not a paragraph.

